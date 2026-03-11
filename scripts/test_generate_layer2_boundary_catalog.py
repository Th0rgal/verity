from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import generate_layer2_boundary_catalog as gen


class GenerateLayer2BoundaryCatalogTests(unittest.TestCase):
    def test_rendered_catalog_has_expected_target_and_helper_gate(self) -> None:
        catalog = gen.build_catalog()
        self.assertEqual(
            catalog["theorem_target"]["intended_claim"],
            "proof_complete_macro_lowered_verity_contract_image",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"]["current_fail_closed_gate"],
            "SupportedBodyCallInterface.helperCompatibility",
        )
        self.assertEqual(
            catalog["theorem_target"]["issue_refs"]["helper_ir_semantics"],
            1638,
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"]["compiled_side_blocker_issue"],
            1638,
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["name"],
            "legacy_compatible_external_body_yul_subset",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["status"],
            "expr_layer_compatibility_proved_dispatch_local_goal_encoded",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["dispatch_local_surface"],
            "Compiler.Proofs.IRGeneration.IRInterpreter."
            "LegacyCompatibleRuntimeDispatch",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["dispatch_goal_surface"],
            "Compiler.Proofs.IRGeneration.IRInterpreter."
            "InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["goal_surface"],
            "Compiler.Proofs.IRGeneration.IRInterpreter."
            "InterpretIRWithInternalsZeroConservativeExtensionGoal",
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_compatibility_subset"
            ]["goal_decomposition_surface"],
            "Compiler.Proofs.IRGeneration.IRInterpreter."
            "InterpretIRWithInternalsZeroConservativeExtensionInterfaces",
        )
        self.assertEqual(
            catalog["current_out_of_scope_surfaces"][0]["status"],
            "blocked_at_body_ir_composition_seam",
        )
        self.assertEqual(
            [
                seam["name"]
                for seam in catalog["supported_spec_split"]["helper_boundary"]["blocking_seams"]
            ],
            [
                "legacy_stmt_fragment_witness",
                "ir_internal_call_semantics",
                "legacy_ir_target_compatibility_subset",
                "summary_soundness_not_yet_consumed",
            ],
        )
        self.assertEqual(
            catalog["supported_spec_split"]["helper_boundary"][
                "compiled_target_proof_surface"
            ]["status"],
            "helper_aware_ir_target_now_total_fuel_indexed_defs",
        )
        self.assertEqual(
            [step["rank"] for step in catalog["ranked_next_steps"]],
            ["P1", "P2", "P3", "P4", "P5", "P6", "P7"],
        )

    def test_check_mode_rejects_stale_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "layer2_boundary_catalog.json"
            output.write_text("{\"stale\": true}\n", encoding="utf-8")
            old_argv = sys.argv
            sys.argv = [
                "generate_layer2_boundary_catalog.py",
                "--check",
                "--output",
                str(output),
            ]
            try:
                with self.assertRaises(SystemExit) as exc:
                    gen.main()
            finally:
                sys.argv = old_argv
        self.assertIn("Stale Layer 2 boundary artifact", str(exc.exception))

    def test_writes_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "layer2_boundary_catalog.json"
            old_argv = sys.argv
            sys.argv = [
                "generate_layer2_boundary_catalog.py",
                "--output",
                str(output),
            ]
            try:
                stdout = io.StringIO()
                with redirect_stdout(stdout):
                    gen.main()
            finally:
                sys.argv = old_argv
            self.assertTrue(output.exists())
            self.assertIn("Wrote Layer 2 boundary artifact", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
