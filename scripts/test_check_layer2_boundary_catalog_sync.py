from __future__ import annotations

import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_layer2_boundary_catalog_sync as check


class Layer2BoundaryCatalogSyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, good_docs: bool) -> None:
        artifact = root / "artifacts" / "layer2_boundary_catalog.json"
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_text(
            json.dumps(
                {
                    "theorem_target": {
                        "intended_claim": "proof_complete_macro_lowered_verity_contract_image",
                        "excludes_arbitrary_lean_compilation_models": True,
                    },
                    "supported_spec_split": {
                        "helper_boundary": {
                            "current_fail_closed_gate": "SupportedBodyCallInterface.helperCompatibility",
                            "blocking_seams": [
                                {"name": "legacy_stmt_fragment_witness"}
                            ],
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

        docs = {
            "GENERIC_PLAN": (
                "`artifacts/layer2_boundary_catalog.json`\n"
                "proof-complete `CompilationModel` subset\n"
                "macro-lowered image of `verity_contract`\n"
                "helper-free `SupportedStmtList` witness\n"
                "legacy-compatible external-body Yul subset\n"
                "total fuel-indexed helper-aware IR semantics\n"
            ),
            "ROADMAP": (
                "`artifacts/layer2_boundary_catalog.json`\n"
                "macro-lowered `verity_contract` image\n"
                "`calls.helperCompatibility` can disappear\n"
                "`execIRFunctionWithInternals` / `interpretIRWithInternals`\n"
                "conservative extension of `interpretIR`\n"
                "total fuel-indexed helper-aware IR semantics\n"
                "[#1638]\n"
            ),
            "VERIFICATION_STATUS": (
                "`artifacts/layer2_boundary_catalog.json`\n"
                "macro-lowered image of `verity_contract`\n"
                "`calls.helperCompatibility` gate\n"
                "helper-aware body theorem does not yet consume helper-summary soundness/rank evidence\n"
                "legacy-compatible external-body Yul subset\n"
                "total fuel-indexed helper-aware IR semantics\n"
                "[#1638]\n"
            ),
            "COMPILER_PROOFS_README": (
                "`artifacts/layer2_boundary_catalog.json`\n"
                "`SupportedSpec` split\n"
                "`calls.helpers`\n"
                "summary-soundness evidence\n"
                "legacy-compatible external-body Yul subset\n"
                "total fuel-indexed helper-aware IR semantics\n"
                "[#1638]\n"
            ),
        }
        if not good_docs:
            docs["ROADMAP"] = "stale roadmap\n"

        for label, rel in {
            "GENERIC_PLAN": Path("docs/GENERIC_LAYER2_PLAN.md"),
            "ROADMAP": Path("docs/ROADMAP.md"),
            "VERIFICATION_STATUS": Path("docs/VERIFICATION_STATUS.md"),
            "COMPILER_PROOFS_README": Path("Compiler/Proofs/README.md"),
        }.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(docs[label], encoding="utf-8")

    def _run_check(self, *, good_docs: bool) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, good_docs=good_docs)

            old_root = check.ROOT
            old_catalog = check.CATALOG
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.CATALOG = root / "artifacts" / "layer2_boundary_catalog.json"
            check.TARGET_FILES = {
                "GENERIC_PLAN": root / "docs" / "GENERIC_LAYER2_PLAN.md",
                "ROADMAP": root / "docs" / "ROADMAP.md",
                "VERIFICATION_STATUS": root / "docs" / "VERIFICATION_STATUS.md",
                "COMPILER_PROOFS_README": root / "Compiler" / "Proofs" / "README.md",
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.CATALOG = old_catalog
                check.TARGET_FILES = old_targets

    def test_matching_docs_pass(self) -> None:
        rc, output = self._run_check(good_docs=True)
        self.assertEqual(rc, 0, output)
        self.assertIn("layer2 boundary catalog sync passed", output)

    def test_missing_doc_phrase_fails(self) -> None:
        rc, output = self._run_check(good_docs=False)
        self.assertEqual(rc, 1)
        self.assertIn("docs/ROADMAP.md is out of sync", output)

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
