from __future__ import annotations

import io
import json
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_axiomatized_primitive_boundary_sync as check


class AxiomatizedPrimitiveBoundarySyncTests(unittest.TestCase):
    def _write_fixture_tree(
        self,
        root: Path,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> None:
        matrix = {
            "expr_features": [
                {
                    "feature": "keccak256",
                    "proof_status": proof_status,
                    "SpecInterpreter_basic": basic_status,
                    "SpecInterpreter_fuel": fuel_status,
                }
            ],
            "stmt_features": [],
        }
        feature_matrix = root / "artifacts" / "interpreter_feature_matrix.json"
        feature_matrix.parent.mkdir(parents=True, exist_ok=True)
        feature_matrix.write_text(json.dumps(matrix), encoding="utf-8")

        edsl_path = root / "docs-site" / "content" / "edsl-api-reference.mdx"
        edsl_path.parent.mkdir(parents=True, exist_ok=True)
        edsl_path.write_text(edsl_doc, encoding="utf-8")

        compiler_path = root / "docs-site" / "content" / "compiler.mdx"
        compiler_path.parent.mkdir(parents=True, exist_ok=True)
        compiler_path.write_text(compiler_doc, encoding="utf-8")

        guide_path = root / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx"
        guide_path.parent.mkdir(parents=True, exist_ok=True)
        guide_path.write_text(solidity_guide, encoding="utf-8")

    def _run_check(
        self,
        *,
        proof_status: str,
        basic_status: str,
        fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(
                root,
                proof_status=proof_status,
                basic_status=basic_status,
                fuel_status=fuel_status,
                edsl_doc=edsl_doc,
                compiler_doc=compiler_doc,
                solidity_guide=solidity_guide,
            )

            old_root = check.ROOT
            old_matrix = check.FEATURE_MATRIX
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.FEATURE_MATRIX = root / "artifacts" / "interpreter_feature_matrix.json"
            check.TARGET_FILES = {
                "EDSL_API": root / "docs-site" / "content" / "edsl-api-reference.mdx",
                "COMPILER_DOC": root / "docs-site" / "content" / "compiler.mdx",
                "SOLIDITY_GUIDE": root / "docs-site" / "content" / "guides" / "solidity-to-verity.mdx",
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.FEATURE_MATRIX = old_matrix
                check.TARGET_FILES = old_targets

    def test_boundary_note_required_when_axiomatized_primitive_not_fully_modeled(self) -> None:
        note = textwrap.dedent(
            """
            `Expr.keccak256` also remains an explicit proof boundary today: the compiler supports it directly, but the current proof stack still treats it as an axiomatized primitive instead of a fully modeled operation.
            archive `--trust-report` and use `--deny-axiomatized-primitives` for proof-strict runs (see issue `#1411`).
            The `keccak256` intrinsic also compiles, but it remains axiomatized in the current proof stack rather than fully modeled end to end.
            archive `--trust-report` and add `--deny-axiomatized-primitives` if the selected contracts must stay inside the proved subset (see issue `#1411`).
            Raw `keccak256` hashing also compiles through the typed intrinsic surface, but it still relies on an explicit axiom in the current proof stack.
            archive `--trust-report`, and use `--deny-axiomatized-primitives` when the translated contract must stay inside the proved subset (see issue `#1411`).
            """
        )
        rc, output = self._run_check(
            proof_status="not_modeled",
            basic_status="unsupported",
            fuel_status="unsupported",
            edsl_doc=note,
            compiler_doc=note,
            solidity_guide=note,
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("boundary note required", output)

    def test_missing_boundary_note_fails_when_axiomatized_primitive_not_fully_modeled(self) -> None:
        rc, output = self._run_check(
            proof_status="not_modeled",
            basic_status="unsupported",
            fuel_status="unsupported",
            edsl_doc="keccak doc\n",
            compiler_doc="compiler doc\n",
            solidity_guide="guide doc\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("edsl-api-reference.mdx is out of sync", output)

    def test_boundary_note_not_required_once_axiomatized_primitive_is_fully_modeled(self) -> None:
        rc, output = self._run_check(
            proof_status="proved",
            basic_status="supported",
            fuel_status="supported",
            edsl_doc="keccak doc\n",
            compiler_doc="compiler doc\n",
            solidity_guide="guide doc\n",
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("boundary note not required", output)

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
