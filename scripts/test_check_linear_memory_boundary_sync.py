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

import check_linear_memory_boundary_sync as check


class LinearMemoryBoundarySyncTests(unittest.TestCase):
    def _write_fixture_tree(
        self,
        root: Path,
        *,
        expr_proof_status: str,
        expr_basic_status: str,
        expr_fuel_status: str,
        stmt_proof_status: str,
        stmt_basic_status: str,
        stmt_fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> None:
        matrix = {
            "expr_features": [
                {
                    "feature": feature,
                    "proof_status": expr_proof_status,
                    "SpecInterpreter_basic": expr_basic_status,
                    "SpecInterpreter_fuel": expr_fuel_status,
                }
                for feature in ("mload", "returndataOptionalBoolAt")
            ],
            "stmt_features": [
                {
                    "feature": feature,
                    "proof_status": stmt_proof_status,
                    "SpecInterpreter_basic": stmt_basic_status,
                    "SpecInterpreter_fuel": stmt_fuel_status,
                }
                for feature in ("mstore", "calldatacopy", "returndataCopy")
            ],
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
        expr_proof_status: str,
        expr_basic_status: str,
        expr_fuel_status: str,
        stmt_proof_status: str,
        stmt_basic_status: str,
        stmt_fuel_status: str,
        edsl_doc: str,
        compiler_doc: str,
        solidity_guide: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(
                root,
                expr_proof_status=expr_proof_status,
                expr_basic_status=expr_basic_status,
                expr_fuel_status=expr_fuel_status,
                stmt_proof_status=stmt_proof_status,
                stmt_basic_status=stmt_basic_status,
                stmt_fuel_status=stmt_fuel_status,
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

    def test_boundary_note_required_when_linear_memory_not_fully_modeled(self) -> None:
        note = textwrap.dedent(
            """
            First-class linear-memory forms (`Expr.mload`, `Stmt.mstore`, `Stmt.calldatacopy`, `Stmt.returndataCopy`, `Expr.returndataOptionalBoolAt`) also compile today, but they are still only partially modeled by the current proof interpreters.
            treat them as an explicit memory/ABI trust boundary, archive `--trust-report`, and use `--deny-linear-memory-mechanics` for proof-strict runs (see issue `#1411`).
            Memory-oriented intrinsics (`mload`, `mstore`, `calldatacopy`, `returndataCopy`, `returndataOptionalBoolAt`) compile, but the current proof interpreters still model them only partially.
            surface that boundary with `--trust-report` / `--deny-linear-memory-mechanics`; the remaining gap is tracked under issue `#1411`.
            Manual ABI or memory plumbing (`mload` / `mstore` / copy-based payload handling) compiles, but it is still outside the fully proved interpreter semantics today.
            use `--deny-linear-memory-mechanics` if the translated contract must stay inside the proved subset (see issue `#1411`).
            """
        )
        rc, output = self._run_check(
            expr_proof_status="partial",
            expr_basic_status="fallback_zero",
            expr_fuel_status="fallback_zero",
            stmt_proof_status="not_modeled",
            stmt_basic_status="unsupported",
            stmt_fuel_status="unsupported",
            edsl_doc=note,
            compiler_doc=note,
            solidity_guide=note,
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("boundary note required", output)

    def test_missing_boundary_note_fails_when_linear_memory_not_fully_modeled(self) -> None:
        rc, output = self._run_check(
            expr_proof_status="partial",
            expr_basic_status="fallback_zero",
            expr_fuel_status="fallback_zero",
            stmt_proof_status="not_modeled",
            stmt_basic_status="unsupported",
            stmt_fuel_status="unsupported",
            edsl_doc="memory forms exist\n",
            compiler_doc="compiler intrinsics exist\n",
            solidity_guide="manual abi note\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("edsl-api-reference.mdx is out of sync", output)

    def test_boundary_note_not_required_once_linear_memory_is_fully_modeled(self) -> None:
        rc, output = self._run_check(
            expr_proof_status="proved",
            expr_basic_status="supported",
            expr_fuel_status="supported",
            stmt_proof_status="proved",
            stmt_basic_status="supported",
            stmt_fuel_status="supported",
            edsl_doc="memory forms exist\n",
            compiler_doc="compiler intrinsics exist\n",
            solidity_guide="manual abi note\n",
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
