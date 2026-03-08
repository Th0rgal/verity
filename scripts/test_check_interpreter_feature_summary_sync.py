#!/usr/bin/env python3
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

import check_interpreter_feature_summary_sync as check


class InterpreterFeatureSummarySyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, matrix: dict, doc_text: str) -> None:
        feature_matrix = root / "artifacts" / "interpreter_feature_matrix.json"
        feature_matrix.parent.mkdir(parents=True, exist_ok=True)
        feature_matrix.write_text(json.dumps(matrix), encoding="utf-8")

        target_doc = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
        target_doc.parent.mkdir(parents=True, exist_ok=True)
        target_doc.write_text(doc_text, encoding="utf-8")

    def _run_check(self, *, matrix: dict, doc_text: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, matrix=matrix, doc_text=doc_text)

            old_root = check.ROOT
            old_feature_matrix = check.FEATURE_MATRIX
            old_target_doc = check.TARGET_DOC
            check.ROOT = root
            check.FEATURE_MATRIX = root / "artifacts" / "interpreter_feature_matrix.json"
            check.TARGET_DOC = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.FEATURE_MATRIX = old_feature_matrix
                check.TARGET_DOC = old_target_doc

    @staticmethod
    def _matrix_fixture() -> dict:
        return {
            "expr_features": [
                {"feature": "provedExpr", "proof_status": "proved"},
                {"feature": "externalCall_expr", "proof_status": "assumed"},
                {"feature": "chainid", "proof_status": "partial"},
                {"feature": "mload", "proof_status": "partial"},
                {"feature": "call", "proof_status": "not_modeled"},
                {"feature": "delegatecall", "proof_status": "not_modeled"},
            ],
            "stmt_features": [
                {"feature": "provedStmt", "proof_status": "proved"},
                {"feature": "mstore", "proof_status": "partial"},
                {"feature": "calldatacopy", "proof_status": "not_modeled"},
            ],
            "builtin_features": [
                {"feature": "add", "agreement_proved": True},
                {"feature": "caller", "agreement_proved": False},
            ],
        }

    def test_missing_summary_row_fails_closed(self) -> None:
        rc, output = self._run_check(
            matrix=self._matrix_fixture(),
            doc_text="| Expression features | 2 | 0 | 0 | 0 |\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("docs/INTERPRETER_FEATURE_MATRIX.md is out of sync", output)

    def test_invalid_builtin_agreement_value_fails(self) -> None:
        matrix = self._matrix_fixture()
        matrix["builtin_features"][0]["agreement_proved"] = "yes"
        rc, output = self._run_check(matrix=matrix, doc_text="")
        self.assertEqual(rc, 1)
        self.assertIn("non-boolean agreement_proved", output)

    def test_repository_doc_is_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
