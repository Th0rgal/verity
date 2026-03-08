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

import check_builtin_bridge_matrix_sync as check


class BuiltinBridgeMatrixSyncTests(unittest.TestCase):
    def _write_fixture_tree(self, root: Path, *, builtin_features: list[dict], doc_text: str) -> None:
        feature_matrix = root / "artifacts" / "interpreter_feature_matrix.json"
        feature_matrix.parent.mkdir(parents=True, exist_ok=True)
        feature_matrix.write_text(json.dumps({"builtin_features": builtin_features}), encoding="utf-8")

        target_doc = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
        target_doc.parent.mkdir(parents=True, exist_ok=True)
        target_doc.write_text(doc_text, encoding="utf-8")

    def _run_check(self, *, builtin_features: list[dict], doc_text: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, builtin_features=builtin_features, doc_text=doc_text)

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

    def test_missing_delegated_builtin_fails_closed(self) -> None:
        builtin_features = [
            {
                "feature": feature,
                "verity_path": "supported",
                "evmyullean_bridge": "supported",
                "agreement_proved": True,
            }
            for feature in check.PURE_BUILTINS
        ] + [
            {
                "feature": feature,
                "verity_path": "supported",
                "evmyullean_bridge": "delegated",
                "agreement_proved": False,
            }
            for feature in ["sload", "caller", "chainid", "calldataload", "mappingSlot"]
        ]
        rc, output = self._run_check(
            builtin_features=builtin_features,
            doc_text="15/22 builtins have bridge agreement coverage between Verity and EVMYulLean evaluation paths.",
        )
        self.assertEqual(rc, 1)
        self.assertIn("builtin feature list is out of sync", output)

    def test_summary_drift_fails(self) -> None:
        builtin_features = [
            {
                "feature": feature,
                "verity_path": "supported",
                "evmyullean_bridge": "supported",
                "agreement_proved": True,
            }
            for feature in check.PURE_BUILTINS
        ] + [
            {
                "feature": feature,
                "verity_path": "supported",
                "evmyullean_bridge": "delegated",
                "agreement_proved": False,
            }
            for feature in check.DELEGATED_BUILTINS
        ]
        rc, output = self._run_check(
            builtin_features=builtin_features,
            doc_text=(
                "| `address` | ok | del | -- |\n"
                "| `timestamp` | ok | del | -- |\n"
                "15/20 builtins have bridge agreement coverage between Verity and EVMYulLean evaluation paths.\n"
                "15 are discharged by universal symbolic lemmas in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`, and none still require concrete-only regression coverage.\n"
                "The remaining 5 are state-dependent or Verity-specific helpers that remain on the Verity evaluation path.\n"
            ),
        )
        self.assertEqual(rc, 1)
        self.assertIn("docs/INTERPRETER_FEATURE_MATRIX.md is out of sync", output)

    def test_repository_files_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
