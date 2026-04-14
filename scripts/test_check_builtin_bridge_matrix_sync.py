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


def _make_builtin_features(
    *,
    proved: list[str] | None = None,
    admitted: list[str] | None = None,
    concrete_only: list[str] | None = None,
    delegated: list[str] | None = None,
) -> list[dict]:
    """Build a builtin_features list from category lists."""
    proved = proved if proved is not None else check.PROVED_BUILTINS
    admitted = admitted if admitted is not None else check.ADMITTED_BUILTINS
    concrete_only = concrete_only if concrete_only is not None else check.CONCRETE_ONLY_BUILTINS
    delegated = delegated if delegated is not None else check.DELEGATED_BUILTINS
    features: list[dict] = []
    for name in proved:
        entry: dict = {
            "feature": name,
            "verity_path": "supported",
            "evmyullean_bridge": "supported",
            "agreement_proved": True,
        }
        if name in admitted:
            entry["sorry_dependent"] = True
        features.append(entry)
    for name in concrete_only:
        features.append({
            "feature": name,
            "verity_path": "supported",
            "evmyullean_bridge": "supported",
            "agreement_proved": False,
        })
    for name in delegated:
        features.append({
            "feature": name,
            "verity_path": "supported",
            "evmyullean_bridge": "delegated",
            "agreement_proved": False,
        })
    return features


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
        features = _make_builtin_features(
            delegated=["sload", "caller", "chainid", "calldataload", "mappingSlot"],
        )
        rc, output = self._run_check(
            builtin_features=features,
            doc_text="15/22 builtins have bridge agreement coverage.",
        )
        self.assertEqual(rc, 1)
        self.assertIn("builtin feature list is out of sync", output)

    def test_summary_drift_fails(self) -> None:
        features = _make_builtin_features()
        rc, output = self._run_check(
            builtin_features=features,
            doc_text=(
                "| `address` | ok | del | -- |\n"
                "| `timestamp` | ok | del | -- |\n"
                "15/30 builtins have universal bridge agreement proofs.\n"
                "15 are discharged by universal symbolic lemmas in X\n"
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

    def test_sorry_dependent_missing_flag_fails(self) -> None:
        """Admitted builtin without sorry_dependent=true should fail."""
        features = _make_builtin_features(admitted=[])  # No sorry flags
        rc, output = self._run_check(
            builtin_features=features,
            doc_text="anything",
        )
        self.assertEqual(rc, 1)
        # First admitted builtin should trigger the error
        self.assertIn("should have sorry_dependent=true", output)

    def test_sorry_dependent_on_non_admitted_fails(self) -> None:
        """Fully proved builtin with sorry_dependent=true should fail."""
        features = _make_builtin_features()
        # Add sorry_dependent to 'add' which is not admitted
        for f in features:
            if f["feature"] == "add":
                f["sorry_dependent"] = True
        rc, output = self._run_check(
            builtin_features=features,
            doc_text="anything",
        )
        self.assertEqual(rc, 1)
        self.assertIn("add should not have sorry_dependent=true", output)

    def test_sorry_qualifier_in_snippets(self) -> None:
        """Doc snippets should include sorry qualifier when admitted builtins exist."""
        features = _make_builtin_features()
        snippets = check.expected_doc_snippets(features)
        self.assertTrue(
            any("20 fully proven, 5 with sorry-dependent core equivalences" in s for s in snippets),
            f"Expected sorry qualifier in snippets: {snippets}",
        )

    def test_no_sorry_qualifier_when_no_admitted(self) -> None:
        """Doc snippets should not include qualifier when no sorry-dependent builtins."""
        features = _make_builtin_features(admitted=[])
        # Remove sorry_dependent flags that _make_builtin_features adds
        for f in features:
            f.pop("sorry_dependent", None)
        snippets = check.expected_doc_snippets(features)
        self.assertTrue(
            any("25/36 builtins have universal bridge agreement proofs" in s
                and "sorry" not in s for s in snippets),
            f"Expected unqualified snippet: {snippets}",
        )


if __name__ == "__main__":
    unittest.main()
