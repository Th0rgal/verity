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
    proved_set = set(proved)
    admitted_set = set(admitted)
    concrete_only_set = set(concrete_only)
    delegated_set = set(delegated)
    features: list[dict] = []
    for name in check.EXPECTED_BUILTINS:
        if name in proved_set:
            entry: dict = {
                "feature": name,
                "verity_path": "supported",
                "evmyullean_bridge": "supported",
                "agreement_proved": True,
            }
            if name in admitted_set:
                entry["sorry_dependent"] = True
            features.append(entry)
        elif name in concrete_only_set:
            features.append({
                "feature": name,
                "verity_path": "supported",
                "evmyullean_bridge": "supported",
                "agreement_proved": False,
            })
        elif name in delegated_set:
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
        admitted = [
            entry["feature"]
            for entry in builtin_features
            if entry.get("sorry_dependent") is True
        ]
        adapter_report = root / "artifacts" / "evmyullean_adapter_report.json"
        adapter_report.write_text(json.dumps({"admitted_bridge_lemmas": admitted}), encoding="utf-8")

        target_doc = root / "docs" / "INTERPRETER_FEATURE_MATRIX.md"
        target_doc.parent.mkdir(parents=True, exist_ok=True)
        target_doc.write_text(doc_text, encoding="utf-8")

    def _run_check(self, *, builtin_features: list[dict], doc_text: str) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(root, builtin_features=builtin_features, doc_text=doc_text)

            old_root = check.ROOT
            old_feature_matrix = check.FEATURE_MATRIX
            old_adapter_report = check.ADAPTER_REPORT
            old_target_doc = check.TARGET_DOC
            check.ROOT = root
            check.FEATURE_MATRIX = root / "artifacts" / "interpreter_feature_matrix.json"
            check.ADAPTER_REPORT = root / "artifacts" / "evmyullean_adapter_report.json"
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
                check.ADAPTER_REPORT = old_adapter_report
                check.TARGET_DOC = old_target_doc

    def test_missing_delegated_builtin_fails_closed(self) -> None:
        features = [
            entry for entry in _make_builtin_features()
            if entry["feature"] != "mappingSlot"
        ]
        rc, output = self._run_check(
            builtin_features=features,
            doc_text="36/36 builtins have bridge agreement coverage.",
        )
        self.assertEqual(rc, 1)
        self.assertIn("builtin feature list is out of sync", output)

    def test_summary_drift_fails(self) -> None:
        features = _make_builtin_features()
        rc, output = self._run_check(
            builtin_features=features,
            doc_text=(
                "| `address` | ok | del | -- |\n"
                "| `timestamp` | ok | ok | yes |\n"
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
        matrix = {"builtin_features": features}
        with self.assertRaisesRegex(ValueError, "should have sorry_dependent=true"):
            check.validate_builtin_features(matrix, ["sar"])

    def test_sorry_dependent_on_non_admitted_fails(self) -> None:
        """Fully proved builtin with sorry_dependent=true should fail."""
        features = _make_builtin_features()
        # Add sorry_dependent to 'add' which is not admitted
        for f in features:
            if f["feature"] == "add":
                f["sorry_dependent"] = True
        matrix = {"builtin_features": features}
        with self.assertRaisesRegex(ValueError, "add should not have sorry_dependent=true"):
            check.validate_builtin_features(matrix)

    def test_sorry_dependent_on_concrete_only_fails(self) -> None:
        """Concrete-only builtin with sorry_dependent=true should fail."""
        # Use validate_builtin_features directly with a synthetic matrix
        # that has a concrete-only builtin, since CONCRETE_ONLY_BUILTINS
        # may be empty in the current codebase state.
        old_concrete = check.CONCRETE_ONLY_BUILTINS
        old_proved = check.PROVED_BUILTINS
        old_expected = check.EXPECTED_BUILTINS
        old_admitted = check.ADMITTED_BUILTINS
        try:
            # Move "add" from proved to concrete-only for this test
            check.CONCRETE_ONLY_BUILTINS = ["add"]
            check.PROVED_BUILTINS = [b for b in old_proved if b != "add"]
            check.ADMITTED_BUILTINS = [b for b in old_admitted if b in check.PROVED_BUILTINS]
            check.EXPECTED_BUILTINS = check.PROVED_BUILTINS + check.CONCRETE_ONLY_BUILTINS + check.DELEGATED_BUILTINS
            features = _make_builtin_features(
                proved=check.PROVED_BUILTINS,
                concrete_only=check.CONCRETE_ONLY_BUILTINS,
                admitted=check.ADMITTED_BUILTINS,
            )
            # Inject sorry_dependent on the concrete-only entry
            for f in features:
                if f["feature"] == "add":
                    f["sorry_dependent"] = True
            matrix = {"builtin_features": features}
            with self.assertRaises(ValueError, msg="concrete-only") as ctx:
                check.validate_builtin_features(matrix)
            self.assertIn("concrete-only and must not have sorry_dependent=true", str(ctx.exception))
        finally:
            check.CONCRETE_ONLY_BUILTINS = old_concrete
            check.PROVED_BUILTINS = old_proved
            check.EXPECTED_BUILTINS = old_expected
            check.ADMITTED_BUILTINS = old_admitted

    def test_sorry_dependent_on_delegated_fails(self) -> None:
        """Delegated builtin with sorry_dependent=true should fail."""
        old_delegated = check.DELEGATED_BUILTINS
        old_proved = check.PROVED_BUILTINS
        old_expected = check.EXPECTED_BUILTINS
        old_admitted = check.ADMITTED_BUILTINS
        try:
            check.DELEGATED_BUILTINS = ["mappingSlot"]
            check.PROVED_BUILTINS = [b for b in old_proved if b != "mappingSlot"]
            check.ADMITTED_BUILTINS = [b for b in old_admitted if b in check.PROVED_BUILTINS]
            check.EXPECTED_BUILTINS = check.PROVED_BUILTINS + check.CONCRETE_ONLY_BUILTINS + check.DELEGATED_BUILTINS
            features = _make_builtin_features(
                proved=check.PROVED_BUILTINS,
                admitted=check.ADMITTED_BUILTINS,
                delegated=check.DELEGATED_BUILTINS,
            )
            for f in features:
                if f["feature"] == "mappingSlot":
                    f["sorry_dependent"] = True
            matrix = {"builtin_features": features}
            with self.assertRaises(ValueError, msg="delegated") as ctx:
                check.validate_builtin_features(matrix)
            self.assertIn("delegated and must not have sorry_dependent=true", str(ctx.exception))
        finally:
            check.DELEGATED_BUILTINS = old_delegated
            check.PROVED_BUILTINS = old_proved
            check.EXPECTED_BUILTINS = old_expected
            check.ADMITTED_BUILTINS = old_admitted

    def test_adapter_report_admitted_set_drives_validation(self) -> None:
        """Repository check should use the adapter report, not the fallback constant."""
        features = _make_builtin_features()
        matrix = {"builtin_features": features}
        with self.assertRaisesRegex(ValueError, "smod should have sorry_dependent=true"):
            check.validate_builtin_features(matrix, ["smod"])

        validated = check.validate_builtin_features(matrix, check.ADMITTED_BUILTINS)
        self.assertEqual(validated, features)

    def test_load_admitted_builtins_rejects_unknown_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "report.json"
            path.write_text(json.dumps({"admitted_bridge_lemmas": ["exp", "fake"]}), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "outside PROVED_BUILTINS"):
                check.load_admitted_builtins(path)

    def test_sorry_qualifier_in_snippets(self) -> None:
        """Doc snippets should include sorry qualifier when admitted builtins exist."""
        features = _make_builtin_features(admitted=["sar"])
        snippets = check.expected_doc_snippets(features)
        self.assertTrue(
            any("35 fully proven, 1 with sorry-dependent core equivalence" in s for s in snippets),
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
            any("36/36 builtins have universal bridge agreement proofs" in s
                and "sorry" not in s for s in snippets),
            f"Expected unqualified snippet: {snippets}",
        )


if __name__ == "__main__":
    unittest.main()
