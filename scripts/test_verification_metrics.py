#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import property_utils
import verification_metrics


class VerificationMetricsTests(unittest.TestCase):
    def test_get_axiom_and_sorry_counts_ignore_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            (root / "Compiler").mkdir(parents=True, exist_ok=True)
            (root / "Verity").mkdir(parents=True, exist_ok=True)
            (root / "Compiler" / "Commented.lean").write_text(
                "\n".join(
                    [
                        "-- axiom fakeAxiom",
                        "/-",
                        "axiom fakeInBlock",
                        "sorry",
                        "-/",
                        'def quoted := "axiom fakeInString"',
                        'def quoted2 := "sorry"',
                        "axiom realAxiom : True",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            (root / "Verity" / "Proof.lean").write_text(
                "\n".join(
                    [
                        "-- sorry",
                        "theorem realSorry : True := by",
                        "  sorry",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            old_root = verification_metrics.ROOT
            try:
                verification_metrics.ROOT = root
                self.assertEqual(verification_metrics.get_axiom_count(), 1)
                self.assertEqual(verification_metrics.get_sorry_count(), 1)
            finally:
                verification_metrics.ROOT = old_root

    def test_get_manifest_counts_rejects_duplicate_json_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            manifest = Path(tmpdir) / "property_manifest.json"
            manifest.write_text(
                '{\n  "Counter": ["ok"],\n  "Counter": ["dup"]\n}\n',
                encoding="utf-8",
            )
            old_manifest = property_utils.MANIFEST
            try:
                property_utils.MANIFEST = manifest
                with self.assertRaises(SystemExit) as ctx:
                    verification_metrics.get_manifest_counts()
                self.assertIn("duplicate object key", str(ctx.exception))
            finally:
                property_utils.MANIFEST = old_manifest

    def test_load_metrics_from_artifact_rejects_boolean_numeric_field(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = verification_metrics.collect_metrics()
            payload["proofs"]["axioms"] = True
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "proofs\\.axioms must be an integer, got bool"):
                verification_metrics.load_metrics_from_artifact(artifact)

    def test_load_metrics_from_artifact_rejects_missing_schema_version(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = verification_metrics.collect_metrics()
            del payload["schema_version"]
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "root: missing required keys: schema_version"):
                verification_metrics.load_metrics_from_artifact(artifact)

    def test_load_metrics_from_artifact_rejects_unknown_top_level_key(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = verification_metrics.collect_metrics()
            payload["extra"] = 1
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "root: unknown keys: extra"):
                verification_metrics.load_metrics_from_artifact(artifact)

    def test_generate_verification_status_check_rejects_invalid_artifact_schema(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            artifact = Path(tmpdir) / "verification_status.json"
            payload = verification_metrics.collect_metrics()
            payload["proofs"]["axioms"] = True
            artifact.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT_DIR / "generate_verification_status.py"),
                    "--check",
                    "--output",
                    str(artifact),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("proofs.axioms must be an integer, got bool", result.stderr)


if __name__ == "__main__":
    unittest.main()
