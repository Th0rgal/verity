#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().parent / "check_lean_warning_regression.py"


class CheckLeanWarningRegressionScriptTests(unittest.TestCase):
    def test_accepts_valid_baseline(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text(
                "warning: Compiler/Main.lean:1:1: declaration uses 'sorry'\n",
                encoding="utf-8",
            )
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 1,
                        "by_file": {"Compiler/Main.lean": 1},
                        "by_message": {"declaration uses 'sorry'": 1},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("Lean warning baseline check passed", proc.stdout)

    def test_rejects_stale_baseline_when_warnings_drop(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 1,
                        "by_file": {"Compiler/Main.lean": 1},
                        "by_message": {"declaration uses 'sorry'": 1},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("Total Lean warnings drifted: observed 0, baseline 1", proc.stderr)

    def test_rejects_invalid_baseline_counter_shape(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 0,
                        "by_file": [],
                        "by_message": {},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("'by_file' must be an object", proc.stderr)

    def test_rejects_invariant_mismatch_in_baseline(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 2,
                        "by_file": {"Compiler/Main.lean": 1},
                        "by_message": {"m": 2},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("sum(by_file)=1 must equal total_warnings=2", proc.stderr)

    def test_rejects_missing_counter_fields(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps({"schema_version": 1, "total_warnings": 0}) + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("missing required keys: by_file, by_message", proc.stderr)

    def test_rejects_null_counter_fields(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 0,
                        "by_file": None,
                        "by_message": {},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("'by_file' must be an object", proc.stderr)

    def test_rejects_boolean_scalar_fields(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": True,
                        "total_warnings": False,
                        "by_file": {},
                        "by_message": {},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("expected schema_version=1", proc.stderr)

    def test_rejects_boolean_counter_values(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_text("", encoding="utf-8")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 1,
                        "by_file": {"Compiler/Main.lean": True},
                        "by_message": {"declaration uses 'sorry'": 1},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("must be an integer, got bool", proc.stderr)

    def test_rejects_invalid_utf8_in_log(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log_path = root / "lake-build.log"
            baseline_path = root / "lean_warning_baseline.json"
            log_path.write_bytes(b"warning:\xff Compiler/Main.lean:1:1: declaration uses 'sorry'\n")
            baseline_path.write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "total_warnings": 0,
                        "by_file": {},
                        "by_message": {},
                    }
                )
                + "\n",
                encoding="utf-8",
            )

            proc = subprocess.run(
                [sys.executable, str(SCRIPT), "--log", str(log_path), "--baseline", str(baseline_path)],
                text=True,
                capture_output=True,
                check=False,
            )

            self.assertNotEqual(proc.returncode, 0)
            self.assertIn("invalid UTF-8 in log input", proc.stderr)


if __name__ == "__main__":
    unittest.main()
