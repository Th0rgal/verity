#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_gas
import check_lean_warning_regression
import check_patch_gas_delta
import check_yul


@contextmanager
def _ambient_argv(*args: str):
    old = sys.argv
    sys.argv = ["prog", *args]
    try:
        yield
    finally:
        sys.argv = old


class CliArgvInjectionTests(unittest.TestCase):
    def test_check_gas_parse_args_ignores_ambient_sys_argv(self) -> None:
        with _ambient_argv("--unexpected-harness-flag"):
            parsed = check_gas.parse_args(["coverage", "--dir", "artifacts/yul"])
        self.assertEqual(parsed.command, "coverage")
        self.assertEqual(parsed.dirs, ["artifacts/yul"])

    def test_check_patch_gas_delta_parse_args_ignores_ambient_sys_argv(self) -> None:
        with _ambient_argv("--unexpected-harness-flag"):
            parsed = check_patch_gas_delta.parse_args(
                ["--baseline-report", "a.tsv", "--patched-report", "b.tsv"]
            )
        self.assertEqual(Path(parsed.baseline_report), Path("a.tsv"))
        self.assertEqual(Path(parsed.patched_report), Path("b.tsv"))

    def test_check_gas_calibration_parse_args_ignores_ambient_sys_argv(self) -> None:
        with _ambient_argv("--unexpected-harness-flag"):
            parsed = check_gas.parse_args(["calibration"])
        self.assertEqual(parsed.command, "calibration")
        self.assertEqual(parsed.match_path, check_gas.check_gas_calibration.DEFAULT_FOUNDRY_PATH_GLOB)

    def test_check_yul_parse_args_ignores_ambient_sys_argv(self) -> None:
        with _ambient_argv("--unexpected-harness-flag"):
            parsed = check_yul.parse_args(["--dir", "artifacts/yul"])
        self.assertEqual(parsed.dirs, ["artifacts/yul"])

    def test_check_lean_warning_main_accepts_injected_argv(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            log = root / "lake-build.log"
            baseline = root / "baseline.json"
            log.write_text("", encoding="utf-8")
            with _ambient_argv("--unexpected-harness-flag"):
                check_lean_warning_regression.main(
                    ["--log", str(log), "--write-baseline", str(baseline)]
                )
            self.assertTrue(baseline.exists())


if __name__ == "__main__":
    unittest.main()
