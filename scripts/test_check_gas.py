#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_gas


class GasCheckTests(unittest.TestCase):
    def test_coverage_dispatches_to_model_coverage(self) -> None:
        calls: list[list[str]] = []
        old_main = check_gas.check_gas_model_coverage.main
        check_gas.check_gas_model_coverage.main = lambda argv=None: calls.append(argv or []) or 0
        try:
            self.assertEqual(check_gas.main(["coverage", "--dir", "a", "--dir", "b"]), 0)
        finally:
            check_gas.check_gas_model_coverage.main = old_main
        self.assertEqual(calls, [["--dir", "a", "--dir", "b"]])

    def test_report_dispatches_to_gas_report(self) -> None:
        calls: list[str] = []
        old_main = check_gas.check_gas_report.main
        check_gas.check_gas_report.main = lambda: calls.append("report") or 0
        try:
            self.assertEqual(check_gas.main(["report"]), 0)
        finally:
            check_gas.check_gas_report.main = old_main
        self.assertEqual(calls, ["report"])

    def test_calibration_dispatches_with_forwarded_args(self) -> None:
        calls: list[list[str]] = []
        old_main = check_gas.check_gas_calibration.main
        check_gas.check_gas_calibration.main = lambda argv=None: calls.append(argv or []) or 0
        try:
            self.assertEqual(
                check_gas.main(
                    [
                        "calibration",
                        "--static-report",
                        "gas.tsv",
                        "--allow-missing-contract",
                        "Demo",
                    ]
                ),
                0,
            )
        finally:
            check_gas.check_gas_calibration.main = old_main
        self.assertEqual(calls, [["--static-report", "gas.tsv", "--allow-missing-contract", "Demo"]])


if __name__ == "__main__":
    unittest.main()
