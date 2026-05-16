#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_macro_health


class MacroHealthTests(unittest.TestCase):
    def test_runs_property_check_by_default(self) -> None:
        calls: list[str] = []
        old_property = check_macro_health.check_macro_property_test_generation.main
        check_macro_health.check_macro_property_test_generation.main = lambda argv=None: calls.append(
            f"property:{argv}"
        ) or 0
        try:
            self.assertEqual(check_macro_health.main([]), 0)
        finally:
            check_macro_health.check_macro_property_test_generation.main = old_property

        self.assertEqual(calls, ["property:['--check']"])

    def test_stops_on_property_failure(self) -> None:
        old_property = check_macro_health.check_macro_property_test_generation.main
        check_macro_health.check_macro_property_test_generation.main = lambda argv=None: 1
        try:
            self.assertEqual(check_macro_health.main([]), 1)
        finally:
            check_macro_health.check_macro_property_test_generation.main = old_property


if __name__ == "__main__":
    unittest.main()
