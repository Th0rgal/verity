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
    def test_runs_all_macro_checks_by_default(self) -> None:
        calls: list[str] = []
        old_property = check_macro_health.check_macro_property_test_generation.main
        old_invariant = check_macro_health.check_macro_translate_invariant_coverage.main
        old_roundtrip = check_macro_health.check_macro_roundtrip_fuzz_coverage.main
        check_macro_health.check_macro_property_test_generation.main = lambda argv=None: calls.append(
            f"property:{argv}"
        ) or 0
        check_macro_health.check_macro_translate_invariant_coverage.main = (
            lambda argv=None: calls.append(f"invariant:{argv}") or 0
        )
        check_macro_health.check_macro_roundtrip_fuzz_coverage.main = lambda argv=None: calls.append(
            f"roundtrip:{argv}"
        ) or 0
        try:
            self.assertEqual(check_macro_health.main([]), 0)
        finally:
            check_macro_health.check_macro_property_test_generation.main = old_property
            check_macro_health.check_macro_translate_invariant_coverage.main = old_invariant
            check_macro_health.check_macro_roundtrip_fuzz_coverage.main = old_roundtrip

        self.assertEqual(calls, ["property:['--check']", "invariant:[]", "roundtrip:[]"])

    def test_stops_on_first_failure(self) -> None:
        old_property = check_macro_health.check_macro_property_test_generation.main
        old_invariant = check_macro_health.check_macro_translate_invariant_coverage.main
        check_macro_health.check_macro_property_test_generation.main = lambda argv=None: 1
        check_macro_health.check_macro_translate_invariant_coverage.main = lambda argv=None: 0
        try:
            self.assertEqual(check_macro_health.main([]), 1)
        finally:
            check_macro_health.check_macro_property_test_generation.main = old_property
            check_macro_health.check_macro_translate_invariant_coverage.main = old_invariant


if __name__ == "__main__":
    unittest.main()
