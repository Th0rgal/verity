#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_selectors
from check_selectors import extract_compile_selectors, extract_specs, load_specs_text


class CheckSelectorsExtractCompileSelectorsTests(unittest.TestCase):
    def test_extract_compile_selectors_allows_empty_list(self) -> None:
        text = (
            "theorem t : compile emptySpec [] = .ok emptyIR := by\n"
            "  trivial\n"
        )
        rows = extract_compile_selectors(text)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].def_name, "emptySpec")
        self.assertEqual(rows[0].selectors, [])

    def test_extract_compile_selectors_parses_non_empty_list(self) -> None:
        text = (
            "theorem t : compile counterSpec [0xd09de08a, 0x8ada066e] "
            "= .ok counterIR := by\n"
            "  trivial\n"
        )
        rows = extract_compile_selectors(text)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].def_name, "counterSpec")
        self.assertEqual(rows[0].selectors, [0xD09DE08A, 0x8ADA066E])


class CheckSelectorsExtractSpecsTests(unittest.TestCase):
    def test_extract_specs_supports_filtered_macro_alias_defs(self) -> None:
        rows = extract_specs(load_specs_text())
        counter = next(row for row in rows if row.def_name == "counterSpec")
        self.assertEqual(counter.contract_name, "Counter")
        self.assertEqual(
            counter.signatures,
            ["increment()", "decrement()", "getCount()"],
        )


class CheckSelectorsCliTests(unittest.TestCase):
    def test_check_fixtures_flag_dispatches_fixture_check(self) -> None:
        calls: list[str] = []
        old_fixture_main = check_selectors.check_selector_fixtures.main
        old_report_errors = check_selectors.report_errors
        check_selectors.check_selector_fixtures.main = lambda: calls.append("fixtures") or 0
        check_selectors.report_errors = lambda _errors, _message: None
        try:
            rc = check_selectors.main(["--check-fixtures"])
        finally:
            check_selectors.check_selector_fixtures.main = old_fixture_main
            check_selectors.report_errors = old_report_errors
        self.assertEqual(rc, 0)
        self.assertEqual(calls, ["fixtures"])


if __name__ == "__main__":
    unittest.main()
