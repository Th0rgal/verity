#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_selectors import extract_compile_selectors, extract_specs


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
    def test_extract_specs_supports_macro_alias_defs(self) -> None:
        rows = extract_specs(
            "def counterSpec : CompilationModel := Contracts.MacroContracts.Counter.spec\n"
        )
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0].def_name, "counterSpec")
        self.assertEqual(rows[0].contract_name, "Counter")
        self.assertIn("increment()", rows[0].signatures)
        self.assertIn("previewAddTwice(uint256)", rows[0].signatures)


if __name__ == "__main__":
    unittest.main()
