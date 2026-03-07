#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_macro_roundtrip_fuzz_coverage


class MacroRoundTripFuzzCoverageTests(unittest.TestCase):
    def test_collect_contracts_ignores_guard_msgs_negative_fixtures(self) -> None:
        text = """
        verity_contract HappyPath where
          storage
            counter : Uint256 := slot 0
          function read () : Uint256 := do
            return 0

        #guard_msgs in
        verity_contract NegativeFixture where
          storage
            counter : Uint256 := slot 0
          function read () : Uint256 := do
            return 0
        end NegativeFixture
        """

        self.assertEqual(
            check_macro_roundtrip_fuzz_coverage._collect_contracts_from_text(text),
            ["HappyPath"],
        )

    def test_collect_contracts_resets_guard_after_non_contract_command(self) -> None:
        text = """
        #guard_msgs in
        #check Uint256

        verity_contract HappyPath where
          storage
            counter : Uint256 := slot 0
          function read () : Uint256 := do
            return 0
        """

        self.assertEqual(
            check_macro_roundtrip_fuzz_coverage._collect_contracts_from_text(text),
            ["HappyPath"],
        )

    def test_collect_contracts_preserves_duplicate_names_in_one_file(self) -> None:
        text = """
        verity_contract Duplicate where
          storage
            counter : Uint256 := slot 0
          function read () : Uint256 := do
            return 0

        verity_contract Duplicate where
          storage
            counter : Uint256 := slot 1
          function readAgain () : Uint256 := do
            return 1
        """

        self.assertEqual(
            check_macro_roundtrip_fuzz_coverage._collect_contracts_from_text(text),
            ["Duplicate", "Duplicate"],
        )


if __name__ == "__main__":
    unittest.main()
