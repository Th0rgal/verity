#!/usr/bin/env python3

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import check_macro_translate_invariant_coverage as check


class MacroTranslateInvariantCoverageTests(unittest.TestCase):
    def test_passes_when_contracts_match_suite_entries(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts"
            contracts_dir.mkdir(parents=True, exist_ok=True)
            (contracts_dir / "Core.lean").write_text(
                """
                verity_contract Counter where
                  storage
                verity_contract Owned where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateInvariantTest.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.Counter.spec
                  , Contracts.MacroContracts.Owned.spec
                  ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 0)

    def test_fails_when_contract_is_missing_from_suite(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts"
            contracts_dir.mkdir(parents=True, exist_ok=True)
            (contracts_dir / "Core.lean").write_text(
                """
                verity_contract Counter where
                  storage
                verity_contract Owned where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateInvariantTest.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.Counter.spec ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 1)

    def test_fails_when_suite_has_unknown_contract(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts"
            contracts_dir.mkdir(parents=True, exist_ok=True)
            (contracts_dir / "Core.lean").write_text(
                """
                verity_contract Counter where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateInvariantTest.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.Counter.spec
                  , Contracts.MacroContracts.Ghost.spec
                  ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
