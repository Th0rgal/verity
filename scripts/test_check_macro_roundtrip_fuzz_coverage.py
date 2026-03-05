#!/usr/bin/env python3

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import check_macro_roundtrip_fuzz_coverage as check


class MacroRoundTripFuzzCoverageTests(unittest.TestCase):
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
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

    def test_main_recursively_discovers_nested_contract_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts" / "MacroContracts"
            (contracts_dir / "Compat").mkdir(parents=True, exist_ok=True)
            (contracts_dir / "Compat" / "Nested.lean").write_text(
                """
                verity_contract NestedCounter where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.NestedCounter.spec ]
                """,
                encoding="utf-8",
            )

            with mock.patch(
                "sys.argv",
                [
                    "check_macro_roundtrip_fuzz_coverage.py",
                    "--contracts-dir",
                    str(contracts_dir),
                    "--fuzz-suite",
                    str(suite),
                ],
            ):
                self.assertEqual(check.main(), 0)

    def test_accepts_nested_module_path_suite_entry(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts"
            contracts_dir.mkdir(parents=True, exist_ok=True)
            (contracts_dir / "Core.lean").write_text(
                """
                verity_contract NestedCounter where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.Compat.Nested.NestedCounter.spec ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 0)

    def test_fails_when_macro_specs_definition_missing(self) -> None:
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                -- no macroSpecs definition on purpose
                def unrelated : Nat := 0
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 1)

    def test_fails_on_duplicate_macro_specs_entry(self) -> None:
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                private def macroSpecs : List CompilationModel :=
                  [ Contracts.MacroContracts.Counter.spec
                  , Contracts.MacroContracts.Counter.spec
                  ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 1)

    def test_fails_on_duplicate_contract_declaration_name(self) -> None:
        with tempfile.TemporaryDirectory(dir=check.ROOT) as tmpdir:
            root = Path(tmpdir)
            contracts_dir = root / "Contracts"
            contracts_dir.mkdir(parents=True, exist_ok=True)
            (contracts_dir / "A.lean").write_text(
                """
                verity_contract Counter where
                  storage
                """,
                encoding="utf-8",
            )
            (contracts_dir / "B.lean").write_text(
                """
                verity_contract Counter where
                  storage
                """,
                encoding="utf-8",
            )
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                private def macroSpecs :=
                  [ Contracts.MacroContracts.Counter.spec ]
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage(
                [contracts_dir / "A.lean", contracts_dir / "B.lean"],
                suite,
            )
            self.assertEqual(rc, 1)

    def test_ignores_spec_references_outside_macro_specs(self) -> None:
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
            suite = root / "MacroTranslateRoundTripFuzz.lean"
            suite.write_text(
                """
                private def macroSpecs : List CompilationModel :=
                  [ Contracts.MacroContracts.Counter.spec ]

                -- This should not count towards macroSpecs coverage.
                #check Contracts.MacroContracts.Owned.spec
                """,
                encoding="utf-8",
            )

            rc = check._check_coverage([contracts_dir / "Core.lean"], suite)
            self.assertEqual(rc, 1)


if __name__ == "__main__":
    unittest.main()
