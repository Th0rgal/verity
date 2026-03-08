#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_evmyullean_capability_boundary
import evmyullean_capability
import property_utils


class EVMYulLeanCapabilityExtractionTests(unittest.TestCase):
    def test_overlap_boundary_includes_delegated_env_builtins(self) -> None:
        self.assertIn("address", evmyullean_capability.EVMYULLEAN_OVERLAP_BUILTINS)
        self.assertIn("timestamp", evmyullean_capability.EVMYULLEAN_OVERLAP_BUILTINS)
        self.assertIn("chainid", evmyullean_capability.EVMYULLEAN_OVERLAP_BUILTINS)

    def test_extract_found_builtins_resolves_alias_literal(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            builtins_file = Path(tmpdir) / "Builtins.lean"
            builtins_file.write_text(
                "namespace X\n\n"
                "def evalBuiltinCall (func : String) (argVals : List Nat) : Option Nat :=\n"
                "  let op := \"create\"\n"
                "  if func = op then\n"
                "    some 1\n"
                "  else\n"
                "    none\n",
                encoding="utf-8",
            )

            found, diagnostics = evmyullean_capability.extract_found_builtins_with_diagnostics(
                builtins_file
            )
            self.assertEqual(found, {"create"})
            self.assertEqual(diagnostics, [])

    def test_extract_found_builtins_reports_unresolved_non_literal_dispatch(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            builtins_file = Path(tmpdir) / "Builtins.lean"
            builtins_file.write_text(
                "namespace X\n\n"
                "def evalBuiltinCall (func : String) (argVals : List Nat) : Option Nat :=\n"
                "  if func = op then\n"
                "    some 1\n"
                "  else\n"
                "    none\n",
                encoding="utf-8",
            )

            _found, diagnostics = evmyullean_capability.extract_found_builtins_with_diagnostics(
                builtins_file
            )
            self.assertEqual(len(diagnostics), 1)
            self.assertIn("non-literal dispatch", diagnostics[0])

    def test_extract_found_builtins_resolves_typed_alias_chain(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            builtins_file = Path(tmpdir) / "Builtins.lean"
            builtins_file.write_text(
                "namespace X\n\n"
                "def evalBuiltinCall (func : String) (argVals : List Nat) : Option Nat :=\n"
                "  let base : String := \"extcodecopy\"\n"
                "  let op := base\n"
                "  if func = op then\n"
                "    some 1\n"
                "  else\n"
                "    none\n",
                encoding="utf-8",
            )

            found, diagnostics = evmyullean_capability.extract_found_builtins_with_diagnostics(
                builtins_file
            )
            self.assertEqual(found, {"extcodecopy"})
            self.assertEqual(diagnostics, [])

    def test_extract_found_builtins_resolves_parenthesized_literal_alias(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            builtins_file = Path(tmpdir) / "Builtins.lean"
            builtins_file.write_text(
                "namespace X\n\n"
                "def evalBuiltinCall (func : String) (argVals : List Nat) : Option Nat :=\n"
                "  let op := (\"create2\")\n"
                "  if func = op then\n"
                "    some 1\n"
                "  else\n"
                "    none\n",
                encoding="utf-8",
            )

            found, diagnostics = evmyullean_capability.extract_found_builtins_with_diagnostics(
                builtins_file
            )
            self.assertEqual(found, {"create2"})
            self.assertEqual(diagnostics, [])

    def test_boundary_check_fails_closed_on_non_literal_dispatch(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            builtins_file = Path(tmpdir) / "Builtins.lean"
            builtins_file.write_text(
                "namespace X\n\n"
                "def evalBuiltinCall (func : String) (argVals : List Nat) : Option Nat :=\n"
                "  if func = op then\n"
                "    some 1\n"
                "  else\n"
                "    none\n",
                encoding="utf-8",
            )

            old_builtins = check_evmyullean_capability_boundary.BUILTINS_FILE
            check_evmyullean_capability_boundary.BUILTINS_FILE = builtins_file
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_evmyullean_capability_boundary.main()
                self.assertEqual(rc, 1)
                self.assertIn("non-literal builtin dispatch", stderr.getvalue())
            finally:
                check_evmyullean_capability_boundary.BUILTINS_FILE = old_builtins


if __name__ == "__main__":
    unittest.main()
