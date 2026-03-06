#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_storage_layout import extract_compiler_specs


class CheckStorageLayoutExtractCompilerSpecsTests(unittest.TestCase):
    def test_extract_compiler_specs_supports_macro_alias_defs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            spec_file = Path(tmpdir) / "Specs.lean"
            spec_file.write_text(
                "def ownedSpec : CompilationModel := Contracts.MacroContracts.Owned.spec\n",
                encoding="utf-8",
            )
            rows = extract_compiler_specs(spec_file)

        self.assertIn("Owned", rows)
        self.assertEqual(rows["Owned"], [("owner", "Address", 0)])


if __name__ == "__main__":
    unittest.main()
