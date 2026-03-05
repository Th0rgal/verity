#!/usr/bin/env python3
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import property_utils


class PropertyUtilsContractNameTests(unittest.TestCase):
    def test_load_manifest_allows_contract_names_starting_with_underscore(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            manifest = Path(tmpdir) / "property_manifest.json"
            manifest.write_text('{"_Vault":["theorem_ok"]}\n', encoding="utf-8")

            original_manifest = property_utils.MANIFEST
            try:
                property_utils.MANIFEST = manifest
                loaded = property_utils.load_manifest()
            finally:
                property_utils.MANIFEST = original_manifest

            self.assertEqual(loaded, {"_Vault": {"theorem_ok"}})

    def test_collect_covered_allows_property_files_with_underscore_contract(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            test_dir = Path(tmpdir)
            (test_dir / "Property_Vault.t.sol").write_text(
                "// SPDX-License-Identifier: MIT\n"
                "/// Property 1: theorem_ok\n"
                "contract Property_Vault {}\n",
                encoding="utf-8",
            )

            original_test_dir = property_utils.TEST_DIR
            try:
                property_utils.TEST_DIR = test_dir
                covered = property_utils.collect_covered()
            finally:
                property_utils.TEST_DIR = original_test_dir

            self.assertEqual(covered, {"_Vault": {"theorem_ok"}})

    def test_extract_manifest_from_proofs_allows_underscore_contract_dirs(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            proofs_dir = root / "Proofs"
            examples_dir = root / "Examples"
            proofs_dir.mkdir()
            examples_dir.mkdir()

            contract_dir = proofs_dir / "_Vault"
            contract_dir.mkdir()
            proofs_subdir = contract_dir / "Proofs"
            proofs_subdir.mkdir()
            (proofs_subdir / "Basic.lean").write_text(
                "theorem theorem_ok : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            original_proofs_dir = property_utils.PROOFS_DIR
            original_examples_dir = property_utils.EXAMPLES_DIR
            try:
                property_utils.PROOFS_DIR = proofs_dir
                property_utils.EXAMPLES_DIR = examples_dir
                manifest = property_utils.extract_manifest_from_proofs()
            finally:
                property_utils.PROOFS_DIR = original_proofs_dir
                property_utils.EXAMPLES_DIR = original_examples_dir

            self.assertEqual(manifest, {"_Vault": ["theorem_ok"]})


class PropertyUtilsPropertyTagTests(unittest.TestCase):
    def test_extract_property_names_rejects_plain_line_comment_tag(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "PropertyCounter.t.sol"
            path.write_text(
                "pragma solidity ^0.8.13;\n"
                "contract PropertyCounter {\n"
                "    function test_note_only() public {\n"
                "        // Property: fake_from_line_comment\n"
                "    }\n"
                "}\n",
                encoding="utf-8",
            )

            names = property_utils.extract_property_names(path)
            self.assertEqual(names, [])

    def test_extract_property_names_accepts_structured_doc_tags(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "PropertyCounter.t.sol"
            path.write_text(
                "pragma solidity ^0.8.13;\n"
                "contract PropertyCounter {\n"
                "    /// Property 1: theorem_indexed\n"
                "    /// Property: theorem_simple\n"
                "    /**\n"
                "     * Property 2: theorem_block_doc\n"
                "     */\n"
                "}\n",
                encoding="utf-8",
            )

            names = property_utils.extract_property_names(path)
            self.assertEqual(names, ["theorem_indexed", "theorem_simple", "theorem_block_doc"])


class PropertyUtilsTheoremExtractionTests(unittest.TestCase):
    def test_collect_theorems_ignores_block_and_line_comments(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "/-\n"
                " theorem ghost_from_comment : True := by\n"
                "   trivial\n"
                "-/\n"
                "\n"
                "-- theorem ghost_from_line_comment : True := by\n"
                "theorem real_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path)
            self.assertEqual(names, ["real_theorem"])

    def test_collect_theorems_accepts_declaration_prefixes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "theorem plain_theorem : True := by\n"
                "  trivial\n"
                "\n"
                "@[simp] theorem simp_theorem : True := by\n"
                "  trivial\n"
                "\n"
                "private theorem private_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path, include_helpers=True)
            self.assertEqual(names, ["plain_theorem", "simp_theorem", "private_theorem"])

    def test_collect_theorems_accepts_multiline_attribute_block(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "@[\n"
                "  simp,\n"
                "  reducible\n"
                "]\n"
                "theorem multi_attr_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path, include_helpers=True)
            self.assertEqual(names, ["multi_attr_theorem"])

    def test_collect_theorems_excludes_helper_declarations_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "Spec.lean"
            path.write_text(
                "theorem plain_theorem : True := by\n"
                "  trivial\n"
                "@[simp] theorem simp_theorem : True := by\n"
                "  trivial\n"
                "private theorem private_theorem : True := by\n"
                "  trivial\n",
                encoding="utf-8",
            )

            names = property_utils.collect_theorems(path)
            self.assertEqual(names, ["plain_theorem"])

if __name__ == "__main__":
    unittest.main()
