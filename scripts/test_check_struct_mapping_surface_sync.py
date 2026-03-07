from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_struct_mapping_surface_sync as check


class StructMappingSurfaceSyncTests(unittest.TestCase):
    def _write_fixture_tree(
        self,
        root: Path,
        *,
        types_text: str,
        roadmap: str,
        compiler_doc: str,
        add_contract: str,
    ) -> None:
        types_path = root / "Compiler" / "CompilationModel" / "Types.lean"
        types_path.parent.mkdir(parents=True, exist_ok=True)
        types_path.write_text(types_text, encoding="utf-8")

        roadmap_path = root / "docs" / "ROADMAP.md"
        roadmap_path.parent.mkdir(parents=True, exist_ok=True)
        roadmap_path.write_text(roadmap, encoding="utf-8")

        compiler_path = root / "docs-site" / "content" / "compiler.mdx"
        compiler_path.parent.mkdir(parents=True, exist_ok=True)
        compiler_path.write_text(compiler_doc, encoding="utf-8")

        add_contract_path = root / "docs-site" / "content" / "add-contract.mdx"
        add_contract_path.parent.mkdir(parents=True, exist_ok=True)
        add_contract_path.write_text(add_contract, encoding="utf-8")

    def _run_check(
        self,
        *,
        types_text: str,
        roadmap: str,
        compiler_doc: str,
        add_contract: str,
    ) -> tuple[int, str]:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            self._write_fixture_tree(
                root,
                types_text=types_text,
                roadmap=roadmap,
                compiler_doc=compiler_doc,
                add_contract=add_contract,
            )

            old_root = check.ROOT
            old_types = check.TYPES_PATH
            old_targets = check.TARGET_FILES
            check.ROOT = root
            check.TYPES_PATH = root / "Compiler" / "CompilationModel" / "Types.lean"
            check.TARGET_FILES = {
                "ROADMAP": root / "docs" / "ROADMAP.md",
                "COMPILER_DOC": root / "docs-site" / "content" / "compiler.mdx",
                "ADD_CONTRACT": root / "docs-site" / "content" / "add-contract.mdx",
            }
            try:
                stdout = io.StringIO()
                stderr = io.StringIO()
                with redirect_stdout(stdout), redirect_stderr(stderr):
                    rc = check.main()
                return rc, stdout.getvalue() + stderr.getvalue()
            finally:
                check.ROOT = old_root
                check.TYPES_PATH = old_types
                check.TARGET_FILES = old_targets

    def test_docs_note_required_when_struct_mapping_surface_exists(self) -> None:
        types_text = textwrap.dedent(
            """
            | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
            | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMember)
            | structMember (field : String) (key : Expr) (memberName : String)
            | structMember2 (field : String) (key1 key2 : Expr) (memberName : String)
            | setStructMember (field : String) (key : Expr) (memberName : String) (value : Expr)
            | setStructMember2 (field : String) (key1 key2 : Expr) (memberName : String) (value : Expr)
            """
        )
        note = textwrap.dedent(
            """
            FieldType.mappingStruct` / `FieldType.mappingStruct2` plus `Expr.structMember` / `Stmt.setStructMember` now make struct-valued mappings and packed submembers first-class.
            `structMember "f" key "member"`
            `structMember2 "f" k1 k2 "member"`
            `setStructMember "f" key "member" val`
            `setStructMember2 "f" k1 k2 "member" val`
            For Morpho-style `mapping(K => Struct)` / `mapping(K1 => mapping(K2 => Struct))` layouts, declare `FieldType.mappingStruct` / `FieldType.mappingStruct2`.
            `generate_contract.py` currently scaffolds scalar fields plus simple `mapping(address => uint256)` / `mapping(uint256 => uint256)` storage only.
            For `mappingStruct` / `mappingStruct2` layouts with packed members, use the native `verity_contract` storage forms `MappingStruct(...)` / `MappingStruct2(...)` and the corresponding `structMember` / `setStructMember` operations directly.
            """
        )
        rc, output = self._run_check(
            types_text=types_text,
            roadmap=note,
            compiler_doc=note,
            add_contract=note,
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("docs note required", output)

    def test_missing_docs_note_fails_when_struct_mapping_surface_exists(self) -> None:
        types_text = textwrap.dedent(
            """
            | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
            | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMember)
            | structMember (field : String) (key : Expr) (memberName : String)
            | structMember2 (field : String) (key1 key2 : Expr) (memberName : String)
            | setStructMember (field : String) (key : Expr) (memberName : String) (value : Expr)
            | setStructMember2 (field : String) (key1 key2 : Expr) (memberName : String) (value : Expr)
            """
        )
        rc, output = self._run_check(
            types_text=types_text,
            roadmap="storage layout controls exist\n",
            compiler_doc="mapping words exist\n",
            add_contract="use the scaffold generator\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("compiler.mdx is out of sync", output)

    def test_partial_struct_mapping_surface_fails_closed(self) -> None:
        types_text = textwrap.dedent(
            """
            | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
            | structMember (field : String) (key : Expr) (memberName : String)
            | setStructMember (field : String) (key : Expr) (memberName : String) (value : Expr)
            """
        )
        rc, output = self._run_check(
            types_text=types_text,
            roadmap="storage layout controls exist\n",
            compiler_doc="mapping words exist\n",
            add_contract="use the scaffold generator\n",
        )
        self.assertEqual(rc, 1)
        self.assertIn("partial struct-mapping surface support", output)
        self.assertIn("missing: | mappingStruct2, | structMember2, | setStructMember2", output)

    def test_docs_note_not_required_without_struct_mapping_surface(self) -> None:
        rc, output = self._run_check(
            types_text="| mappingTyped (mt : MappingType)\n",
            roadmap="storage layout controls exist\n",
            compiler_doc="mapping words exist\n",
            add_contract="use the scaffold generator\n",
        )
        self.assertEqual(rc, 0, output)
        self.assertIn("docs note not required", output)

    def test_repository_docs_are_currently_in_sync(self) -> None:
        stdout = io.StringIO()
        stderr = io.StringIO()
        with redirect_stdout(stdout), redirect_stderr(stderr):
            rc = check.main()
        output = stdout.getvalue() + stderr.getvalue()
        self.assertEqual(rc, 0, output)


if __name__ == "__main__":
    unittest.main()
