#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_mapping_slot_boundary
import property_utils


class MappingSlotBoundaryTests(unittest.TestCase):
    def test_comment_decoys_do_not_satisfy_required_markers(self) -> None:
        with tempfile.TemporaryDirectory(dir=property_utils.ROOT) as tmpdir:
            root = Path(tmpdir)
            proofs = root / "Compiler" / "Proofs"
            (proofs / "IRGeneration").mkdir(parents=True)
            (proofs / "YulGeneration").mkdir(parents=True)

            mapping_slot = proofs / "MappingSlot.lean"
            ir = proofs / "IRGeneration" / "IRInterpreter.lean"
            sem = proofs / "YulGeneration" / "Semantics.lean"
            builtins = proofs / "YulGeneration" / "Builtins.lean"
            trust = root / "TRUST_ASSUMPTIONS.md"

            mapping_slot.write_text(
                textwrap.dedent(
                    """
                    -- def activeMappingSlotBackend : MappingSlotBackend := .keccak
                    -- def activeMappingSlotBackendIsEvmFaithful : Bool := true
                    -- def abiEncodeMappingSlot (
                    -- def solidityMappingSlot (
                    -- | .keccak => solidityMappingSlot baseSlot key
                    -- def abstractLoadMappingEntry
                    -- | .keccak => storage (solidityMappingSlot baseSlot key)
                    -- def abstractStoreMappingEntry
                    -- | .keccak =>
                    -- s = solidityMappingSlot baseSlot key, mappings)
                    """
                ),
                encoding="utf-8",
            )
            ir.write_text(
                "import Compiler.Proofs.MappingSlot\n"
                "def x := Compiler.Proofs.abstractStoreStorageOrMapping\n"
                "def y := Compiler.Proofs.abstractStoreMappingEntry\n",
                encoding="utf-8",
            )
            sem.write_text(
                "import Compiler.Proofs.MappingSlot\n"
                "def x := Compiler.Proofs.abstractStoreStorageOrMapping\n"
                "def y := Compiler.Proofs.abstractStoreMappingEntry\n",
                encoding="utf-8",
            )
            builtins.write_text(
                "import Compiler.Proofs.MappingSlot\n"
                "def x := Compiler.Proofs.abstractMappingSlot\n"
                "def y := Compiler.Proofs.abstractLoadStorageOrMapping\n",
                encoding="utf-8",
            )
            trust.write_text(
                "activeMappingSlotBackend = .keccak\nffi.KEC\n",
                encoding="utf-8",
            )

            old_root = check_mapping_slot_boundary.ROOT
            old_proofs = check_mapping_slot_boundary.PROOFS_DIR
            old_mapping_slot = check_mapping_slot_boundary.MAPPING_SLOT_FILE
            old_trust = check_mapping_slot_boundary.TRUST_ASSUMPTIONS_FILE
            old_builtins = check_mapping_slot_boundary.BUILTINS_FILE
            old_allowed = check_mapping_slot_boundary.ALLOWED_MAPPING_ENCODING_IMPORTERS
            old_required = check_mapping_slot_boundary.REQUIRED_ABSTRACTION_IMPORTS
            old_forbidden = check_mapping_slot_boundary.LEGACY_SYMBOL_FORBIDDEN_FILES
            old_ir = check_mapping_slot_boundary.IR_INTERPRETER_FILE
            old_sem = check_mapping_slot_boundary.YUL_SEMANTICS_FILE
            check_mapping_slot_boundary.ROOT = root
            check_mapping_slot_boundary.PROOFS_DIR = proofs
            check_mapping_slot_boundary.MAPPING_SLOT_FILE = mapping_slot
            check_mapping_slot_boundary.TRUST_ASSUMPTIONS_FILE = trust
            check_mapping_slot_boundary.BUILTINS_FILE = builtins
            check_mapping_slot_boundary.ALLOWED_MAPPING_ENCODING_IMPORTERS = set()
            check_mapping_slot_boundary.REQUIRED_ABSTRACTION_IMPORTS = {ir, sem}
            check_mapping_slot_boundary.LEGACY_SYMBOL_FORBIDDEN_FILES = {ir, sem}
            check_mapping_slot_boundary.IR_INTERPRETER_FILE = ir
            check_mapping_slot_boundary.YUL_SEMANTICS_FILE = sem
            try:
                stderr = io.StringIO()
                with redirect_stderr(stderr):
                    rc = check_mapping_slot_boundary.main()
                self.assertEqual(rc, 1)
                err = stderr.getvalue()
                self.assertIn("expected explicit active backend marker", err)
                self.assertIn("missing `abiEncodeMappingSlot` helper", err)
            finally:
                check_mapping_slot_boundary.ROOT = old_root
                check_mapping_slot_boundary.PROOFS_DIR = old_proofs
                check_mapping_slot_boundary.MAPPING_SLOT_FILE = old_mapping_slot
                check_mapping_slot_boundary.TRUST_ASSUMPTIONS_FILE = old_trust
                check_mapping_slot_boundary.BUILTINS_FILE = old_builtins
                check_mapping_slot_boundary.ALLOWED_MAPPING_ENCODING_IMPORTERS = old_allowed
                check_mapping_slot_boundary.REQUIRED_ABSTRACTION_IMPORTS = old_required
                check_mapping_slot_boundary.LEGACY_SYMBOL_FORBIDDEN_FILES = old_forbidden
                check_mapping_slot_boundary.IR_INTERPRETER_FILE = old_ir
                check_mapping_slot_boundary.YUL_SEMANTICS_FILE = old_sem


if __name__ == "__main__":
    unittest.main()
