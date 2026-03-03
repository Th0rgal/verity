#!/usr/bin/env python3
"""Ensure proof interpreters depend on the MappingSlot abstraction boundary.

This guard enforces the mapping-slot abstraction boundary and ensures the active
proof backend remains the keccak-faithful model.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

from property_utils import scrub_lean_code

ROOT = Path(__file__).resolve().parents[1]
PROOFS_DIR = ROOT / "Compiler" / "Proofs"
MAPPING_SLOT_FILE = PROOFS_DIR / "MappingSlot.lean"
TRUST_ASSUMPTIONS_FILE = ROOT / "TRUST_ASSUMPTIONS.md"

ALLOWED_MAPPING_ENCODING_IMPORTERS: set[Path] = set()

REQUIRED_ABSTRACTION_IMPORTS = {
    PROOFS_DIR / "IRGeneration" / "IRInterpreter.lean",
    PROOFS_DIR / "YulGeneration" / "Semantics.lean",
}

LEGACY_SYMBOL_FORBIDDEN_FILES = REQUIRED_ABSTRACTION_IMPORTS | {
    PROOFS_DIR / "YulGeneration" / "SmokeTests.lean",
}

BUILTINS_FILE = PROOFS_DIR / "YulGeneration" / "Builtins.lean"
IR_INTERPRETER_FILE = PROOFS_DIR / "IRGeneration" / "IRInterpreter.lean"
YUL_SEMANTICS_FILE = PROOFS_DIR / "YulGeneration" / "Semantics.lean"

IMPORT_MAPPING_ENCODING_RE = re.compile(r"^\s*import\s+Compiler\.Proofs\.MappingEncoding\s*$", re.MULTILINE)
IMPORT_MAPPING_SLOT_RE = re.compile(r"^\s*import\s+Compiler\.Proofs\.MappingSlot\s*$", re.MULTILINE)
ABSTRACT_SLOT_REF_RE = re.compile(r"Compiler\.Proofs\.abstractMappingSlot")
ABSTRACT_LOAD_REF_RE = re.compile(r"Compiler\.Proofs\.abstractLoadStorageOrMapping")
ABSTRACT_STORE_REF_RE = re.compile(r"Compiler\.Proofs\.abstractStoreStorageOrMapping")
ABSTRACT_STORE_ENTRY_REF_RE = re.compile(r"Compiler\.Proofs\.abstractStoreMappingEntry")
STATE_MAPPINGS_FIELD_RE = re.compile(r"^\s*mappings\s*:\s*Nat\s*→\s*Nat\s*→\s*Nat", re.MULTILINE)
DIRECT_MAPPING_ENCODING_SYMBOL_REF_RE = re.compile(
    r"Compiler\.Proofs\.(?:mappingTag|encodeMappingSlot|decodeMappingSlot|encodeNestedMappingSlot|normalizeMappingBaseSlot)"
)
LEGACY_ALIAS_SYMBOL_RE = re.compile(
    r"\b(?:mappingTag|encodeMappingSlot|decodeMappingSlot|encodeNestedMappingSlot|normalizeMappingBaseSlot)\b"
)
ACTIVE_BACKEND_KECCAK_RE = re.compile(
    r"def\s+activeMappingSlotBackend\s*:\s*MappingSlotBackend\s*:=\s*\.keccak"
)
ACTIVE_BACKEND_FAITHFUL_TRUE_RE = re.compile(
    r"def\s+activeMappingSlotBackendIsEvmFaithful\s*:\s*Bool\s*:=\s*"
    r"(?:true|[\s\S]*?\|\s*\.tagged\s*=>\s*false[\s\S]*?\|\s*\.keccak\s*=>\s*true)"
)
ABI_ENCODE_MAPPING_SLOT_RE = re.compile(r"def\s+abiEncodeMappingSlot\s*\(")
SOLIDITY_MAPPING_SLOT_RE = re.compile(r"def\s+solidityMappingSlot\s*\(")
KECCAK_ROUTING_RE = re.compile(
    r"(?:def\s+abstractMappingSlot\s*\([^)]*\)\s*:\s*Nat\s*:=\s*solidityMappingSlot\s+baseSlot\s+key)"
    r"|(?:\|\s*\.keccak\s*=>\s*solidityMappingSlot\s+baseSlot\s+key)"
)
KECCAK_LOAD_ENTRY_ROUTING_RE = re.compile(
    r"(?:def\s+abstractLoadMappingEntry[\s\S]*?:=\s*(?:let\s+_.*?\n\s*)?storage\s+\(solidityMappingSlot\s+baseSlot\s+key\))"
    r"|(?:def\s+abstractLoadMappingEntry[\s\S]*?\|\s*\.keccak\s*=>\s*storage\s+\(solidityMappingSlot\s+baseSlot\s+key\))"
)
KECCAK_STORE_ENTRY_ROUTING_RE = re.compile(
    r"(?:def\s+abstractStoreMappingEntry[\s\S]*?:=\s*fun\s+s\s*=>\s*if\s+s\s*=\s*solidityMappingSlot\s+baseSlot\s+key)"
    r"|(?:def\s+abstractStoreMappingEntry[\s\S]*?\|\s*\.keccak\s*=>[\s\S]*?s\s*=\s*solidityMappingSlot\s+baseSlot\s+key)"
)


def main() -> int:
    errors: list[str] = []

    mapping_slot_text = scrub_lean_code(MAPPING_SLOT_FILE.read_text(encoding="utf-8"))
    trust_text = TRUST_ASSUMPTIONS_FILE.read_text(encoding="utf-8")

    if not ACTIVE_BACKEND_KECCAK_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: expected explicit active backend marker "
            "`activeMappingSlotBackend := .keccak`"
        )

    if not ACTIVE_BACKEND_FAITHFUL_TRUE_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: expected explicit "
            "`activeMappingSlotBackendIsEvmFaithful` marker proving keccak faithfulness"
        )

    if not ABI_ENCODE_MAPPING_SLOT_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(f"{rel}: missing `abiEncodeMappingSlot` helper for keccak backend")

    if not SOLIDITY_MAPPING_SLOT_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(f"{rel}: missing `solidityMappingSlot` helper for keccak backend")

    if not KECCAK_ROUTING_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: expected `abstractMappingSlot` "
            "to route through `solidityMappingSlot`"
        )

    if not KECCAK_LOAD_ENTRY_ROUTING_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: expected `abstractLoadMappingEntry` "
            "to read flat storage via `solidityMappingSlot`"
        )

    if not KECCAK_STORE_ENTRY_ROUTING_RE.search(mapping_slot_text):
        rel = MAPPING_SLOT_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: expected `abstractStoreMappingEntry` "
            "to write flat storage via `solidityMappingSlot`"
        )

    if "activeMappingSlotBackend = .keccak" not in trust_text:
        rel = TRUST_ASSUMPTIONS_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: must document current mapping backend scope "
            "(`activeMappingSlotBackend = .keccak`)"
        )

    if "ffi.KEC" not in trust_text:
        rel = TRUST_ASSUMPTIONS_FILE.relative_to(ROOT)
        errors.append(
            f"{rel}: must document external keccak trust boundary (`ffi.KEC`)"
        )

    for lean_file in PROOFS_DIR.rglob("*.lean"):
        text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))

        if IMPORT_MAPPING_ENCODING_RE.search(text) and lean_file not in ALLOWED_MAPPING_ENCODING_IMPORTERS:
            rel = lean_file.relative_to(ROOT)
            errors.append(
                f"{rel}: direct import of Compiler.Proofs.MappingEncoding is disallowed; "
                "import Compiler.Proofs.MappingSlot instead"
            )

    for lean_file in REQUIRED_ABSTRACTION_IMPORTS:
        text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))
        rel = lean_file.relative_to(ROOT)

        if not IMPORT_MAPPING_SLOT_RE.search(text):
            errors.append(f"{rel}: missing required import Compiler.Proofs.MappingSlot")

        if not ABSTRACT_STORE_REF_RE.search(text):
            errors.append(f"{rel}: missing reference to Compiler.Proofs.abstractStoreStorageOrMapping")

        if not ABSTRACT_STORE_ENTRY_REF_RE.search(text):
            errors.append(f"{rel}: missing reference to Compiler.Proofs.abstractStoreMappingEntry")

    for lean_file in LEGACY_SYMBOL_FORBIDDEN_FILES:
        text = scrub_lean_code(lean_file.read_text(encoding="utf-8"))
        rel = lean_file.relative_to(ROOT)

        if DIRECT_MAPPING_ENCODING_SYMBOL_REF_RE.search(text):
            errors.append(
                f"{rel}: direct reference to MappingEncoding symbol is disallowed; "
                "use MappingSlot abstraction symbols instead"
            )

        if LEGACY_ALIAS_SYMBOL_RE.search(text):
            errors.append(
                f"{rel}: legacy mapping symbol names "
                "(mappingTag/encodeMappingSlot/decodeMappingSlot/encodeNestedMappingSlot/normalizeMappingBaseSlot) "
                "are disallowed; use MappingSlot/solidityMappingSlot-based names directly"
            )

    builtins_text = scrub_lean_code(BUILTINS_FILE.read_text(encoding="utf-8"))
    builtins_rel = BUILTINS_FILE.relative_to(ROOT)

    if not IMPORT_MAPPING_SLOT_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing required import Compiler.Proofs.MappingSlot")

    if not ABSTRACT_SLOT_REF_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing reference to Compiler.Proofs.abstractMappingSlot")

    if not ABSTRACT_LOAD_REF_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing reference to Compiler.Proofs.abstractLoadStorageOrMapping")

    for state_file in (IR_INTERPRETER_FILE, YUL_SEMANTICS_FILE):
        state_text = scrub_lean_code(state_file.read_text(encoding="utf-8"))
        state_rel = state_file.relative_to(ROOT)
        if STATE_MAPPINGS_FIELD_RE.search(state_text):
            errors.append(
                f"{state_rel}: execution state must not define a separate `mappings` table; "
                "mapping semantics must flow through flat storage only"
            )

    if errors:
        print("Mapping slot boundary check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print("✓ Mapping slot boundary is enforced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
