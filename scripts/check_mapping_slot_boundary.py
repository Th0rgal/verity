#!/usr/bin/env python3
"""Ensure proof interpreters depend on the MappingSlot abstraction boundary.

This guard supports issue #259 migration by preventing new direct imports of
`Compiler.Proofs.MappingEncoding` outside `Compiler/Proofs/MappingSlot.lean`.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS_DIR = ROOT / "Compiler" / "Proofs"

ALLOWED_MAPPING_ENCODING_IMPORTERS = {
    PROOFS_DIR / "MappingSlot.lean",
}

REQUIRED_ABSTRACTION_IMPORTS = {
    PROOFS_DIR / "IRGeneration" / "IRInterpreter.lean",
    PROOFS_DIR / "YulGeneration" / "Semantics.lean",
}

BUILTINS_FILE = PROOFS_DIR / "YulGeneration" / "Builtins.lean"

IMPORT_MAPPING_ENCODING_RE = re.compile(r"^\s*import\s+Compiler\.Proofs\.MappingEncoding\s*$", re.MULTILINE)
IMPORT_MAPPING_SLOT_RE = re.compile(r"^\s*import\s+Compiler\.Proofs\.MappingSlot\s*$", re.MULTILINE)
ABSTRACT_SLOT_REF_RE = re.compile(r"Compiler\.Proofs\.abstractMappingSlot")
ABSTRACT_LOAD_REF_RE = re.compile(r"Compiler\.Proofs\.abstractLoadStorageOrMapping")
ABSTRACT_STORE_REF_RE = re.compile(r"Compiler\.Proofs\.abstractStoreStorageOrMapping")
ABSTRACT_STORE_ENTRY_REF_RE = re.compile(r"Compiler\.Proofs\.abstractStoreMappingEntry")
DIRECT_MAPPING_ENCODING_SYMBOL_REF_RE = re.compile(
    r"Compiler\.Proofs\.(?:mappingTag|encodeMappingSlot|decodeMappingSlot|encodeNestedMappingSlot|normalizeMappingBaseSlot)"
)
LEGACY_ALIAS_SYMBOL_RE = re.compile(r"\b(?:mappingTag|encodeMappingSlot|decodeMappingSlot)\b")


def main() -> int:
    errors: list[str] = []

    for lean_file in PROOFS_DIR.rglob("*.lean"):
        text = lean_file.read_text(encoding="utf-8")

        if IMPORT_MAPPING_ENCODING_RE.search(text) and lean_file not in ALLOWED_MAPPING_ENCODING_IMPORTERS:
            rel = lean_file.relative_to(ROOT)
            errors.append(
                f"{rel}: direct import of Compiler.Proofs.MappingEncoding is disallowed; "
                "import Compiler.Proofs.MappingSlot instead"
            )

    for lean_file in REQUIRED_ABSTRACTION_IMPORTS:
        text = lean_file.read_text(encoding="utf-8")
        rel = lean_file.relative_to(ROOT)

        if not IMPORT_MAPPING_SLOT_RE.search(text):
            errors.append(f"{rel}: missing required import Compiler.Proofs.MappingSlot")

        if not ABSTRACT_STORE_REF_RE.search(text):
            errors.append(f"{rel}: missing reference to Compiler.Proofs.abstractStoreStorageOrMapping")

        if not ABSTRACT_STORE_ENTRY_REF_RE.search(text):
            errors.append(f"{rel}: missing reference to Compiler.Proofs.abstractStoreMappingEntry")

        if DIRECT_MAPPING_ENCODING_SYMBOL_REF_RE.search(text):
            errors.append(
                f"{rel}: direct reference to MappingEncoding symbol is disallowed; "
                "use MappingSlot abstraction symbols instead"
            )

        if LEGACY_ALIAS_SYMBOL_RE.search(text):
            errors.append(
                f"{rel}: legacy mapping symbol names (mappingTag/encodeMappingSlot/decodeMappingSlot) "
                "are disallowed; use abstractMapping* names directly"
            )

    builtins_text = BUILTINS_FILE.read_text(encoding="utf-8")
    builtins_rel = BUILTINS_FILE.relative_to(ROOT)

    if not IMPORT_MAPPING_SLOT_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing required import Compiler.Proofs.MappingSlot")

    if not ABSTRACT_SLOT_REF_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing reference to Compiler.Proofs.abstractMappingSlot")

    if not ABSTRACT_LOAD_REF_RE.search(builtins_text):
        errors.append(f"{builtins_rel}: missing reference to Compiler.Proofs.abstractLoadStorageOrMapping")

    if errors:
        print("Mapping slot boundary check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print("✓ Mapping slot boundary is enforced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
