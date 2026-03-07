#!/usr/bin/env python3
"""Keep struct-mapping storage docs aligned with the compiler surface."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TYPES_PATH = ROOT / "Compiler" / "CompilationModel" / "Types.lean"
TARGET_FILES = {
    "ROADMAP": ROOT / "docs" / "ROADMAP.md",
    "COMPILER_DOC": ROOT / "docs-site" / "content" / "compiler.mdx",
    "ADD_CONTRACT": ROOT / "docs-site" / "content" / "add-contract.mdx",
}


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def struct_mapping_surface_present(types_text: str) -> bool:
    required_tokens = (
        "| mappingStruct ",
        "| mappingStruct2 ",
        "| structMember ",
        "| structMember2 ",
        "| setStructMember ",
        "| setStructMember2 ",
    )
    return all(token in types_text for token in required_tokens)


def expected_snippets(struct_surface_present: bool) -> dict[str, list[str]]:
    if not struct_surface_present:
        return {label: [] for label in TARGET_FILES}

    return {
        "ROADMAP": [
            "FieldType.mappingStruct` / `FieldType.mappingStruct2` plus `Expr.structMember` / `Stmt.setStructMember` now make struct-valued mappings and packed submembers first-class",
        ],
        "COMPILER_DOC": [
            '`structMember "f" key "member"`',
            '`structMember2 "f" k1 k2 "member"`',
            '`setStructMember "f" key "member" val`',
            '`setStructMember2 "f" k1 k2 "member" val`',
            "For Morpho-style `mapping(K => Struct)` / `mapping(K1 => mapping(K2 => Struct))` layouts, declare `FieldType.mappingStruct` / `FieldType.mappingStruct2`",
        ],
        "ADD_CONTRACT": [
            "`generate_contract.py` currently scaffolds scalar fields plus simple `mapping(address => uint256)` / `mapping(uint256 => uint256)` storage only.",
            "For `mappingStruct` / `mappingStruct2` layouts with packed members, start from a handwritten contract/module and use `Expr.structMember` / `Stmt.setStructMember` directly; see issue `#1334`.",
        ],
    }


def main() -> int:
    if not TYPES_PATH.exists():
        print(f"Missing: {TYPES_PATH.relative_to(ROOT)}", file=sys.stderr)
        return 1

    struct_surface_present = struct_mapping_surface_present(
        TYPES_PATH.read_text(encoding="utf-8")
    )
    expected = expected_snippets(struct_surface_present)

    errors: list[str] = []
    for label, path in TARGET_FILES.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in expected[label]:
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with struct-mapping compiler support: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    status = "required" if struct_surface_present else "not required"
    print(f"struct-mapping surface sync passed: docs note {status}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
