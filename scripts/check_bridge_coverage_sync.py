#!/usr/bin/env python3
"""Ensure bridge-coverage docs stay in sync with the proven builtin bridge set."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE_LEMMAS = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanBridgeLemmas.lean"
TARGET_FILES = {
    "AUDIT": ROOT / "AUDIT.md",
    "AXIOMS": ROOT / "AXIOMS.md",
    "ARITHMETIC_PROFILE": ROOT / "docs" / "ARITHMETIC_PROFILE.md",
    "INTERPRETER_FEATURE_MATRIX": ROOT / "docs" / "INTERPRETER_FEATURE_MATRIX.md",
    "END_TO_END": ROOT / "Compiler" / "Proofs" / "EndToEnd.lean",
}

PURE_BUILTINS = [
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "lt",
    "gt",
    "eq",
    "iszero",
    "and",
    "or",
    "xor",
    "not",
    "shl",
    "shr",
]


def normalize_ws(text: str) -> str:
    return " ".join(text.split())


def code_list(names: list[str]) -> str:
    quoted = [f"`{name}`" for name in names]
    if not quoted:
        return ""
    if len(quoted) == 1:
        return quoted[0]
    if len(quoted) == 2:
        return f"{quoted[0]} and {quoted[1]}"
    return f"{', '.join(quoted[:-1])}, and {quoted[-1]}"


def code_csv(names: list[str]) -> str:
    return ", ".join(f"`{name}`" for name in names)


def plain_code_subject(names: list[str]) -> str:
    items = code_list(names)
    if len(names) == 1:
        return items
    return f"{items} collectively"


def extract_universal_builtins(text: str) -> list[str]:
    found = {
        match.group(1)
        for match in re.finditer(r"@\[simp\]\s+theorem\s+evalBuiltinCall_([A-Za-z0-9]+)_bridge\b", text)
    }
    return [name for name in PURE_BUILTINS if name in found]


def expected_snippets(universal: list[str], remaining: list[str]) -> dict[str, list[str]]:
    count = len(universal)
    universal_codes = code_list(universal)
    remaining_codes = code_list(remaining)

    audit_remaining = (
        "All pure bridge cases are now covered by universal symbolic lemmas."
        if not remaining
        else (
            f"The remaining pure bridge case ({remaining_codes}) is still covered by concrete regression checks."
            if len(remaining) == 1
            else f"The remaining pure bridge cases ({remaining_codes}) are still covered by concrete regression checks."
        )
    )
    axioms_remaining = (
        "with no remaining pure builtins relying only on concrete bridge checks"
        if not remaining
        else (
            f"while {remaining_codes} is covered by concrete bridge checks"
            if len(remaining) == 1
            else f"while {remaining_codes} are covered by concrete bridge checks"
        )
    )
    arithmetic_remaining = (
        "concrete bridge smoke tests are no longer needed for any pure builtin"
        if not remaining
        else f"concrete bridge smoke tests for {remaining_codes}"
    )
    arithmetic_summary = (
        "15/15 pure EVMYulLean-backed builtins have universal bridge lemmas."
        if not remaining
        else (
            f"{count}/15 pure EVMYulLean-backed builtins have universal bridge lemmas; {remaining_codes} still relies on concrete smoke tests."
            if len(remaining) == 1
            else f"{count}/15 pure EVMYulLean-backed builtins have universal bridge lemmas; {plain_code_subject(remaining)} still rely on concrete smoke tests."
        )
    )
    interpreter_remaining = (
        "and none still require concrete-only regression coverage"
        if not remaining
        else (
            f"while {remaining_codes} is currently guarded by concrete regression checks"
            if len(remaining) == 1
            else f"while {plain_code_subject(remaining)} are currently guarded by concrete regression checks"
        )
    )
    end_to_end_remaining = (
        "replacement coverage: universal bridge lemmas for all pure bridged builtins."
        if not remaining
        else f"replacement coverage: universal bridge lemmas for all pure bridged builtins except {remaining_codes}, plus concrete smoke tests for {remaining_codes}."
    )

    return {
        "AUDIT": [
            f"{count} universal pure bridge theorems are now proven",
            audit_remaining,
        ],
        "AXIOMS": [
            f"The EVMYulLean bridge currently has universal equivalence lemmas for {count} of them ({code_csv(universal)})",
            axioms_remaining,
        ],
        "ARITHMETIC_PROFILE": [
            f"universal bridge lemmas for {count} pure builtins: {universal_codes}",
            arithmetic_remaining,
            arithmetic_summary,
        ],
        "INTERPRETER_FEATURE_MATRIX": [
            f"{count} are discharged by universal symbolic lemmas",
            interpreter_remaining,
        ],
        "END_TO_END": [
            end_to_end_remaining,
        ],
    }


def main() -> int:
    errors: list[str] = []
    if not BRIDGE_LEMMAS.exists():
        print(f"Missing: {BRIDGE_LEMMAS.relative_to(ROOT)}", file=sys.stderr)
        return 1

    universal = extract_universal_builtins(BRIDGE_LEMMAS.read_text(encoding="utf-8"))
    remaining = [name for name in PURE_BUILTINS if name not in universal]
    expected = expected_snippets(universal, remaining)

    for label, path in TARGET_FILES.items():
        if not path.exists():
            errors.append(f"Missing: {path.relative_to(ROOT)}")
            continue
        normalized = normalize_ws(path.read_text(encoding="utf-8"))
        for snippet in expected[label]:
            if normalize_ws(snippet) not in normalized:
                errors.append(
                    f"{path.relative_to(ROOT)} is out of sync with bridge coverage: missing `{snippet}`"
                )

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(
        "bridge coverage sync passed: "
        f"{len(universal)}/{len(PURE_BUILTINS)} pure builtins universally bridged; "
        f"remaining concrete-only: {', '.join(remaining) if remaining else 'none'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
