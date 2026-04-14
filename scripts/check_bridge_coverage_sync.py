#!/usr/bin/env python3
"""Ensure bridge-coverage docs stay in sync with the proven builtin bridge set."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BRIDGE_LEMMAS = ROOT / "Compiler" / "Proofs" / "YulGeneration" / "Backends" / "EvmYulLeanBridgeLemmas.lean"
TARGET_FILES = {
    "TRUST_ASSUMPTIONS": ROOT / "TRUST_ASSUMPTIONS.md",
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
    "addmod",
    "mulmod",
    "exp",
    "sdiv",
    "smod",
    "lt",
    "gt",
    "slt",
    "sgt",
    "eq",
    "iszero",
    "and",
    "or",
    "xor",
    "not",
    "shl",
    "shr",
    "sar",
    "signextend",
    "byte",
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


def extract_admitted_builtins(text: str) -> list[str]:
    """Detect bridge builtins whose core lemma depends on sorry.

    Detects both standalone ``sorry`` lines and inline ``by sorry`` /
    ``:= sorry`` forms, while ignoring sorry mentions in comments, doc
    comments, and markdown status annotations.
    """
    admitted: set[str] = set()
    sorry_pending = False
    bridge_re = re.compile(r"@\[simp\]\s+theorem\s+evalBuiltinCall_([A-Za-z0-9]+)_bridge\b")
    sorry_re = re.compile(r"\bsorry\b")
    comment_re = re.compile(r"^\s*--")
    docstring_re = re.compile(r"^\s*/--")
    status_re = re.compile(r"\*\*Status\*\*")
    for line in text.splitlines():
        # Skip comments, doc comments, and markdown status annotations
        if comment_re.match(line) or docstring_re.match(line) or status_re.search(line):
            continue
        if sorry_re.search(line):
            sorry_pending = True
        if sorry_pending:
            m = bridge_re.search(line)
            if m:
                admitted.add(m.group(1))
                sorry_pending = False
    return [name for name in PURE_BUILTINS if name in admitted]


def _admitted_qualifier(admitted: list[str]) -> str:
    """Return a parenthetical qualifier for sorry-dependent lemmas, or empty string."""
    if not admitted:
        return ""
    n = len(admitted)
    proven = len(PURE_BUILTINS) - n
    return f" ({proven} fully proven, {n} with sorry-dependent core equivalences)"


def expected_snippets(
    universal: list[str], remaining: list[str], *, admitted: list[str] | None = None,
) -> dict[str, list[str]]:
    count = len(universal)
    universal_codes = code_list(universal)
    remaining_codes = code_list(remaining)
    qualifier = _admitted_qualifier(admitted or [])

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
    total = len(PURE_BUILTINS)
    arithmetic_summary = (
        f"{total}/{total} pure EVMYulLean-backed builtins have universal bridge lemmas{qualifier}."
        if not remaining
        else (
            f"{count}/{total} pure EVMYulLean-backed builtins have universal bridge lemmas; {remaining_codes} still relies on concrete smoke tests."
            if len(remaining) == 1
            else f"{count}/{total} pure EVMYulLean-backed builtins have universal bridge lemmas; {plain_code_subject(remaining)} still rely on concrete smoke tests."
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
        "TRUST_ASSUMPTIONS": [
            f"{count} universal pure bridge theorems{qualifier}",
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

    lemma_text = BRIDGE_LEMMAS.read_text(encoding="utf-8")
    universal = extract_universal_builtins(lemma_text)
    remaining = [name for name in PURE_BUILTINS if name not in universal]
    admitted = extract_admitted_builtins(lemma_text)
    expected = expected_snippets(universal, remaining, admitted=admitted)

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

    admitted_str = f"; admitted (sorry-dependent): {', '.join(admitted)}" if admitted else ""
    print(
        "bridge coverage sync passed: "
        f"{len(universal)}/{len(PURE_BUILTINS)} pure builtins universally bridged; "
        f"remaining concrete-only: {', '.join(remaining) if remaining else 'none'}"
        f"{admitted_str}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
