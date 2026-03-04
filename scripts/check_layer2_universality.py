#!/usr/bin/env python3
"""Enforce universal sender/storage quantification in Layer-2 bridge theorems.

Guards against regressions from Issue #1103 where Layer-2 proofs were written for
fixed test values (e.g., concrete sender or empty initial storage) instead of
universally quantifying over inputs.

Checks:
1. Every `*_semantic_bridge` theorem in `Compiler/Proofs/SemanticBridge.lean`
   quantifies both `(state : ContractState)` and `(sender : Address)`.
2. Legacy fixed-value anti-patterns are absent from the Layer-2 bridge file.

Usage:
    python3 scripts/check_layer2_universality.py
"""

from __future__ import annotations

import re

from property_utils import ROOT, report_errors, strip_lean_comments

TARGET = ROOT / "Compiler" / "Proofs" / "SemanticBridge.lean"

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma)\s+(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
)
STATE_PARAM_RE = re.compile(r"\(\s*state\s*:\s*ContractState\s*\)")
SENDER_PARAM_RE = re.compile(r"\(\s*sender\s*:\s*Address\s*\)")

LEGACY_ANTI_PATTERNS: tuple[tuple[str, str], ...] = (
    ("SpecStorage.empty", "fixed empty initial storage"),
    ("test_sender", "fixed concrete sender"),
    ("let initialStorage :=", "local fixed-storage theorem pattern"),
)


def _collect_semantic_bridge_headers(lines: list[str]) -> list[tuple[str, int, str]]:
    """Return `(name, start_line_1indexed, header_text)` for bridge theorems."""
    out: list[tuple[str, int, str]] = []
    i = 0
    while i < len(lines):
        match = THEOREM_RE.match(lines[i])
        if match is None:
            i += 1
            continue

        name = match.group("name")
        if not name.endswith("_semantic_bridge"):
            i += 1
            continue

        start = i
        header_lines = [lines[i]]
        i += 1
        while i < len(lines):
            header_lines.append(lines[i])
            if re.search(r":\s*$", lines[i]):
                break
            i += 1

        out.append((name, start + 1, "\n".join(header_lines)))
        i += 1

    return out


def main() -> None:
    errors: list[str] = []

    text = strip_lean_comments(TARGET.read_text(encoding="utf-8"))
    lines = text.splitlines()

    theorem_headers = _collect_semantic_bridge_headers(lines)
    if not theorem_headers:
        errors.append(
            f"{TARGET.relative_to(ROOT)}: no *_semantic_bridge theorem headers found"
        )

    for name, line_no, header in theorem_headers:
        if STATE_PARAM_RE.search(header) is None:
            errors.append(
                f"{TARGET.relative_to(ROOT)}:{line_no}: {name} is missing "
                "`(state : ContractState)` quantification"
            )
        if SENDER_PARAM_RE.search(header) is None:
            errors.append(
                f"{TARGET.relative_to(ROOT)}:{line_no}: {name} is missing "
                "`(sender : Address)` quantification"
            )

    for needle, reason in LEGACY_ANTI_PATTERNS:
        for idx, line in enumerate(lines, 1):
            if needle in line:
                errors.append(
                    f"{TARGET.relative_to(ROOT)}:{idx}: found `{needle}` "
                    f"(legacy non-universal pattern: {reason})"
                )

    report_errors(errors, "Layer-2 universality check failed")
    print(
        "Layer-2 universality check passed "
        f"({len(theorem_headers)} semantic bridge theorem headers validated)."
    )


if __name__ == "__main__":
    main()
