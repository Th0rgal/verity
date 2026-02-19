#!/usr/bin/env python3
"""Check for Lean code hygiene issues.

Validates:
1. No debug commands (#eval, #check, #print, #reduce) in proof files
2. Exactly 1 allowUnsafeReducibility (documented trust assumption)
3. No sorry in any Lean files (proof completeness)
4. No native_decide in proof files outside smoke tests (kernel bypass)

Usage:
    python3 scripts/check_lean_hygiene.py
"""

from __future__ import annotations

import re

from property_utils import ROOT, report_errors, strip_lean_comments

SORRY_RE = re.compile(r"\bsorry\b")


def scrub_lean_code(text: str) -> str:
    """Remove comments and string literal contents from Lean source text."""
    return _strip_lean_strings(strip_lean_comments(text))


def _strip_lean_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    in_string = False
    raw_hashes: int | None = None

    while i < n:
        ch = text[i]

        if raw_hashes is not None:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == '"':
                j = i + 1
                hashes = 0
                while j < n and text[j] == "#" and hashes < raw_hashes:
                    hashes += 1
                    j += 1
                if hashes == raw_hashes:
                    out.append('"')
                    out.extend("#" * hashes)
                    i = j
                    raw_hashes = None
                    continue
            out.append(" ")
            i += 1
            continue

        if in_string:
            if ch == "\n":
                out.append("\n")
                i += 1
                continue
            if ch == "\\" and i + 1 < n:
                out.extend([" ", " "])
                i += 2
                continue
            if ch == '"':
                out.append('"')
                in_string = False
                i += 1
                continue
            out.append(" ")
            i += 1
            continue

        if ch == '"':
            out.append('"')
            in_string = True
            i += 1
            continue

        if ch == "r":
            j = i + 1
            hashes = 0
            while j < n and text[j] == "#":
                hashes += 1
                j += 1
            if j < n and text[j] == '"':
                out.append("r")
                out.extend("#" * hashes)
                out.append('"')
                i = j + 1
                raw_hashes = hashes
                continue

        out.append(ch)
        i += 1

    return "".join(out)


def line_starts_with_command(line: str, cmd: str) -> bool:
    stripped = line.lstrip()
    return stripped == cmd or stripped.startswith(cmd + " ")


def main() -> None:
    errors: list[str] = []

    # Check 1: No debug commands in proof files
    debug_commands = ["#eval", "#check", "#print", "#reduce"]
    proof_dirs = [ROOT / "Compiler" / "Proofs", ROOT / "Verity" / "Proofs"]
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                for cmd in debug_commands:
                    if line_starts_with_command(line, cmd):
                        errors.append(
                            f"{rel}:{i}: found {cmd} in proof file "
                            f"(debug command that slows builds)"
                        )

    # Check 2: Exactly 1 allowUnsafeReducibility
    expected_unsafe = 1
    unsafe_count = 0
    unsafe_locations: list[str] = []
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if "allowUnsafeReducibility" in line:
                unsafe_count += 1
                unsafe_locations.append(f"{rel}:{i}")

    if unsafe_count != expected_unsafe:
        errors.append(
            f"Expected {expected_unsafe} allowUnsafeReducibility, "
            f"found {unsafe_count}: {unsafe_locations}"
        )

    # Check 3: No sorry in any Lean file (global proof completeness)
    sorry_count = 0
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if SORRY_RE.search(line):
                sorry_count += 1
                errors.append(f"{rel}:{i}: found sorry (incomplete proof)")

    # Check 4: No native_decide in proof files (except smoke tests)
    # native_decide bypasses the kernel and is acceptable only in smoke tests
    # that check generated code strings, not in mathematical proofs.
    native_decide_count = 0
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            # Smoke tests legitimately use native_decide for string comparisons
            if "SmokeTest" in lean_file.name:
                continue
            scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
            for i, line in enumerate(scrubbed_lines, 1):
                if "native_decide" in line:
                    native_decide_count += 1
                    errors.append(
                        f"{rel}:{i}: found native_decide in proof file "
                        f"(bypasses kernel — use decide or other tactics)"
                    )

    report_errors(errors, "Lean hygiene check failed")
    print(
        f"Lean hygiene check passed "
        f"(0 debug commands in proofs, {unsafe_count} allowUnsafeReducibility, "
        f"0 sorry, 0 native_decide in proofs)."
    )


if __name__ == "__main__":
    main()
