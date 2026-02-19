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

from property_utils import ROOT, die, report_errors


def main() -> None:
    errors: list[str] = []

    # Check 1: No debug commands in proof files
    debug_commands = ["#eval", "#check", "#print", "#reduce"]
    proof_dirs = [ROOT / "Compiler" / "Proofs", ROOT / "Verity" / "Proofs"]
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            for i, line in enumerate(lean_file.read_text().splitlines(), 1):
                stripped = line.lstrip()
                if stripped.startswith("--"):
                    continue
                for cmd in debug_commands:
                    if stripped.startswith(cmd + " ") or stripped == cmd:
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
        for i, line in enumerate(lean_file.read_text().splitlines(), 1):
            if "allowUnsafeReducibility" in line and not line.lstrip().startswith("--"):
                unsafe_count += 1
                unsafe_locations.append(f"{rel}:{i}")

    if unsafe_count != expected_unsafe:
        errors.append(
            f"Expected {expected_unsafe} allowUnsafeReducibility, "
            f"found {unsafe_count}: {unsafe_locations}"
        )

    # Check 3: No sorry in any Lean file (global proof completeness)
    # Track block comment nesting to skip /- ... -/ and /-! ... -/ comments.
    sorry_re = re.compile(r"\bsorry\b")
    sorry_count = 0
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        block_depth = 0
        for i, line in enumerate(lean_file.read_text().splitlines(), 1):
            # Update block comment depth
            j = 0
            code_parts: list[str] = []
            line_len = len(line)
            while j < line_len:
                if block_depth > 0:
                    if j + 1 < line_len and line[j] == "-" and line[j + 1] == "/":
                        block_depth -= 1
                        j += 2
                    elif j + 1 < line_len and line[j] == "/" and line[j + 1] == "-":
                        block_depth += 1
                        j += 2
                    else:
                        j += 1
                else:
                    if j + 1 < line_len and line[j] == "/" and line[j + 1] == "-":
                        block_depth += 1
                        j += 2
                    else:
                        code_parts.append(line[j])
                        j += 1
            code = "".join(code_parts)
            # Skip line comments
            comment_idx = code.find("--")
            if comment_idx >= 0:
                code = code[:comment_idx]
            # Remove string literals
            code = re.sub(r'"[^"]*"', '', code)
            if sorry_re.search(code):
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
            for i, line in enumerate(lean_file.read_text().splitlines(), 1):
                stripped = line.lstrip()
                if stripped.startswith("--"):
                    continue
                if "native_decide" in stripped:
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
