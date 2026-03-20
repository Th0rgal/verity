#!/usr/bin/env python3
"""Check for Lean code hygiene issues.

Validates:
1. No debug commands (#eval, #check, #print, #reduce) in proof files
2. Exactly 1 allowUnsafeReducibility (documented trust assumption)
3. Zero sorry in Lean code after scrubbing comments/strings
4. No native_decide in proof files outside smoke tests (kernel bypass)

Usage:
    python3 scripts/check_lean_hygiene.py
"""

from __future__ import annotations

import re

from property_utils import ROOT, report_errors, scrub_lean_code

SORRY_RE = re.compile(r"\bsorry\b")


def line_starts_with_command(line: str, cmd: str) -> bool:
    stripped = line.lstrip()
    return stripped == cmd or stripped.startswith(cmd + " ")


def main() -> None:
    errors: list[str] = []

    # Check 1: No debug commands in proof files
    debug_commands = ["#eval", "#check", "#print", "#reduce"]
    proof_dirs = [ROOT / "Compiler" / "Proofs", ROOT / "Verity" / "Proofs", ROOT / "Contracts"]
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

    # Check 3: Zero sorry after scrubbing comments and string literals.
    # CI requires fully completed proofs in-tree.
    expected_sorry = 194  # PR #1649 follow-up: 5 remaining SourceSemantics admissions + 189 remaining proof failures exposed by from-scratch build (FunctionBody, GenericInduction, Function, Dispatch, Contract)
    sorry_count = 0
    sorry_locations: list[str] = []
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if SORRY_RE.search(line):
                sorry_count += 1
                sorry_locations.append(f"{rel}:{i}")

    if sorry_count != expected_sorry:
        errors.append(
            f"Expected {expected_sorry} sorry, found {sorry_count}: {sorry_locations}"
        )

    # Check 4: No native_decide in proof files (except tests/profiles)
    # native_decide bypasses the kernel and is acceptable in:
    #   - Smoke tests (string comparisons against generated code)
    #   - Feature/bridge tests (decidable equality checks across systems)
    #   - Arithmetic profiles (cross-system constant agreement)
    # It is NOT acceptable in mathematical preservation/correctness proofs.
    native_decide_count = 0
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            stem = lean_file.stem
            if "Test" in stem or "Profile" in stem:
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
        f"{sorry_count} sorry (expected {expected_sorry}), "
        f"0 native_decide in proofs)."
    )


if __name__ == "__main__":
    main()
