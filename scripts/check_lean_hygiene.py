#!/usr/bin/env python3
"""Check for Lean code hygiene issues.

Validates:
1. No #eval in Compiler/Proofs/ files (debug commands slow builds)
2. Exactly 1 allowUnsafeReducibility (documented trust assumption)

Usage:
    python3 scripts/check_lean_hygiene.py
"""

from __future__ import annotations

from pathlib import Path

from property_utils import die, report_errors

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    errors: list[str] = []

    # Check 1: No #eval in proof files
    proof_dirs = [ROOT / "Compiler" / "Proofs"]
    for proof_dir in proof_dirs:
        for lean_file in proof_dir.rglob("*.lean"):
            rel = lean_file.relative_to(ROOT)
            for i, line in enumerate(lean_file.read_text().splitlines(), 1):
                stripped = line.lstrip()
                if stripped.startswith("#eval ") or stripped == "#eval":
                    errors.append(
                        f"{rel}:{i}: found #eval in proof file "
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

    report_errors(errors, "Lean hygiene check failed")
    print(
        f"Lean hygiene check passed "
        f"(0 #eval in proofs, {unsafe_count} allowUnsafeReducibility)."
    )


if __name__ == "__main__":
    main()
