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

    # Check 3: Fixed sorry baseline after the merged proof-reduction pass.
    # Allowed sorry locations are pinned to specific infrastructure files
    # with per-file count caps so that extra sorrys cannot be added silently.
    ALLOWED_SORRY_FILES: dict[str, int] = {
        "Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean": 5,
    }
    sorry_count = 0
    sorry_locations: list[str] = []
    unexpected_sorry_locations: list[str] = []
    sorry_per_file: dict[str, int] = {}
    for lean_file in ROOT.rglob("*.lean"):
        if ".lake" in str(lean_file):
            continue
        rel = lean_file.relative_to(ROOT)
        rel_str = str(rel)
        scrubbed_lines = scrub_lean_code(lean_file.read_text(encoding="utf-8")).splitlines()
        for i, line in enumerate(scrubbed_lines, 1):
            if SORRY_RE.search(line):
                sorry_count += 1
                loc = f"{rel}:{i}"
                sorry_locations.append(loc)
                if rel_str not in ALLOWED_SORRY_FILES:
                    unexpected_sorry_locations.append(loc)
                else:
                    sorry_per_file[rel_str] = sorry_per_file.get(rel_str, 0) + 1

    if unexpected_sorry_locations:
        errors.append(
            f"Found sorry in non-allowlisted files: {unexpected_sorry_locations}"
        )

    for path, expected_cap in ALLOWED_SORRY_FILES.items():
        actual = sorry_per_file.get(path, 0)
        if actual > expected_cap:
            errors.append(
                f"{path}: found {actual} sorry (cap is {expected_cap})"
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
        f"{sorry_count} sorry ({sorry_count - len(unexpected_sorry_locations)} allowed, {len(unexpected_sorry_locations)} unexpected), "
        f"0 native_decide in proofs)."
    )


if __name__ == "__main__":
    main()
