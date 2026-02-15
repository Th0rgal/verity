#!/usr/bin/env python3
"""Check that AXIOMS.md references correct line numbers for axiom declarations.

Parses AXIOMS.md for location patterns like `File.lean:NN` and verifies each
axiom actually appears at the claimed line number in the source file.

Usage:
    python3 scripts/check_axiom_locations.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    axioms_md = ROOT / "AXIOMS.md"
    if not axioms_md.exists():
        print("AXIOMS.md not found", file=sys.stderr)
        raise SystemExit(1)

    text = axioms_md.read_text(encoding="utf-8")

    # Match patterns like: ### N. `axiom_name`
    # followed by **Location**: `path/to/File.lean:NN`
    axiom_blocks = re.findall(
        r"### \d+\.\s+`(\w+)`\s*\n\n"
        r"\*\*Location\*\*:\s*`([^:]+):(\d+)`",
        text,
    )

    if not axiom_blocks:
        print("No axiom location entries found in AXIOMS.md", file=sys.stderr)
        raise SystemExit(1)

    errors: list[str] = []
    checked = 0

    for axiom_name, rel_path, claimed_line_str in axiom_blocks:
        claimed_line = int(claimed_line_str)
        source_file = ROOT / rel_path

        if not source_file.exists():
            errors.append(f"{axiom_name}: file {rel_path} not found")
            continue

        lines = source_file.read_text(encoding="utf-8").splitlines()

        # Find actual line number for this axiom
        actual_line = None
        for i, line in enumerate(lines, 1):
            if re.match(rf"^axiom\s+{re.escape(axiom_name)}\b", line):
                actual_line = i
                break

        if actual_line is None:
            errors.append(
                f"{axiom_name}: not found in {rel_path} "
                f"(AXIOMS.md claims line {claimed_line})"
            )
        elif actual_line != claimed_line:
            errors.append(
                f"{axiom_name}: AXIOMS.md says line {claimed_line} "
                f"but actually at line {actual_line} in {rel_path}"
            )
        else:
            print(f"  OK {axiom_name} at {rel_path}:{actual_line}")
            checked += 1

    if errors:
        print("\nAxiom location check FAILED:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        raise SystemExit(1)

    print(f"\nOK: All {checked} axiom locations in AXIOMS.md are accurate")


if __name__ == "__main__":
    main()
