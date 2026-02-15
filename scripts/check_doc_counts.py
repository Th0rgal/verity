#!/usr/bin/env python3
"""Check that documentation files have accurate theorem/test/axiom counts.

Validates counts in README.md, VERIFICATION_STATUS.md, llms.txt, and other
documentation against the actual property manifest and codebase.

Usage:
    python3 scripts/check_doc_counts.py
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def get_manifest_counts() -> tuple[int, int, dict[str, int]]:
    """Return (total_theorems, num_categories, per_contract_counts)."""
    manifest = ROOT / "test" / "property_manifest.json"
    data = json.loads(manifest.read_text(encoding="utf-8"))
    per_contract = {k: len(v) for k, v in data.items()}
    total = sum(per_contract.values())
    return total, len(data), per_contract


def get_axiom_count() -> int:
    """Count axiom declarations in Lean files."""
    count = 0
    for d in [ROOT / "Compiler", ROOT / "DumbContracts"]:
        if not d.exists():
            continue
        for lean in d.rglob("*.lean"):
            text = lean.read_text(encoding="utf-8")
            for line in text.splitlines():
                if re.match(r"^axiom\s+", line):
                    count += 1
    return count


def check_file(path: Path, checks: list[tuple[str, re.Pattern, str]]) -> list[str]:
    """Check a file for expected patterns. Returns list of errors."""
    if not path.exists():
        return [f"{path.name}: file not found"]
    text = path.read_text(encoding="utf-8")
    errors = []
    for desc, pattern, expected in checks:
        match = pattern.search(text)
        if not match:
            errors.append(f"{path.name}: missing expected pattern for {desc}")
        elif match.group(1) != expected:
            errors.append(
                f"{path.name}: {desc} says '{match.group(1)}' but expected '{expected}'"
            )
    return errors


def main() -> None:
    total_theorems, num_categories, _ = get_manifest_counts()
    axiom_count = get_axiom_count()

    errors: list[str] = []

    # Check README.md
    readme = ROOT / "README.md"
    errors.extend(
        check_file(
            readme,
            [
                (
                    "theorem count",
                    re.compile(r"(\d+) theorems across"),
                    str(total_theorems),
                ),
                (
                    "category count",
                    re.compile(r"theorems across (\d+) categor"),
                    str(num_categories),
                ),
                (
                    "axiom count in What's Verified",
                    re.compile(r"verified with (\d+) axioms"),
                    str(axiom_count),
                ),
            ],
        )
    )

    # Check llms.txt
    llms = ROOT / "docs-site" / "public" / "llms.txt"
    errors.extend(
        check_file(
            llms,
            [
                (
                    "theorem count",
                    re.compile(r"\*\*Theorems\*\*: (\d+) across"),
                    str(total_theorems),
                ),
                (
                    "category count",
                    re.compile(r"Theorems\*\*: \d+ across (\d+) categor"),
                    str(num_categories),
                ),
            ],
        )
    )

    # Check TRUST_ASSUMPTIONS.md
    trust = ROOT / "TRUST_ASSUMPTIONS.md"
    errors.extend(
        check_file(
            trust,
            [
                (
                    "axiom count in verification chain",
                    re.compile(r"FULLY VERIFIED, (\d+) axioms"),
                    str(axiom_count),
                ),
            ],
        )
    )

    if errors:
        print("Documentation count check FAILED:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        print("", file=sys.stderr)
        print(
            f"Actual counts: {total_theorems} theorems, "
            f"{num_categories} categories, {axiom_count} axioms",
            file=sys.stderr,
        )
        raise SystemExit(1)

    print(
        f"Documentation count check passed "
        f"({total_theorems} theorems, {num_categories} categories, "
        f"{axiom_count} axioms)."
    )


if __name__ == "__main__":
    main()
