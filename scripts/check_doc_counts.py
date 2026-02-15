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
    for d in [ROOT / "Compiler", ROOT / "Verity"]:
        if not d.exists():
            continue
        for lean in d.rglob("*.lean"):
            text = lean.read_text(encoding="utf-8")
            for line in text.splitlines():
                if re.match(r"^axiom\s+", line):
                    count += 1
    return count


def get_test_counts() -> tuple[int, int]:
    """Count test functions and test suite files."""
    test_dir = ROOT / "test"
    suite_count = len(list(test_dir.glob("*.t.sol")))
    test_count = 0
    for sol in test_dir.glob("*.t.sol"):
        text = sol.read_text(encoding="utf-8")
        test_count += len(re.findall(r"function\s+test", text))
    return test_count, suite_count


def get_core_line_count() -> int:
    """Count lines in Verity/Core.lean."""
    core = ROOT / "Verity" / "Core.lean"
    return len(core.read_text(encoding="utf-8").splitlines())


def get_sorry_count() -> int:
    """Count sorry statements in Lean proof files."""
    count = 0
    for d in [ROOT / "Compiler", ROOT / "Verity"]:
        if not d.exists():
            continue
        for lean in d.rglob("*.lean"):
            text = lean.read_text(encoding="utf-8")
            for line in text.splitlines():
                if re.match(r"^\s*sorry\b", line):
                    count += 1
    return count


def get_exclusion_count() -> int:
    """Count total property exclusions from property_exclusions.json."""
    exclusions = ROOT / "test" / "property_exclusions.json"
    if not exclusions.exists():
        return 0
    data = json.loads(exclusions.read_text(encoding="utf-8"))
    return sum(len(v) for v in data.values())


def get_covered_count(total_theorems: int) -> tuple[int, int]:
    """Compute covered property count and coverage percentage.

    Returns (covered_count, coverage_percent).
    """
    sys.path.insert(0, str(ROOT / "scripts"))
    from property_utils import collect_covered

    covered = collect_covered()
    covered_count = sum(len(v) for v in covered.values())
    pct = round(covered_count * 100 / total_theorems) if total_theorems else 0
    return covered_count, pct


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
    test_count, suite_count = get_test_counts()
    core_lines = get_core_line_count()
    sorry_count = get_sorry_count()
    exclusion_count = get_exclusion_count()
    covered_count, coverage_pct = get_covered_count(total_theorems)
    proven_count = total_theorems - sorry_count

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
                (
                    "test count",
                    re.compile(r"(\d+) Foundry tests across"),
                    str(test_count),
                ),
                (
                    "test suite count",
                    re.compile(r"Foundry tests across (\d+) test suites"),
                    str(suite_count),
                ),
                (
                    "covered count",
                    re.compile(r"(\d+) covered by property tests"),
                    str(covered_count),
                ),
                (
                    "coverage percentage",
                    re.compile(r"(\d+)% coverage"),
                    str(coverage_pct),
                ),
                (
                    "exclusion count",
                    re.compile(r"(\d+) proof-only exclusions"),
                    str(exclusion_count),
                ),
                (
                    "sorry count",
                    re.compile(r"(\d+) `sorry`"),
                    str(sorry_count),
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
                (
                    "test count",
                    re.compile(r"\*\*Tests\*\*: (\d+) Foundry"),
                    str(test_count),
                ),
                (
                    "proven count",
                    re.compile(r"(\d+) fully proven"),
                    str(proven_count),
                ),
                (
                    "sorry count",
                    re.compile(r"(\d+) `sorry` placeholders"),
                    str(sorry_count),
                ),
            ],
        )
    )

    # Check compiler.mdx
    compiler_mdx = ROOT / "docs-site" / "content" / "compiler.mdx"
    errors.extend(
        check_file(
            compiler_mdx,
            [
                (
                    "theorem count",
                    re.compile(r"(\d+) EDSL theorems"),
                    str(total_theorems),
                ),
                (
                    "theorem count in links",
                    re.compile(r"Verification.+ — (\d+) proven theorems"),
                    str(total_theorems),
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

    # Check core size claims
    core_mdx = ROOT / "docs-site" / "content" / "core.mdx"
    errors.extend(
        check_file(
            core_mdx,
            [
                (
                    "core line count",
                    re.compile(r"the (\d+)-line core"),
                    str(core_lines),
                ),
            ],
        )
    )
    index_mdx = ROOT / "docs-site" / "content" / "index.mdx"
    errors.extend(
        check_file(
            index_mdx,
            [
                (
                    "core line count",
                    re.compile(r"the (\d+)-line EDSL"),
                    str(core_lines),
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
            f"{num_categories} categories, {axiom_count} axioms, "
            f"{test_count} tests, {suite_count} suites, "
            f"{sorry_count} sorry, {proven_count} proven, "
            f"{covered_count} covered ({coverage_pct}%), "
            f"{exclusion_count} exclusions",
            file=sys.stderr,
        )
        raise SystemExit(1)

    print(
        f"Documentation count check passed "
        f"({total_theorems} theorems, {num_categories} categories, "
        f"{axiom_count} axioms, {test_count} tests, {suite_count} suites, "
        f"{sorry_count} sorry, {covered_count}/{total_theorems} covered)."
    )


if __name__ == "__main__":
    main()
