#!/usr/bin/env python3
"""Check that documentation files have accurate theorem/test/axiom counts.

Validates counts in README.md, test/README.md, docs/VERIFICATION_STATUS.md,
docs/ROADMAP.md, TRUST_ASSUMPTIONS.md, docs-site llms.txt, compiler.mdx,
verification.mdx, research.mdx, core.mdx, and index.mdx against the actual
property manifest and codebase.

Usage:
    python3 scripts/check_doc_counts.py
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

from property_utils import collect_covered

ROOT = Path(__file__).resolve().parents[1]


def get_manifest_counts() -> tuple[int, int, dict[str, int]]:
    """Return (total_theorems, num_categories, per_contract_counts)."""
    manifest = ROOT / "test" / "property_manifest.json"
    data = json.loads(manifest.read_text(encoding="utf-8"))
    per_contract = {k: len(v) for k, v in data.items()}
    total = sum(per_contract.values())
    return total, len(data), per_contract


def _count_lean_lines(pattern: str) -> int:
    """Count lines matching *pattern* across all Lean files in Compiler/ and Verity/."""
    count = 0
    for d in [ROOT / "Compiler", ROOT / "Verity"]:
        if not d.exists():
            continue
        for lean in d.rglob("*.lean"):
            text = lean.read_text(encoding="utf-8")
            for line in text.splitlines():
                if re.match(pattern, line):
                    count += 1
    return count


def get_axiom_count() -> int:
    """Count axiom declarations in Lean files."""
    return _count_lean_lines(r"^axiom\s+")


def get_test_counts() -> tuple[int, int]:
    """Count test functions and test suite files (recursive, includes test/yul/)."""
    test_dir = ROOT / "test"
    suite_count = len(list(test_dir.rglob("*.t.sol")))
    test_count = 0
    for sol in test_dir.rglob("*.t.sol"):
        text = sol.read_text(encoding="utf-8")
        test_count += len(re.findall(r"function\s+test", text))
    return test_count, suite_count


def get_core_line_count() -> int:
    """Count lines in Verity/Core.lean."""
    core = ROOT / "Verity" / "Core.lean"
    return len(core.read_text(encoding="utf-8").splitlines())


def get_sorry_count() -> int:
    """Count sorry statements in Lean proof files."""
    return _count_lean_lines(r"^\s*(·\s*)?sorry\b")


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


def check_verification_theorem_names(path: Path) -> list[str]:
    """Validate backtick-quoted theorem names in verification.mdx tables.

    Parses each ``### ContractName`` section, extracts theorem names from
    table rows (``| N | `theorem_name` | ...``), and checks:
    1. Each table name exists in the property manifest (forward check).
    2. Each manifest theorem appears in the tables (reverse completeness check).
       Skipped for Stdlib (only Math subsection tabled) and contracts without
       a ``###`` section (e.g. ReentrancyExample).
    """
    if not path.exists():
        return []
    text = path.read_text(encoding="utf-8")
    manifest = json.loads(
        (ROOT / "test" / "property_manifest.json").read_text(encoding="utf-8")
    )
    errors: list[str] = []

    # Map verification.mdx section headers to manifest contract names
    section_to_contract = {
        "Stdlib/Math": "Stdlib",
    }
    # Contracts where only a subset of manifest theorems are tabled
    partial_contracts = {"Stdlib"}

    # Split into sections by ### headers
    section_pat = re.compile(r"^### (.+)$", re.MULTILINE)
    sections = list(section_pat.finditer(text))
    for i, match in enumerate(sections):
        section_name = match.group(1).strip()
        contract = section_to_contract.get(section_name, section_name)
        if contract not in manifest:
            continue

        # Get section text (from this header to next header or end)
        start = match.end()
        end = sections[i + 1].start() if i + 1 < len(sections) else len(text)
        section_text = text[start:end]

        # Extract backtick-quoted theorem names from table rows
        theorem_pat = re.compile(r"^\|\s*\d+\s*\|\s*`([^`]+)`", re.MULTILINE)
        table_names = set()
        manifest_names = set(manifest[contract])
        for m in theorem_pat.finditer(section_text):
            name = m.group(1)
            table_names.add(name)
            if name not in manifest_names:
                errors.append(
                    f"verification.mdx: `{name}` in {section_name} table "
                    f"not found in property manifest for {contract}"
                )

        # Reverse check: manifest theorems missing from tables
        if contract not in partial_contracts:
            missing = sorted(manifest_names - table_names)
            if missing:
                errors.append(
                    f"verification.mdx: {contract} section missing "
                    f"{len(missing)} manifest theorem(s): "
                    + ", ".join(f"`{n}`" for n in missing[:5])
                    + ("..." if len(missing) > 5 else "")
                )

    return errors


def main() -> None:
    total_theorems, num_categories, per_contract = get_manifest_counts()
    axiom_count = get_axiom_count()
    test_count, suite_count = get_test_counts()
    core_lines = get_core_line_count()
    sorry_count = get_sorry_count()
    exclusion_count = get_exclusion_count()
    covered_count, coverage_pct = get_covered_count(total_theorems)
    proven_count = total_theorems - sorry_count
    stdlib_count = per_contract.get("Stdlib", 0)
    non_stdlib_total = total_theorems - stdlib_count

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
                (
                    "inline theorem count",
                    re.compile(r"Verifies all (\d+) theorems"),
                    str(total_theorems),
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
                (
                    "core line count",
                    re.compile(r"\*\*Core Size\*\*: (\d+) lines"),
                    str(core_lines),
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
                (
                    "expected test count",
                    re.compile(r"Expected: (\d+)/\d+ tests pass"),
                    str(test_count),
                ),
                (
                    "Foundry test count",
                    re.compile(r"\*\*Foundry Tests\*\*: (\d+)/"),
                    str(test_count),
                ),
                (
                    "test suite count",
                    re.compile(r"Ran (\d+) test suites:"),
                    str(suite_count),
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

    # Check test/README.md
    test_readme = ROOT / "test" / "README.md"
    errors.extend(
        check_file(
            test_readme,
            [
                (
                    "covered count",
                    re.compile(r"(\d+)/\d+ theorems tested"),
                    str(covered_count),
                ),
                (
                    "theorem count",
                    re.compile(r"\d+/(\d+) theorems tested"),
                    str(total_theorems),
                ),
                (
                    "coverage percentage",
                    re.compile(r"theorems tested \((\d+)%\)"),
                    str(coverage_pct),
                ),
                (
                    "exclusion count",
                    re.compile(r"(\d+) proof-only exclusions"),
                    str(exclusion_count),
                ),
                (
                    "property test coverage in tree",
                    re.compile(r"covering (\d+)/\d+ theorems"),
                    str(covered_count),
                ),
            ],
        )
    )

    # Check docs/VERIFICATION_STATUS.md
    verification_status = ROOT / "docs" / "VERIFICATION_STATUS.md"
    errors.extend(
        check_file(
            verification_status,
            [
                (
                    "non-stdlib total",
                    re.compile(r"\*\*Total\*\* \| \*\*(\d+)\*\*"),
                    str(non_stdlib_total),
                ),
                (
                    "stdlib count in note",
                    re.compile(r"Stdlib \((\d+) internal"),
                    str(stdlib_count),
                ),
                (
                    "total properties in note",
                    re.compile(r"(\d+) total properties"),
                    str(total_theorems),
                ),
                (
                    "coverage percentage",
                    re.compile(r"(\d+)% coverage"),
                    str(coverage_pct),
                ),
                (
                    "covered/total in status",
                    re.compile(r"coverage \((\d+)/"),
                    str(covered_count),
                ),
                (
                    "total in coverage status",
                    re.compile(r"coverage \(\d+/(\d+)\)"),
                    str(total_theorems),
                ),
                (
                    "exclusion count in status",
                    re.compile(r"(\d+) remaining exclusions"),
                    str(exclusion_count),
                ),
                (
                    "total properties field",
                    re.compile(r"Total Properties\*\*: (\d+)"),
                    str(total_theorems),
                ),
                (
                    "excluded count",
                    re.compile(r"Excluded\*\*: (\d+)"),
                    str(exclusion_count),
                ),
                (
                    "stdlib coverage",
                    re.compile(r"Stdlib \| 0% \(0/(\d+)\)"),
                    str(stdlib_count),
                ),
                (
                    "stdlib exclusions",
                    re.compile(r"Stdlib \| 0% \(0/\d+\) \| (\d+) proof-only"),
                    str(stdlib_count),
                ),
                (
                    "exclusion header count",
                    re.compile(r"Proof-Only Properties \((\d+) exclusions\)"),
                    str(exclusion_count),
                ),
                (
                    "sorry count",
                    re.compile(r"(\d+) `sorry` remaining"),
                    str(sorry_count),
                ),
            ],
        )
    )

    # Check docs/ROADMAP.md
    roadmap = ROOT / "docs" / "ROADMAP.md"
    errors.extend(
        check_file(
            roadmap,
            [
                (
                    "coverage percentage",
                    re.compile(r"Property Testing\*\*: (\d+)% coverage"),
                    str(coverage_pct),
                ),
                (
                    "covered count",
                    re.compile(r"Property Testing\*\*: \d+% coverage \((\d+)/"),
                    str(covered_count),
                ),
                (
                    "total in coverage",
                    re.compile(r"Property Testing\*\*: \d+% coverage \(\d+/(\d+)\)"),
                    str(total_theorems),
                ),
            ],
        )
    )

    # Check verification.mdx
    verification_mdx = ROOT / "docs-site" / "content" / "verification.mdx"
    verification_checks = [
        (
            "theorem count in Status",
            re.compile(r"\*\*Status\*\*: (\d+) theorems across"),
            str(total_theorems),
        ),
        (
            "category count in Status",
            re.compile(r"\*\*Status\*\*: \d+ theorems across (\d+) categor"),
            str(num_categories),
        ),
        (
            "theorem count in Snapshot",
            re.compile(r"EDSL theorems: (\d+) across"),
            str(total_theorems),
        ),
        (
            "category count in Snapshot",
            re.compile(r"EDSL theorems: \d+ across (\d+) categor"),
            str(num_categories),
        ),
        (
            "Stdlib count",
            re.compile(r"Stdlib: (\d+) theorems"),
            str(stdlib_count),
        ),
    ]
    # Add per-contract total checks
    for contract, count in per_contract.items():
        if contract == "Stdlib":
            continue  # Handled separately above
        verification_checks.append((
            f"{contract} total",
            re.compile(rf"- {contract}: (\d+) total"),
            str(count),
        ))
    errors.extend(check_file(verification_mdx, verification_checks))

    # Validate theorem names in verification.mdx tables against manifest
    errors.extend(
        check_verification_theorem_names(verification_mdx)
    )

    # Check research.mdx
    research_mdx = ROOT / "docs-site" / "content" / "research.mdx"
    errors.extend(
        check_file(
            research_mdx,
            [
                (
                    "test count in forge test comment",
                    re.compile(r"forge test\s+#\s*(\d+)/\d+ tests pass"),
                    str(test_count),
                ),
                (
                    "test count in metrics",
                    re.compile(r"Foundry tests pass \((\d+) as of"),
                    str(test_count),
                ),
                (
                    "test count in results",
                    re.compile(r"All Foundry tests passing \((\d+) as of"),
                    str(test_count),
                ),
            ],
        )
    )

    # Check theorem counts in getting-started.mdx
    getting_started = ROOT / "docs-site" / "content" / "getting-started.mdx"
    errors.extend(
        check_file(
            getting_started,
            [
                (
                    "theorem count",
                    re.compile(r"verifies all (\d+) theorems"),
                    str(total_theorems),
                ),
            ],
        )
    )

    # Check theorem count and test counts in index.mdx
    index_mdx = ROOT / "docs-site" / "content" / "index.mdx"
    errors.extend(
        check_file(
            index_mdx,
            [
                (
                    "theorem count",
                    re.compile(r"(\d+) machine-checked theorems"),
                    str(total_theorems),
                ),
                (
                    "test count",
                    re.compile(r"(\d+) Foundry tests across"),
                    str(test_count),
                ),
                (
                    "test suite count",
                    re.compile(r"Foundry tests across (\d+) suites"),
                    str(suite_count),
                ),
            ],
        )
    )

    # Check theorem count in research.mdx header
    errors.extend(
        check_file(
            research_mdx,
            [
                (
                    "theorem count in header",
                    re.compile(r"(\d+) theorems, all fully proven"),
                    str(total_theorems),
                ),
                (
                    "theorem count in metrics",
                    re.compile(r"(\d+) theorems as of"),
                    str(total_theorems),
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

    # Check layout.tsx banner (proven/total theorems proven)
    layout_tsx = ROOT / "docs-site" / "app" / "layout.tsx"
    errors.extend(
        check_file(
            layout_tsx,
            [
                (
                    "banner proven count",
                    re.compile(r"(\d+)/\d+ theorems proven"),
                    str(proven_count),
                ),
                (
                    "banner total count",
                    re.compile(r"\d+/(\d+) theorems proven"),
                    str(total_theorems),
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
