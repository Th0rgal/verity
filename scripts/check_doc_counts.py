#!/usr/bin/env python3
"""Check that documentation files have accurate theorem/test/axiom counts.

Validates counts in README.md, test/README.md, docs/VERIFICATION_STATUS.md,
docs/ROADMAP.md, TRUST_ASSUMPTIONS.md, docs-site llms.txt, compiler.mdx,
verification.mdx, research.mdx, core.mdx, examples.mdx, index.mdx,
getting-started.mdx, and layout.tsx against the actual property manifest
and codebase. Also validates theorem counts in Property*.t.sol file headers
and AST equivalence theorem counts in Verity/AST/*.lean.

Usage:
    python3 scripts/check_doc_counts.py
"""

from __future__ import annotations

import json
import re
import sys
import argparse
from pathlib import Path
from typing import Any

from property_utils import ROOT, collect_covered


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


def get_property_test_function_count() -> int:
    """Count test functions in Property*.t.sol files only."""
    test_dir = ROOT / "test"
    count = 0
    for sol in sorted(test_dir.glob("Property*.t.sol")):
        text = sol.read_text(encoding="utf-8")
        count += len(re.findall(r"function\s+test", text))
    return count


def get_core_line_count() -> int:
    """Count lines in Verity/Core.lean."""
    core = ROOT / "Verity" / "Core.lean"
    return len(core.read_text(encoding="utf-8").splitlines())


def get_sorry_count() -> int:
    """Count sorry statements in Lean proof files."""
    return _count_lean_lines(r"^\s*(·\s*)?sorry\b")


def get_contract_count() -> int:
    """Count example contracts in Verity/Examples/."""
    examples_dir = ROOT / "Verity" / "Examples"
    return len(list(examples_dir.glob("*.lean")))


def get_ast_equiv_count() -> int:
    """Count public theorems in Verity/AST/*.lean (equivalence proofs)."""
    ast_dir = ROOT / "Verity" / "AST"
    count = 0
    for lean in ast_dir.glob("*.lean"):
        text = lean.read_text(encoding="utf-8")
        # Count public theorem declarations (not private)
        count += len(re.findall(r"^theorem\s+", text, re.MULTILINE))
    return count


def get_diff_test_total() -> int:
    """Compute total differential tests (10,000 per contract × number of contracts)."""
    test_dir = ROOT / "test"
    diff_count = len(list(test_dir.glob("Differential*.t.sol")))
    return diff_count * 10_000


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


def get_lean_toolchain() -> str:
    """Return pinned Lean toolchain string."""
    return (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()


def get_solc_version() -> str:
    """Return pinned solc version from foundry.toml."""
    text = (ROOT / "foundry.toml").read_text(encoding="utf-8")
    match = re.search(r'^solc_version\s*=\s*"([^"]+)"', text, re.MULTILINE)
    if not match:
        raise ValueError("foundry.toml: missing solc_version pin")
    return match.group(1)


def collect_metrics() -> dict[str, Any]:
    """Collect verification/doc metric values from source files."""
    total_theorems, num_categories, per_contract = get_manifest_counts()
    axiom_count = get_axiom_count()
    test_count, suite_count = get_test_counts()
    core_lines = get_core_line_count()
    sorry_count = get_sorry_count()
    exclusion_count = get_exclusion_count()
    covered_count, coverage_pct = get_covered_count(total_theorems)
    stdlib_count = per_contract.get("Stdlib", 0)

    return {
        "schema_version": 1,
        "theorems": {
            "total": total_theorems,
            "categories": num_categories,
            "per_contract": per_contract,
            "covered": covered_count,
            "coverage_percent": coverage_pct,
            "excluded": exclusion_count,
            "proven": total_theorems - sorry_count,
            "stdlib": stdlib_count,
            "non_stdlib_total": total_theorems - stdlib_count,
            "ast_equivalence": get_ast_equiv_count(),
        },
        "tests": {
            "foundry_functions": test_count,
            "suites": suite_count,
            "property_functions": get_property_test_function_count(),
            "differential_total": get_diff_test_total(),
        },
        "proofs": {
            "axioms": axiom_count,
            "sorry": sorry_count,
        },
        "codebase": {
            "core_lines": core_lines,
            "example_contracts": get_contract_count(),
        },
        "toolchain": {
            "lean": get_lean_toolchain(),
            "solc": get_solc_version(),
        },
    }


def load_metrics_from_artifact(path: Path) -> dict[str, Any]:
    """Load and minimally validate verification status artifact JSON."""
    if not path.exists():
        raise FileNotFoundError(f"{path}: verification status artifact not found")
    data = json.loads(path.read_text(encoding="utf-8"))
    required = ["theorems", "tests", "proofs", "codebase", "toolchain"]
    missing = [key for key in required if key not in data]
    if missing:
        raise ValueError(f"{path}: missing required keys: {', '.join(missing)}")
    return data


def check_property_test_headers(per_contract: dict[str, int]) -> list[str]:
    """Validate theorem counts in Property*.t.sol file headers against manifest."""
    test_dir = ROOT / "test"
    errors = []
    header_pat = re.compile(r"(\d+)\s+proven\s+theorems")
    for sol in sorted(test_dir.glob("Property*.t.sol")):
        name = sol.name.replace("Property", "").replace(".t.sol", "")
        if name not in per_contract:
            continue
        # Read just the header (first 500 chars is enough)
        text = sol.read_text(encoding="utf-8")[:500]
        match = header_pat.search(text)
        if not match:
            continue  # No standard header pattern — skip
        header_count = int(match.group(1))
        manifest_count = per_contract[name]
        if header_count != manifest_count:
            errors.append(
                f"Property{name}.t.sol: header says {header_count} proven theorems "
                f"but manifest has {manifest_count}"
            )
    return errors


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


def apply_fixes(path: Path, checks: list[tuple[str, re.Pattern, str]]) -> bool:
    """Apply in-place count fixes for all matched stale capture groups in path."""
    if not path.exists():
        return False
    text = path.read_text(encoding="utf-8")
    edits: list[tuple[int, int, str]] = []
    for _, pattern, expected in checks:
        match = pattern.search(text)
        if not match:
            continue
        if match.group(1) == expected:
            continue
        edits.append((match.start(1), match.end(1), expected))

    if not edits:
        return False

    # Apply right-to-left to preserve index validity.
    for start, stop, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[stop:]
    path.write_text(text, encoding="utf-8")
    return True


def check_and_maybe_fix(
    path: Path, checks: list[tuple[str, re.Pattern, str]], fix: bool
) -> list[str]:
    """Optionally apply fixes, then run checks."""
    if fix:
        apply_fixes(path, checks)
    return check_file(path, checks)


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
    parser = argparse.ArgumentParser(
        description="Check documentation count claims against manifest/code metrics."
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Auto-fix stale numeric counts in documentation files before validating.",
    )
    parser.add_argument(
        "--artifact",
        type=Path,
        default=ROOT / "artifacts" / "verification_status.json",
        help="Path to verification status artifact JSON.",
    )
    args = parser.parse_args()

    artifact_metrics = load_metrics_from_artifact(args.artifact)
    live_metrics = collect_metrics()
    if artifact_metrics != live_metrics:
        print(
            f"Verification status artifact is stale: {args.artifact}",
            file=sys.stderr,
        )
        print(
            "Run `python3 scripts/generate_verification_status.py` and commit the result.",
            file=sys.stderr,
        )
        raise SystemExit(1)

    theorem_metrics = artifact_metrics["theorems"]
    tests_metrics = artifact_metrics["tests"]
    proofs_metrics = artifact_metrics["proofs"]
    codebase_metrics = artifact_metrics["codebase"]
    total_theorems = int(theorem_metrics["total"])
    num_categories = int(theorem_metrics["categories"])
    per_contract = dict(theorem_metrics["per_contract"])
    covered_count = int(theorem_metrics["covered"])
    coverage_pct = int(theorem_metrics["coverage_percent"])
    exclusion_count = int(theorem_metrics["excluded"])
    proven_count = int(theorem_metrics["proven"])
    stdlib_count = int(theorem_metrics["stdlib"])
    non_stdlib_total = int(theorem_metrics["non_stdlib_total"])
    ast_equiv_count = int(theorem_metrics["ast_equivalence"])
    test_count = int(tests_metrics["foundry_functions"])
    suite_count = int(tests_metrics["suites"])
    property_fn_count = int(tests_metrics["property_functions"])
    diff_test_total = int(tests_metrics["differential_total"])
    axiom_count = int(proofs_metrics["axioms"])
    sorry_count = int(proofs_metrics["sorry"])
    core_lines = int(codebase_metrics["core_lines"])
    contract_count = int(codebase_metrics["example_contracts"])

    errors: list[str] = []

    # Check property test file header counts
    errors.extend(check_property_test_headers(per_contract))

    # Check README.md
    readme = ROOT / "README.md"
    readme_checks = [
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
                (
                    "Foundry test count in Testing section",
                    re.compile(r"Foundry tests.*\((\d+) tests\)"),
                    str(test_count),
                ),
            ]
    errors.extend(check_and_maybe_fix(readme, readme_checks, args.fix))
    # Check per-contract theorem counts in README table (| Contract | N | ...)
    readme_contract_checks = []
    for contract, count in per_contract.items():
        if contract == "Stdlib":
            continue  # Stdlib not in README table
        readme_contract_checks.append((
            f"README {contract} count",
            re.compile(rf"\|\s*{contract}\s*\|\s*(\d+)\s*\|"),
            str(count),
        ))
    errors.extend(check_and_maybe_fix(readme, readme_contract_checks, args.fix))

    # Check per-contract theorem counts in examples/solidity/README.md (| ... | N theorems | ...)
    solidity_readme = ROOT / "examples" / "solidity" / "README.md"
    solidity_contract_checks = []
    for contract, count in per_contract.items():
        if contract == "Stdlib":
            continue
        solidity_contract_checks.append((
            f"solidity README {contract} count",
            re.compile(rf"{contract}\.lean.*?(\d+) theorems"),
            str(count),
        ))
    errors.extend(check_and_maybe_fix(solidity_readme, solidity_contract_checks, args.fix))

    # Check llms.txt
    llms = ROOT / "docs-site" / "public" / "llms.txt"
    errors.extend(
        check_and_maybe_fix(
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
            args.fix,
        )
    )
    # Check per-contract theorem counts in llms.txt table (| Contract | N | ...)
    llms_contract_checks = []
    for contract, count in per_contract.items():
        llms_contract_checks.append((
            f"llms.txt {contract} count",
            re.compile(rf"\|\s*{contract}\s*\|\s*(\d+)\s*\|"),
            str(count),
        ))
    errors.extend(check_and_maybe_fix(llms, llms_contract_checks, args.fix))

    # Check compiler.mdx
    compiler_mdx = ROOT / "docs-site" / "content" / "compiler.mdx"
    errors.extend(
        check_and_maybe_fix(
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
                (
                    "example contract count",
                    re.compile(r"(\d+) example contracts"),
                    str(contract_count),
                ),
            ],
            args.fix,
        )
    )

    # Check examples.mdx
    examples_mdx = ROOT / "docs-site" / "content" / "examples.mdx"
    errors.extend(
        check_and_maybe_fix(
            examples_mdx,
            [
                (
                    "contract count in description",
                    re.compile(r"(\d+) contracts covering"),
                    str(contract_count),
                ),
            ],
            args.fix,
        )
    )

    # Check TRUST_ASSUMPTIONS.md
    trust = ROOT / "TRUST_ASSUMPTIONS.md"
    errors.extend(
        check_and_maybe_fix(
            trust,
            [
                (
                    "axiom count in verification chain",
                    re.compile(r"FULLY VERIFIED, (\d+) axioms"),
                    str(axiom_count),
                ),
                (
                    "covered count",
                    re.compile(r"(\d+) theorems have corresponding Foundry property tests"),
                    str(covered_count),
                ),
                (
                    "coverage percentage",
                    re.compile(r"(\d+)% runtime test coverage"),
                    str(coverage_pct),
                ),
                (
                    "theorem count in summary",
                    re.compile(r"(\d+) theorems across \d+ categor"),
                    str(total_theorems),
                ),
                (
                    "category count in summary",
                    re.compile(r"\d+ theorems across (\d+) categor"),
                    str(num_categories),
                ),
            ],
            args.fix,
        )
    )

    # Check test/README.md
    test_readme = ROOT / "test" / "README.md"
    errors.extend(
        check_and_maybe_fix(
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
                (
                    "property test function count",
                    re.compile(r"(\d+) functions, covering"),
                    str(property_fn_count),
                ),
            ],
            args.fix,
        )
    )

    # Check docs/VERIFICATION_STATUS.md
    verification_status = ROOT / "docs" / "VERIFICATION_STATUS.md"
    errors.extend(
        check_and_maybe_fix(
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
                (
                    "differential test total",
                    re.compile(r"Scaled to (\d+,\d+)\+"),
                    f"{diff_test_total:,}",
                ),
                (
                    "AST equiv theorem count",
                    re.compile(r"equivalence proofs \((\d+) theorems"),
                    str(ast_equiv_count),
                ),
            ],
            args.fix,
        )
    )

    # Check docs/ROADMAP.md
    roadmap = ROOT / "docs" / "ROADMAP.md"
    errors.extend(
        check_and_maybe_fix(
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
                (
                    "AST equiv theorem count",
                    re.compile(r"equivalence proofs \((\d+) theorems"),
                    str(ast_equiv_count),
                ),
            ],
            args.fix,
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
        (
            "AST equiv theorem count",
            re.compile(r"\((\d+) public \+"),
            str(ast_equiv_count),
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
    errors.extend(check_and_maybe_fix(verification_mdx, verification_checks, args.fix))

    # Validate theorem names in verification.mdx tables against manifest
    errors.extend(
        check_verification_theorem_names(verification_mdx)
    )

    # Check research.mdx
    research_mdx = ROOT / "docs-site" / "content" / "research.mdx"
    errors.extend(
        check_and_maybe_fix(
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
            args.fix,
        )
    )

    # Check theorem counts in getting-started.mdx
    getting_started = ROOT / "docs-site" / "content" / "getting-started.mdx"
    errors.extend(
        check_and_maybe_fix(
            getting_started,
            [
                (
                    "theorem count",
                    re.compile(r"verifies all (\d+) theorems"),
                    str(total_theorems),
                ),
            ],
            args.fix,
        )
    )

    # Check theorem count, test counts, and core size in index.mdx
    index_mdx = ROOT / "docs-site" / "content" / "index.mdx"
    errors.extend(
        check_and_maybe_fix(
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
                (
                    "core line count",
                    re.compile(r"the (\d+)-line EDSL"),
                    str(core_lines),
                ),
            ],
            args.fix,
        )
    )

    # Check core size claims in core.mdx
    core_mdx = ROOT / "docs-site" / "content" / "core.mdx"
    errors.extend(
        check_and_maybe_fix(
            core_mdx,
            [
                (
                    "core line count",
                    re.compile(r"the (\d+)-line core"),
                    str(core_lines),
                ),
            ],
            args.fix,
        )
    )

    # Check layout.tsx banner (proven/total theorems proven)
    layout_tsx = ROOT / "docs-site" / "app" / "layout.tsx"
    errors.extend(
        check_and_maybe_fix(
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
            args.fix,
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
            f"{exclusion_count} exclusions, "
            f"{ast_equiv_count} AST equiv theorems",
            file=sys.stderr,
        )
        raise SystemExit(1)

    print(
        f"Documentation count check passed "
        f"({total_theorems} theorems, {num_categories} categories, "
        f"{axiom_count} axioms, {test_count} tests, {suite_count} suites, "
        f"{sorry_count} sorry, {covered_count}/{total_theorems} covered, "
        f"{ast_equiv_count} AST equiv)."
    )


if __name__ == "__main__":
    main()
