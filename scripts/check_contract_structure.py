#!/usr/bin/env python3
"""Validate that all contracts have the expected file structure.

For each contract found in Verity/Examples/, verify that the
corresponding Spec, Invariants, and Proof files exist. This catches
incomplete contract additions early.

Contracts with inline proofs (e.g., ReentrancyExample) are excluded.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Contracts that use non-standard structure (inline proofs, proof-only, etc.)
EXCLUDED_CONTRACTS = {
    "ReentrancyExample",  # Inline proofs in Examples/, no separate Proofs/ dir
    "CryptoHash",         # Axiom-based, no separate proof structure
}

# Expected files for each contract (relative to ROOT)
EXPECTED_STRUCTURE = [
    "Verity/Specs/{name}/Spec.lean",
    "Verity/Specs/{name}/Invariants.lean",
    "Verity/Specs/{name}/Proofs.lean",
    "Verity/Proofs/{name}/Basic.lean",
    "Verity/Proofs/{name}/Correctness.lean",
]


def die(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def find_contracts() -> list[str]:
    """Find all contract names from Verity/Examples/."""
    examples_dir = ROOT / "Verity" / "Examples"
    if not examples_dir.is_dir():
        die(f"Examples directory not found: {examples_dir}")

    contracts = []
    for f in sorted(examples_dir.iterdir()):
        if f.suffix == ".lean" and f.stem not in EXCLUDED_CONTRACTS:
            contracts.append(f.stem)
    return contracts


def check_contract(name: str) -> list[str]:
    """Check a single contract has all expected files. Returns missing paths."""
    missing = []
    for template in EXPECTED_STRUCTURE:
        path = ROOT / template.format(name=name)
        if not path.exists():
            missing.append(str(path.relative_to(ROOT)))
    return missing


def check_all_lean_imports(contracts: list[str]) -> list[str]:
    """Check that All.lean imports all required modules for each contract.

    For each contract, verifies the Examples import and all imports
    corresponding to EXPECTED_STRUCTURE (Spec, Invariants, Proofs, Basic,
    Correctness).
    """
    all_lean = ROOT / "Verity" / "All.lean"
    if not all_lean.exists():
        return [f"Verity/All.lean not found"]

    line_set = {line.strip() for line in all_lean.read_text().splitlines()}
    missing = []
    for name in contracts:
        # Check Examples import
        examples_import = f"import Verity.Examples.{name}"
        if examples_import not in line_set:
            missing.append(f"Verity/All.lean missing: {examples_import}")
        # Check imports for each file in EXPECTED_STRUCTURE
        for template in EXPECTED_STRUCTURE:
            path = template.format(name=name)
            import_path = path.replace("/", ".").removesuffix(".lean")
            expected_import = f"import {import_path}"
            if expected_import not in line_set:
                missing.append(f"Verity/All.lean missing: {expected_import}")
    return missing


def main() -> None:
    contracts = find_contracts()
    if not contracts:
        die("No contracts found in Verity/Examples/")

    print(f"Checking {len(contracts)} contracts for complete file structure...")
    print(f"  (Excluding: {', '.join(sorted(EXCLUDED_CONTRACTS))})")
    print()

    all_issues: list[str] = []

    for name in contracts:
        missing = check_contract(name)
        if missing:
            print(f"  INCOMPLETE {name}:")
            for m in missing:
                print(f"    Missing: {m}")
            all_issues.extend(f"{name}: {m}" for m in missing)
        else:
            print(f"  OK {name}")

    # Check All.lean imports
    import_issues = check_all_lean_imports(contracts)
    if import_issues:
        print()
        print("  All.lean import issues:")
        for issue in import_issues:
            print(f"    {issue}")
        all_issues.extend(import_issues)

    print()
    if all_issues:
        print(f"FAILED: {len(all_issues)} issue(s) found")
        sys.exit(1)
    else:
        print(f"OK: All {len(contracts)} contracts have complete file structure")


if __name__ == "__main__":
    main()
