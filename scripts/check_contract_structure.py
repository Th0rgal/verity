#!/usr/bin/env python3
"""Validate that all contracts have the expected file structure.

For each contract found in DumbContracts/Examples/, verify that the
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
    "DumbContracts/Specs/{name}/Spec.lean",
    "DumbContracts/Specs/{name}/Invariants.lean",
    "DumbContracts/Proofs/{name}/Basic.lean",
    "DumbContracts/Proofs/{name}/Correctness.lean",
]


def die(msg: str) -> None:
    print(f"ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def find_contracts() -> list[str]:
    """Find all contract names from DumbContracts/Examples/."""
    examples_dir = ROOT / "DumbContracts" / "Examples"
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
    """Check that All.lean imports all contracts."""
    all_lean = ROOT / "DumbContracts" / "All.lean"
    if not all_lean.exists():
        return [f"DumbContracts/All.lean not found"]

    lines = all_lean.read_text().splitlines()
    missing = []
    for name in contracts:
        expected_import = f"import DumbContracts.Examples.{name}"
        # Use exact line matching to avoid prefix collisions
        # (e.g., "Owned" matching "OwnedCounter")
        if not any(line.strip() == expected_import for line in lines):
            missing.append(f"DumbContracts/All.lean missing: {expected_import}")
    return missing


def main() -> None:
    contracts = find_contracts()
    if not contracts:
        die("No contracts found in DumbContracts/Examples/")

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
