#!/usr/bin/env python3
"""Validate that all contracts have the expected file structure.

For each contract found in Contracts/, verify that the corresponding
Spec, Invariants, and proof modules exist. This catches incomplete
contract additions early.

Contracts with non-standard structure (e.g., ReentrancyExample) are excluded.
"""

from __future__ import annotations

import sys

from property_utils import ROOT, die

# Contracts that use non-standard structure (inline proofs, proof-only, etc.)
EXCLUDED_CONTRACTS = {
    "ReentrancyExample",  # Inline proofs in Examples/, no separate Proofs/ dir
    "CryptoHash",         # Axiom-based, no separate proof structure
}

# Contracts excluded from property test check
EXCLUDED_FROM_PROPERTY_TESTS = {
    "CryptoHash",         # External-library contract, no property tests
    "Vault",              # Minimal scaffolding landed before proof/property suite completion
}

# Contracts excluded from differential test check
EXCLUDED_FROM_DIFFERENTIAL_TESTS = {
    "CryptoHash",         # External-library oracle behavior is not differential-tested
    "ReentrancyExample",  # Reentrancy model requires dedicated external-call harnessing
    "Vault",              # Minimal scaffolding landed before differential harness completion
}

# Expected files for each contract (relative to ROOT)
EXPECTED_STRUCTURE = [
    "Contracts/{name}/{name}.lean",
    "Contracts/{name}/Spec.lean",
    "Contracts/{name}/Invariants.lean",
    "Contracts/{name}/Proofs/Basic.lean",
    "Contracts/{name}/Proofs/Correctness.lean",
    "Contracts/{name}/SpecProofs.lean",
]


def is_contract_dir(path) -> bool:
    """Return whether a Contracts/ child looks like a contract module directory."""
    if not path.is_dir():
        return False
    name = path.name
    return (path / f"{name}.lean").exists() or (path / "Contract.lean").exists()


def find_contracts() -> list[str]:
    """Find all contract names from Contracts/."""
    contracts_dir = ROOT / "Contracts"
    if not contracts_dir.is_dir():
        die(f"Contracts directory not found: {contracts_dir}")

    contracts = []
    for f in sorted(contracts_dir.iterdir()):
        if is_contract_dir(f) and f.name not in EXCLUDED_CONTRACTS:
            contracts.append(f.name)
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
    """Check that Contracts.lean imports each contract umbrella module.

    For each contract, expects:
      import Contracts.<ContractName>
    """
    all_lean = ROOT / "Contracts.lean"
    if not all_lean.exists():
        return [f"Contracts.lean not found"]

    line_set = {line.strip() for line in all_lean.read_text().splitlines()}
    missing = []
    for name in contracts:
        expected_import = f"import Contracts.{name}"
        if expected_import not in line_set:
            missing.append(f"Contracts.lean missing: {expected_import}")
    return missing


def check_all_lean_imports_exist() -> list[str]:
    """Check that every import in Contracts.lean points to a file that exists.

    Parses all ``import Contracts.*`` lines and verifies the corresponding
    ``.lean`` file is present on disk.  This catches orphaned imports
    (e.g. someone deletes a proof file but forgets to remove the import)
    and typos in module paths.
    """
    all_lean = ROOT / "Contracts.lean"
    if not all_lean.exists():
        return ["Contracts.lean not found"]

    issues: list[str] = []
    for line in all_lean.read_text().splitlines():
        stripped = line.strip()
        # Skip comments and blank lines
        if not stripped.startswith("import Verity.") and not stripped.startswith("import Contracts."):
            continue
        # "import Contracts.Counter" → "Contracts/Counter.lean"
        module = stripped.removeprefix("import ").split()[0]
        file_path = ROOT / (module.replace(".", "/") + ".lean")
        if not file_path.exists():
            rel = str(file_path.relative_to(ROOT))
            issues.append(f"Contracts.lean imports {module} but {rel} does not exist")
    return issues


def check_differential_tests(all_examples: list[str]) -> list[str]:
    """Check that each eligible contract has a Differential test suite."""
    issues: list[str] = []
    for name in all_examples:
        if name in EXCLUDED_FROM_DIFFERENTIAL_TESTS:
            continue
        diff_test = ROOT / "test" / f"Differential{name}.t.sol"
        if not diff_test.exists():
            issues.append(f"{name}: missing test/Differential{name}.t.sol")
    return issues


def check_property_tests(all_examples: list[str]) -> list[str]:
    """Check that each eligible contract has a Property test suite."""
    issues: list[str] = []
    for name in all_examples:
        if name in EXCLUDED_FROM_PROPERTY_TESTS:
            continue
        prop_test = ROOT / "test" / f"Property{name}.t.sol"
        if not prop_test.exists():
            issues.append(f"{name}: missing test/Property{name}.t.sol")
    return issues


def main() -> None:
    contracts = find_contracts()
    if not contracts:
        die("No contracts found in Contracts/")

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

    # Check property test files
    all_examples = [
        f.name for f in sorted((ROOT / "Contracts").iterdir())
        if is_contract_dir(f)
    ]
    property_issues = check_property_tests(all_examples)
    for issue in property_issues:
        print(f"  MISSING {issue}")
    all_issues.extend(property_issues)

    # Check differential test files
    differential_issues = check_differential_tests(all_examples)
    for issue in differential_issues:
        print(f"  MISSING {issue}")
    all_issues.extend(differential_issues)

    # Check All.lean imports
    import_issues = check_all_lean_imports(contracts)
    if import_issues:
        print()
        print("  Contracts.lean import issues:")
        for issue in import_issues:
            print(f"    {issue}")
        all_issues.extend(import_issues)

    # Check that every import in All.lean resolves to an existing file
    existence_issues = check_all_lean_imports_exist()
    if existence_issues:
        print()
        print("  Contracts.lean orphaned imports:")
        for issue in existence_issues:
            print(f"    {issue}")
        all_issues.extend(existence_issues)

    print()
    if all_issues:
        print(f"FAILED: {len(all_issues)} issue(s) found")
        sys.exit(1)
    else:
        print(f"OK: All {len(contracts)} contracts have complete file structure")


if __name__ == "__main__":
    main()
