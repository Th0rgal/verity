# DumbContracts Scripts

This directory contains verification and testing scripts for the DumbContracts project.

## Property Test Coverage Scripts

These scripts manage the relationship between proven Lean theorems and their corresponding Foundry test implementations.

### Core Scripts

- **`check_property_manifest.py`** - Verifies that `property_manifest.json` contains all property theorems from Lean proofs
- **`check_property_coverage.py`** - Ensures all properties are either tested or explicitly excluded
- **`report_property_coverage.py`** - Generates detailed coverage statistics (new!)

### Usage

#### Check Coverage (CI)
```bash
# Verify manifest is up-to-date
python3 scripts/check_property_manifest.py

# Verify all properties are covered or excluded
python3 scripts/check_property_coverage.py
```

#### Generate Coverage Reports
```bash
# Text report (default)
python3 scripts/report_property_coverage.py

# Markdown report (for GitHub)
python3 scripts/report_property_coverage.py --format=markdown

# JSON report (for tooling)
python3 scripts/report_property_coverage.py --format=json

# Fail if coverage is below threshold
python3 scripts/report_property_coverage.py --fail-below 50.0
```

#### Find Missing Properties
```bash
# List properties without test coverage
python3 scripts/report_property_gaps.py

# Generate test stubs for missing properties
python3 scripts/report_property_gaps.py --stubs
```

### Coverage Report Format

The coverage report shows:
- **Total Properties**: All proven theorems across all contracts
- **Covered**: Properties with corresponding Foundry tests (tagged with `Property: <theorem_name>`)
- **Excluded**: Properties explicitly marked as proof-only or requiring special modeling
- **Missing**: Properties that need test coverage (should be 0 after verification)

Example output:
```
✅ SimpleToken
   Total:      56 properties
   Covered:    47 ( 84.0%)
   Excluded:     9 (proof-only)

Overall: 69.9% coverage (207/296 properties)
```

### Property Exclusions

Properties are excluded in `test/property_exclusions.json` for valid reasons:
- **Proof-only**: Low-level helpers (e.g., `setStorage_*`, `getStorage_*`) that are internal proof machinery
- **Sum equations**: Properties requiring finite address set modeling (e.g., total supply invariants)
- **Internal helpers**: Functions like `isOwner_*` that are tested implicitly through other operations

## Validation Scripts

These CI-critical scripts validate cross-layer consistency:

- **`check_property_manifest_sync.py`** - Ensures `property_manifest.json` stays in sync with actual Lean theorems (detects added/removed theorems)
- **`check_storage_layout.py`** - Validates storage slot consistency across EDSL, Spec, and Compiler layers; detects intra-contract slot collisions
- **`check_doc_counts.py`** - Validates theorem, axiom, category, test, and suite counts in README.md, llms.txt, and TRUST_ASSUMPTIONS.md against actual codebase data
- **`check_contract_structure.py`** - Validates all contracts in Examples/ have complete file structure (Spec, Invariants, Basic proofs, Correctness proofs)

```bash
# Run locally before submitting documentation changes
python3 scripts/check_doc_counts.py

# Run locally after modifying storage slots or adding contracts
python3 scripts/check_storage_layout.py

# Run locally after adding/removing theorems
python3 scripts/check_property_manifest_sync.py

# Run locally after adding a new contract
python3 scripts/check_contract_structure.py
```

## Selector & Yul Scripts

- **`check_selectors.py`** - Verifies function selector hashes match between Lean and generated Yul
- **`check_selector_fixtures.py`** - Cross-checks selectors against solc-generated hashes
- **`check_yul_compiles.py`** - Ensures generated Yul code compiles with solc

## Contract Scaffold Generator

- **`generate_contract.py`** - Generates all boilerplate files for a new contract

```bash
# Simple contract
python3 scripts/generate_contract.py MyContract

# Contract with typed fields and custom functions
python3 scripts/generate_contract.py MyToken \
  --fields "balances:mapping,totalSupply:uint256,owner:address" \
  --functions "deposit,withdraw,getBalance"

# Preview without creating files
python3 scripts/generate_contract.py MyContract --dry-run
```

Creates 6 files: EDSL implementation, Spec, Invariants, Basic proofs, Correctness proofs, and Property tests. Prints instructions for manual steps (All.lean imports, Compiler/Specs.lean entry).

## Utilities

- **`property_utils.py`** - Shared utilities for loading manifests, exclusions, and test coverage
- **`keccak256.py`** - Keccak-256 hashing implementation for selector verification
- **`extract_property_manifest.py`** - Extracts theorem names from Lean proofs to regenerate `property_manifest.json`
- **`test_multiple_seeds.sh`** - Runs Foundry tests with multiple random seeds to detect flakiness

## CI Integration

All verification scripts run automatically in GitHub Actions (`verify.yml`):
1. Property manifest sync check
2. Property coverage validation
3. Selector hash verification (against Lean specs and solc output)
4. Yul compilation check
5. Storage layout consistency validation
6. Contract file structure validation
7. Documentation count validation
8. Coverage reports in workflow summary

## Adding New Property Tests

To add test coverage for a proven theorem:

1. Add a `Property: <theorem_name>` comment in your test function:
   ```solidity
   /**
    * Property: transfer_preserves_balance
    * Theorem: Transfer doesn't change total balance
    */
   function testProperty_TransferPreservesBalance() public { ... }
   ```

2. Run verification:
   ```bash
   python3 scripts/check_property_coverage.py
   python3 scripts/report_property_coverage.py
   ```

3. If the property cannot be tested in Foundry (e.g., proof-only helper), add it to `test/property_exclusions.json`

## Recent Improvements

- **Property Coverage Reporting** (Feb 2026): Added comprehensive coverage statistics and reporting
  - Text/Markdown/JSON output formats
  - Per-contract and overall statistics
  - CI integration with GitHub workflow summaries
  - Coverage improved from 53.1% (155/292) to 70% (207/296) — all testable properties covered
