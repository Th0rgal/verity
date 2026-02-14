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

Overall: 53.1% coverage (155/292 properties)
```

### Property Exclusions

Properties are excluded in `test/property_exclusions.json` for valid reasons:
- **Proof-only**: Low-level helpers (e.g., `setStorage_*`, `getStorage_*`) that are internal proof machinery
- **Sum equations**: Properties requiring finite address set modeling (e.g., total supply invariants)
- **Internal helpers**: Functions like `isOwner_*` that are tested implicitly through other operations

## Selector & Yul Scripts

- **`check_selectors.py`** - Verifies function selector hashes match between Lean and generated Yul
- **`check_selector_fixtures.py`** - Cross-checks selectors against solc-generated hashes
- **`check_yul_compiles.py`** - Ensures generated Yul code compiles with solc

## Utilities

- **`property_utils.py`** - Shared utilities for loading manifests, exclusions, and test coverage
- **`keccak256.py`** - Keccak-256 hashing implementation for selector verification

## CI Integration

All verification scripts run automatically in GitHub Actions:
1. Property coverage is checked on every PR
2. Coverage reports are displayed in the workflow summary
3. Selector hashes are verified against both Lean specs and solc output
4. Generated Yul code must compile successfully

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
  - Coverage improved from 53.1% (155/292) to near-complete (see reports for current status)
