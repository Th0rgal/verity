# Verity Scripts

This directory contains verification and testing scripts for the Verity project.

## Property Test Coverage Scripts

These scripts manage the relationship between proven Lean theorems and their corresponding Foundry test implementations.

### Core Scripts

- **`check_property_manifest.py`** - Verifies that `property_manifest.json` contains all property theorems from Lean proofs
- **`check_property_coverage.py`** - Ensures all properties are either tested or explicitly excluded
- **`report_property_coverage.py`** - Generates detailed coverage statistics

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
   Total:      59 properties
   Covered:    52 ( 88.1%)
   Excluded:     7 (proof-only)

Overall: 59% coverage (220/371 properties)
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
- **`check_doc_counts.py`** - Validates theorem, axiom, test, suite, coverage, and contract counts across 14 documentation files (README, llms.txt, compiler.mdx, verification.mdx, research.mdx, index.mdx, core.mdx, examples.mdx, getting-started.mdx, TRUST_ASSUMPTIONS, VERIFICATION_STATUS, ROADMAP, test/README, layout.tsx), theorem-name completeness in verification.mdx tables, and proven-theorem counts in Property*.t.sol file headers
- **`check_axiom_locations.py`** - Validates that AXIOMS.md line number references match actual axiom locations in source files
- **`check_contract_structure.py`** - Validates all contracts in Examples/ have complete file structure (Spec, Invariants, Basic proofs, Correctness proofs)
- **`check_lean_hygiene.py`** - Validates no `#eval` in Compiler/Proofs/ and exactly 1 `allowUnsafeReducibility` (documented trust assumption)

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
- **`check_yul_compiles.py`** - Ensures generated Yul code compiles with solc and can compare bytecode parity between directories

```bash
# Default: check compiler/yul
python3 scripts/check_yul_compiles.py

# Check multiple directories and assert legacy/AST bytecode parity
python3 scripts/check_yul_compiles.py \
  --dir compiler/yul \
  --dir compiler/yul-ast \
  --compare-dirs compiler/yul compiler/yul-ast
```

## Contract Scaffold Generator

- **`generate_contract.py`** - Generates all boilerplate files for a new contract

```bash
# Simple contract
python3 scripts/generate_contract.py MyContract

# Contract with typed fields and custom functions
python3 scripts/generate_contract.py MyToken \
  --fields "balances:mapping,totalSupply:uint256,owner:address" \
  --functions "deposit(uint256),withdraw(uint256),getBalance(address)"

# Preview without creating files
python3 scripts/generate_contract.py MyContract --dry-run
```

Creates 7 files: EDSL implementation, Spec, Invariants, Proofs re-export, Basic proofs, Correctness proofs, and Property tests. Prints instructions for manual steps (All.lean imports, Compiler/Specs.lean entry).

## Utilities

- **`property_utils.py`** - Shared utilities for loading manifests, exclusions, and test coverage
- **`keccak256.py`** - Keccak-256 hashing implementation for selector verification
- **`extract_property_manifest.py`** - Extracts theorem names from Lean proofs to regenerate `property_manifest.json`
- **`test_multiple_seeds.sh`** - Runs Foundry tests with multiple random seeds to detect flakiness

## CI Integration

Scripts run automatically in GitHub Actions (`verify.yml`) across 5 jobs:

**`changes`** — Path filter that gates code-dependent jobs (doc-only PRs skip build/test)

**`checks` job** (fast, no Lean build required):
1. Property manifest validation (`check_property_manifest.py`)
2. Property coverage validation (`check_property_coverage.py`)
3. Contract file structure validation (`check_contract_structure.py`)
4. Axiom location validation (`check_axiom_locations.py`)
5. Documentation count validation (`check_doc_counts.py`)
6. Property manifest sync (`check_property_manifest_sync.py`)
7. Storage layout consistency (`check_storage_layout.py`)
8. Lean hygiene (`check_lean_hygiene.py`)

**`build` job** (requires `lake build` artifacts):
1. Keccak-256 self-test (`keccak256.py --self-test`)
2. Selector hash verification (`check_selectors.py`)
3. Yul compilation check (`check_yul_compiles.py`)
4. Selector fixture check (`check_selector_fixtures.py`)
5. Coverage and storage layout reports in workflow summary

**`foundry`** — 8-shard parallel Foundry tests with seed 42
**`foundry-multi-seed`** — 7-seed flakiness detection (seeds: 0, 1, 42, 123, 999, 12345, 67890)

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
