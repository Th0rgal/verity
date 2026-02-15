# Test Suite

Foundry-based tests validating EDSL, Yul, and EVM execution equivalence.

## Test Types

### Property Tests
**Pattern**: `Property<Contract>.t.sol`

Validate that proven Lean theorems hold when executed as EVM bytecode. Each test tags the corresponding theorem:

```solidity
/// Property: store_retrieve_correct
function testProperty_StoreRetrieve() public {
    // Test implementation
}
```

**Coverage**: 207/296 theorems tested (70%), 89 proof-only exclusions documented in `property_exclusions.json`.

### Differential Tests
**Pattern**: `Differential<Contract>.t.sol`

Compare EDSL interpreter output against Yul-compiled EVM execution to catch compiler bugs.

**Files**: `DifferentialTestBase.sol` (shared utilities), `DiffTestConfig.sol` (configuration)

### Unit Tests
**Pattern**: `Unit<Contract>.t.sol`

Basic contract behavior validation without formal property mapping.

## Running Tests

```bash
# All tests
forge test

# Single contract
forge test --match-path test/PropertyCounter.t.sol

# Specific test
forge test --match-test testProperty_StoreRetrieve

# With verbosity
forge test -vvv

# Multi-seed testing (detects flakiness)
bash scripts/test_multiple_seeds.sh
```

## Test Organization

```
test/
├── Property*.t.sol          # Property tests (207 tests)
├── Differential*.t.sol      # Differential tests
├── Unit*.t.sol              # Unit tests
├── DifferentialTestBase.sol # Shared differential test utilities
├── DiffTestConfig.sol       # Test configuration
├── property_manifest.json   # All Lean theorems (auto-generated)
└── property_exclusions.json # Proof-only theorems (manual)
```

## Coverage Validation

CI automatically validates:
- Property manifest sync (`check_property_manifest.py`)
- Property coverage (`check_property_coverage.py`)
- All manifest theorems have tests or documented exclusions

Generate coverage report:
```bash
python3 scripts/report_property_coverage.py
```

## Adding Property Tests

1. Prove theorem in `Verity/Specs/<Contract>/Proofs.lean`
2. Add test in `test/Property<Contract>.t.sol` with tag:
   ```solidity
   /// Property: theorem_name
   ```
3. Validate: `python3 scripts/check_property_coverage.py`

If a theorem can't be tested (proof-only helper), add to `property_exclusions.json` with justification.

See [`scripts/README.md`](../scripts/README.md) for full property testing details.
