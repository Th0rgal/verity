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

**Coverage**: 220/378 theorems tested (58%), 158 proof-only exclusions documented in `property_exclusions.json`.

### Differential Tests
**Pattern**: `Differential<Contract>.t.sol`

Compare EDSL interpreter output against Yul-compiled EVM execution to catch compiler bugs.

**Files**: `DifferentialTestBase.sol` (shared utilities), `DiffTestConfig.sol` (configuration)

### Unit Tests
**Pattern**: `<Contract>.t.sol` (e.g., `Counter.t.sol`, `Ledger.t.sol`)

Basic contract behavior validation without formal property mapping.

## Running Tests

```bash
# All tests (requires FFI for property tests and differential tests)
FOUNDRY_PROFILE=difftest forge test

# Unit tests only (no FFI needed)
forge test --no-match-path "test/Property*" --no-match-path "test/Differential*" --no-match-path "test/CallValue*" --no-match-path "test/CalldataSize*" --no-match-path "test/yul/*"

# Single contract
FOUNDRY_PROFILE=difftest forge test --match-path test/PropertyCounter.t.sol

# Specific test
FOUNDRY_PROFILE=difftest forge test --match-test testProperty_StoreRetrieve

# With verbosity
FOUNDRY_PROFILE=difftest forge test -vvv

# Multi-seed testing (detects flakiness)
bash scripts/test_multiple_seeds.sh
```

> **Note**: Property tests (`Property*.t.sol`) deploy Yul contracts via `vm.ffi()`, and differential tests shell out to `lake exe difftest-interpreter`. Both require `FOUNDRY_PROFILE=difftest`. Plain `forge test` will fail on these suites because FFI is disabled in the default profile. See [foundry.toml](../foundry.toml).

## Test Organization

```
test/
├── Property*.t.sol           # Property tests (195 functions, covering 220/378 theorems)
├── Differential*.t.sol       # Differential tests
├── <Contract>.t.sol          # Unit tests (Counter, Ledger, Owned, etc.)
├── CallValueGuard.t.sol      # Call value rejection tests
├── CalldataSizeGuard.t.sol   # Calldata size validation tests
├── SelectorSanity.t.sol      # Selector verification tests
├── DifferentialTestBase.sol  # Shared differential test utilities
├── DiffTestConfig.sol        # Test configuration
├── yul/                      # Yul test utilities (YulTestBase.sol)
├── property_manifest.json    # All Lean theorems (auto-generated)
└── property_exclusions.json  # Proof-only theorems (manual)
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

1. Prove theorem in `Verity/Proofs/<Contract>/Basic.lean`
2. Add test in `test/Property<Contract>.t.sol` with tag:
   ```solidity
   /// Property: theorem_name
   ```
3. Validate: `python3 scripts/check_property_coverage.py`

If a theorem can't be tested (proof-only helper), add to `property_exclusions.json` with justification.

See [`scripts/README.md`](../scripts/README.md) for full property testing details.
