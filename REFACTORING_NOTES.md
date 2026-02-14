# Differential Test Refactoring

## Summary

Created `test/DifferentialTestBase.sol` to consolidate duplicated utility functions across all differential test files.

## Problem

The 7 differential test files (`DifferentialCounter.t.sol`, `DifferentialLedger.t.sol`, etc.) contained significant code duplication:

- `contains()` - string search (duplicated 7 times)
- `_extractReturnValue()` - JSON parsing (duplicated 7 times)
- `_stringToUint()` - string conversion (duplicated 7 times)
- `_extractStorageChange()` - JSON parsing (duplicated 7 times)
- `_extractNumber()` - JSON parsing (duplicated 6 times)
- `_toLowerCase()` - string manipulation (duplicated 4 times)
- `_prng()` - pseudo-random generation (duplicated 5 times)
- `_skipRandom()` - PRNG helper (duplicated 5 times)
- `_indexToAddress()` - address mapping (duplicated 5 times)
- `_addressToString()` - address formatting (duplicated 3 times)
- `_hexChar()` - hex formatting (duplicated 3 times)
- `_parseHexAddress()` - hex parsing (duplicated 3 times)

**Total:** ~800-900 lines of duplicated code across the 7 files.

## Solution

Created `test/DifferentialTestBase.sol` (291 lines) containing:

1. **JSON Parsing Utilities**
   - `_extractReturnValue()` - Extract returnValue from EDSL JSON
   - `_extractStorageChange()` - Extract storage changes from JSON
   - `_extractNumber()` - Parse numbers from JSON

2. **String Utilities**
   - `contains()` - Substring search
   - `_stringToUint()` - String to uint256 conversion
   - `_toLowerCase()` - Lowercase conversion
   - `_addressToString()` - Address to hex string
   - `_hexChar()` - Hex character conversion
   - `_parseHexAddress()` - Hex string to uint256

3. **Test Utilities**
   - `_prng()` - Linear congruential generator
   - `_skipRandom()` - Skip PRNG iterations
   - `_indexToAddress()` - Deterministic address generation
   - `testsPassed` / `testsFailed` - Shared counters

## Impact (Pilot: DifferentialCounter.t.sol)

- **Before:** 406 lines
- **After:** 293 lines
- **Reduction:** 113 lines (-28%)
- **Added:** 1 import statement

## Projected Impact (All 7 Files)

Once all differential tests are refactored:

- **Before:** ~2,800 lines total (7 files × ~400 lines avg)
- **After:** ~2,050 lines total (291 shared + 7 files × ~250 lines avg)
- **Total Reduction:** ~750 lines (-27%)

## Benefits

1. **Single Source of Truth** - Utility functions defined once
2. **Easier Maintenance** - Bug fixes apply to all tests
3. **Consistency** - All tests use identical parsing logic
4. **Readability** - Test files focus on test logic, not utilities
5. **Extensibility** - New differential tests can reuse utilities

## Next Steps

To complete the refactoring:

1. Refactor remaining 6 differential test files:
   - `DifferentialLedger.t.sol`
   - `DifferentialOwned.t.sol`
   - `DifferentialOwnedCounter.t.sol`
   - `DifferentialSafeCounter.t.sol`
   - `DifferentialSimpleStorage.t.sol`
   - `DifferentialSimpleToken.t.sol`

2. Run full test suite to verify no regressions

3. Update documentation if needed

## Files

- **New:** `test/DifferentialTestBase.sol` (291 lines)
- **Modified:** `test/DifferentialCounter.t.sol` (-113 lines)
- **Remaining:** 6 differential test files to refactor
