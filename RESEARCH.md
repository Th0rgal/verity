# Dumb Contracts Research Log

## Iteration 1: Bootstrap (2026-02-09)

### What I Added
1. **Minimal Lean EDSL Core** (DumbContracts/Core.lean:1-58)
   - Basic Ethereum types: Address, Uint256, Bool', Bytes
   - StorageSlot abstraction for type-safe storage access
   - ContractState structure with storage map, sender, and contract address
   - Contract monad as StateM alias
   - Storage operations: getStorage, setStorage
   - Context accessors: msgSender, contractAddress
   - Require guard for validation

2. **SimpleStorage Example** (DumbContracts/Examples/SimpleStorage.lean:1-38)
   - Demonstrates basic storage pattern
   - Two functions: store and retrieve
   - Includes executable example that evaluates to 42
   - Clean, minimal syntax

3. **Foundry Test Suite** (test/SimpleStorage.t.sol:1-41)
   - Tests initial state (zero value)
   - Tests store and retrieve
   - Tests value updates
   - Fuzz test for arbitrary values
   - All 4 tests pass with 256 fuzz runs

### What I Tried

**Approach 1: Initial design with `get` and `set` function names**
- Problem: Name collision with StateM's get method
- Solution: Renamed to getStorage and setStorage for clarity

**Approach 2: Using `StateM.get` explicitly**
- Problem: StateM.get doesn't exist in Lean 4's API
- Solution: Use plain `get` which is automatically available in do-notation

**Approach 3: Using `example` as function name**
- Problem: `example` is a reserved keyword in Lean
- Solution: Renamed to `exampleUsage`

**Approach 4: Including Repr instance for ContractState**
- Problem: Repr can't handle function types (Nat → Uint256)
- Solution: Removed the deriving Repr clause

### Findings

**EDSL Design Principles That Work:**
1. **StateM is the right abstraction** for contract execution
   - Clean do-notation syntax
   - Natural fit for storage operations
   - Easy to reason about state changes

2. **Type-safe storage slots** prevent common errors
   - StorageSlot wrapper makes slots explicit
   - Type parameter ensures type consistency
   - Simple Nat-based addressing is sufficient for now

3. **Minimal is maintainable**
   - Only 58 lines of core code
   - Zero external dependencies
   - Everything needed for basic contracts

4. **Example-driven development works**
   - SimpleStorage guided the core API design
   - Real usage revealed naming conflicts early
   - Having a working example validates the approach

**Lean 4 Specifics:**
- Do-notation requires using plain `get` and `modify`, not `StateM.get`
- Function types can't derive Repr automatically
- `example` is a reserved keyword
- Lake build system is straightforward and fast

**Testing Strategy:**
- Parallel Solidity implementation validates semantics
- Foundry tests provide runtime confidence
- Fuzz testing catches edge cases
- Evaluating Lean code inline (with #eval) catches issues early

### Complexity Metrics
- Core EDSL: 58 lines
- SimpleStorage Example: 38 lines (24 lines of actual code)
- Ratio: ~0.66 - example is slightly smaller than core
- Test coverage: 4 tests, all passing

### Next Iteration Ideas
1. **Counter contract** - add increment/decrement pattern
2. **Ownership pattern** - introduce msg.sender checks
3. **Events** - add event emission support
4. **Math safety** - add checked arithmetic helpers
5. **Multiple storage types** - extend beyond Uint256

### Questions for Future Exploration
- Should we add syntactic sugar for common patterns?
- How to handle reverts more elegantly?
- Can we add event support without too much complexity?
- Should we create a standard library module?

### Files Modified This Iteration
- Created: DumbContracts/Core.lean
- Created: DumbContracts/Examples/SimpleStorage.lean
- Created: DumbContracts.lean
- Created: contracts/SimpleStorage.sol
- Created: test/SimpleStorage.t.sol
- Created: lean-toolchain
- Created: lakefile.lean
- Created: foundry.toml
- Created: STATUS.md
- Created: RESEARCH.md
- Created: .gitignore

---

## Iteration 2: Counter Pattern (2026-02-09)

### What I Added
1. **Counter Example Contract** (DumbContracts/Examples/Counter.lean:1-50)
   - Demonstrates arithmetic operations (addition, subtraction)
   - Three functions: increment, decrement, getCount
   - Uses separate namespace (DumbContracts.Examples.Counter) to avoid name conflicts
   - Includes executable example that evaluates to 1 (increment twice, decrement once)
   - Clean syntax showing stateful updates

2. **Solidity Reference Implementation** (contracts/Counter.sol:1-23)
   - Parallel implementation in Solidity
   - Uses Solidity 0.8+ with built-in overflow protection
   - Identical semantics to Lean version

3. **Comprehensive Test Suite** (test/Counter.t.sol:1-70)
   - Tests initial state, single increment, multiple increments
   - Tests decrement behavior
   - Tests the specific example from Lean code
   - **Critical test**: Documents underflow protection (decrement from zero reverts)
   - Fuzz test for arbitrary increment counts
   - All 7 tests pass (11 total tests across both contracts)

### What I Tried

**Approach 1: Shared namespace for all examples**
- Problem: Name collision - both SimpleStorage and Counter define `exampleUsage`
- Solution: Use separate namespaces (DumbContracts.Examples.Counter vs DumbContracts.Examples)
- Learning: Need clear namespace strategy for growing example library

**Approach 2: Testing underflow behavior**
- Initial test: Expected underflow to wrap to max uint256
- Problem: Solidity 0.8+ reverts on underflow (arithmetic safety)
- Solution: Updated test to expect revert using `vm.expectRevert`
- **Key Finding**: This reveals the need to decide on arithmetic safety semantics

**Approach 3: Basic arithmetic with + and -**
- Used Lean's built-in Nat arithmetic (+ and -)
- Works cleanly in the EDSL
- Question raised: Should we add checked arithmetic helpers?

### Findings

**EDSL Capabilities Validated:**
1. **Arithmetic operations work naturally**
   - Lean's Nat supports + and - out of the box
   - Clean syntax: `current + 1`, `current - 1`
   - No special operators needed

2. **Stateful updates compose well**
   - Read-modify-write pattern is straightforward
   - Do-notation makes it readable
   - State changes are explicit

3. **Namespace strategy matters**
   - Need to avoid name conflicts as examples grow
   - Solution: Use full hierarchical namespaces (e.g., Examples.Counter)
   - Each example should be self-contained in its namespace

**Critical Design Question: Arithmetic Safety**

The Counter example reveals an important semantic question:

**Solidity 0.8+ behavior:**
- Reverts on overflow/underflow
- Safe by default
- Requires explicit `unchecked` blocks for wrapping behavior

**Lean/Nat behavior:**
- Nat subtraction saturates at 0 (5 - 10 = 0)
- No concept of underflow for natural numbers
- Different semantics from Uint256!

**Options going forward:**
1. **Accept semantic difference** - Document that Lean Nat != Solidity Uint256
2. **Add checked arithmetic** - Create stdlib helpers that enforce bounds
3. **Use a different type** - Create a proper Uint256 type with overflow checks
4. **Hybrid approach** - Keep simple for examples, add optional safety helpers

**Current recommendation**: Option 4 (Hybrid)
- Keep core minimal
- Add optional checked arithmetic helpers in stdlib
- Let examples choose their safety level
- Document the semantic differences clearly

### Complexity Metrics
- Core EDSL: 58 lines (unchanged)
- Counter Example: 50 lines (26 lines of actual code)
- Example-to-Core Ratio: 0.86 (slightly larger than SimpleStorage)
- Test coverage: 11 tests total, all passing
- Build time: ~2 seconds (Lean), ~20ms (Foundry tests)

### Namespace Strategy Established
- Core: `DumbContracts`
- Examples: `DumbContracts.Examples.<ContractName>`
- Each example in its own namespace prevents conflicts
- Pattern: One file, one contract, one namespace

### Next Iteration Ideas (Updated Priorities)

1. **Math Safety Helpers** (High Priority - revealed by Counter)
   - Add checked arithmetic to stdlib
   - Functions: safeAdd, safeSub, safeMul, safeDiv
   - Optional - examples can use basic + - or safe versions

2. **Ownership Pattern**
   - Introduce msg.sender checks
   - Add owner-only modifiers
   - Foundation for access control

3. **Better Storage Abstraction**
   - Consider mappings (Address → Uint256)
   - Multiple storage types (Bool, Address)
   - Generic storage operations

4. **Events**
   - Event emission support
   - Logging pattern
   - Observable state changes

### Files Modified This Iteration
- Created: DumbContracts/Examples/Counter.lean
- Created: contracts/Counter.sol
- Created: test/Counter.t.sol
- Modified: DumbContracts.lean (added Counter import)
- Modified: STATUS.md (updated for iteration 2)
- Modified: RESEARCH.md (this file)
