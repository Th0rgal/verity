# DumbContracts Compiler Roadmap — Trustworthy, Simple, Auditable

PR you are working on: https://github.com/Th0rgal/dumbcontracts/pull/11

Mission: Turn the EDSL→EVM compiler into a generic, well‑tested, and eventually verified pipeline that is easy to audit and maintain.

Current state:
- ✅ Item 1 complete: Generic compilation working
- ✅ Item 2 core complete: Differential testing infrastructure for 3 contracts
- ⚠️ **CRITICAL**: Type system semantic mismatch discovered (see Item 2.5)
- All 88 tests passing, 252 proofs verified

Other agents are working on it: always pull the latest changes, review them, and check the pull request reviews that will report bugs and improvements you will need to fix or answer before starting. Additionally run foundry tests and lake build to detect additional issues.

---

## Priorities (in order):

### 1) ✅ Generic compilation (no manual Translate.lean) - COMPLETE
   - Parse contract AST, infer storage, compute selectors (keccak)
   - Auto‑generate IR for all contracts
   - Fail fast on spec errors

   **Success criteria**: ✅ `lake exe compile --all` works for every contract + new contract compiles without Translate edits

   **Status**: Complete. All 7 contracts compile automatically from declarative specs. 76 original Foundry tests + 12 differential tests passing.

---

### 2) 🔄 Differential testing (trust before proofs) - CORE COMPLETE
   - ✅ Lean interpreter + random transaction generator
   - ✅ Compare interpreter vs EVM results (storage, returns, reverts)
   - ✅ Foundry vm.ffi integration with proper state tracking
   - ✅ 100/100 random tests passing for SimpleStorage, Counter, SafeCounter
   - ⏳ Extend to remaining 5 contracts
   - ⏳ Scale to 10k+ tests per contract in CI

   **Success criteria**: Zero mismatches across all contracts at 10k+ tests per contract

   **Status**: Core infrastructure complete. 3/7 contracts have differential tests. Need to extend to Owned, Ledger, OwnedCounter, SimpleToken, then scale up test count.

   **Blockers**: None - infrastructure is solid and working.

---

### 2.5) ⚠️ **EVM Type System Compatibility (NEWLY DISCOVERED - HIGH PRIORITY)**
   **Problem**: EDSL uses `Uint256 := Nat` (unbounded) but EVM uses modular 256-bit arithmetic. This creates a semantic mismatch where:
   - EDSL: `2^256 - 1 + 2 = 2^256 + 1` (mathematically correct)
   - EVM: `2^256 - 1 + 2 = 1` (wraps at 2^256)

   **Impact**:
   - 6/7 contracts vulnerable to overflow/underflow semantic mismatches
   - Verification doesn't match execution behavior
   - Differential testing WILL catch this (which is good!), but we need to fix the root cause

   **Solution**: Implement modular arithmetic with EVM-compatible semantics

   **Tasks**:

   #### Phase 1: Add EVM-Compatible Operations (Week 1)
   - Create `DumbContracts/Core/Uint256.lean` with modular operations:
     - `Uint256.add/sub/mul/div` with wrapping at 2^256
     - Overflow detection predicates: `willAddOverflow`, `willSubUnderflow`, `willMulOverflow`
     - Match EVM semantics: `div 0` returns 0, subtraction uses two's complement
   - Add basic lemmas for modular arithmetic reasoning

   #### Phase 2: Update Compiler (Week 1-2)
   - Modify `Compiler/ContractSpec.lean` to emit modular operations
   - Add `mul`, `div`, `mod` to DSL expression types (currently only `add`/`sub`)
   - Update Yul emission to match EVM opcodes exactly
   - Validate with differential tests - should catch any mismatches

   #### Phase 3: Migrate Examples (Week 2)
   - Update contracts to use `Uint256.add/sub/mul/div` instead of raw `+`/`-`/`*`/`/`
   - Order: Counter → SimpleStorage → Owned → OwnedCounter → Ledger → SimpleToken → SafeCounter
   - SafeCounter: prove overflow predicates show no wrapping occurs
   - Re-run all 88 Foundry tests (should pass)
   - Re-run differential tests (should pass with zero mismatches)

   #### Phase 4: Update Proofs (Week 2-3)
   - Add modular arithmetic lemmas to `DumbContracts/Stdlib/Math.lean`
   - Migrate 252 proofs to reason about bounded operations
   - Add overflow-freedom proofs where contracts guarantee no wrapping
   - Most proofs should work with minimal changes (Nat operations still valid for reasoning)

   #### Phase 5: Add Missing EVM Features (Week 3-4)
   - **EVM Context** (HIGH priority):
     - `msg.value`, `msg.sender`, `tx.origin`, `tx.gasprice`
     - `block.timestamp`, `block.number`, `block.difficulty`, `block.coinbase`
     - `address(this).balance`, `gasleft()`
   - **Bitwise Operations** (MEDIUM priority):
     - `&` (AND), `|` (OR), `^` (XOR), `~` (NOT), `<<` (SHL), `>>` (SHR)
   - **Additional Integer Types** (LOW priority - defer):
     - `Uint8`, `Uint16`, `Uint32`, `Uint64`, `Uint128`
     - `Int8`, `Int16`, `Int32`, `Int64`, `Int128`, `Int256`

   **Success criteria**:
   - ✅ All arithmetic operations have EVM-compatible semantics
   - ✅ Differential tests pass with zero mismatches (validates semantic equivalence)
   - ✅ All 252 proofs still verify
   - ✅ All 88+ tests still pass
   - ✅ Can express realistic contracts (time-locks, payable functions)

   **Why now**: This is blocking trust in the compiler. Without EVM-compatible types:
   - Verification doesn't apply to compiled contracts
   - Differential testing will catch mismatches (good) but we need the fix
   - Cannot safely express standard patterns (ERC20 with overflow protection)

   **Dependencies**:
   - Differential testing infrastructure (complete) - will validate the fix
   - Should do Phase 1-3 before scaling differential testing to 10k+ tests

   **Estimated effort**: 2-3 weeks (can overlap with differential testing extension)

---

### 3) Property extraction (proofs → tests) - NOT STARTED
   - Convert proven theorems to Foundry tests
   - Generate test cases from preconditions
   - Validate that proofs translate to executable checks

   **Success criteria**: All 252 theorems produce passing Foundry tests

   **Status**: Not started. Blocked by Items 2 and 2.5 completion.

   **Dependencies**: Need type system fix (Item 2.5) so proofs match execution.

---

### 4) Compiler verification (long‑term) - NOT STARTED
   - Prove compiled EVM matches EDSL semantics
   - Formalize Yul semantics in Lean
   - Prove IR → Yul transformation preserves semantics
   - Prove EDSL → IR transformation preserves semantics

   **Success criteria**: `lake build Compiler.Proofs` has zero `sorry`

   **Status**: Not started. Long-term goal after practical trust established.

   **Dependencies**: Items 2, 2.5, and 3 complete.

---

## Current Issues Summary

### Type System Issues (Item 2.5)
1. ⚠️ **HIGH**: Missing EVM arithmetic semantics - `Uint256 := Nat` doesn't wrap
2. 🔶 **MEDIUM**: Incomplete DSL arithmetic - only `add`/`sub`, missing `mul`/`div`/`mod`
3. ⚠️ **HIGH**: No EVM context access - cannot express `msg.value`, `block.timestamp`, etc.
4. 🔶 **MEDIUM**: Missing bitwise operations - cannot express masks, shifts
5. 🔶 **MEDIUM**: Limited numeric types - only `Uint256`, no `Uint8`/`Int256`/etc.
6. 🔶 **MEDIUM**: Safe math underutilized - opt-in only, most contracts don't use it

### Migration Strategy
**Approach**: Modular arithmetic (Option 2) - best EVM compatibility
- Keep `Uint256 := Nat` for flexibility
- Add `Uint256.add/sub/mul/div` with wrapping semantics
- Provide overflow predicates for safety proofs
- Most proofs work with minimal changes
- Perfect semantic equivalence with EVM

**Why this approach**:
- ✅ EVM compatibility is critical (per project requirements)
- ✅ Differential testing validates semantic equivalence
- ✅ Manageable migration (2-3 weeks)
- ✅ Preserves most existing proofs
- ✅ Explicit about overflow behavior

---

## Non‑goals
- Optimize gas costs
- Mimic Solidity quirks or edge cases
- Add unproven EDSL features
- Support non-EVM targets (yet)

## Trust model
- Prefer simple specs over complex optimizations
- Minimal surface area for auditing
- Strict error handling (fail fast on invalid input)
- Reusable stdlib with proven properties
- Differential testing validates compiler correctness
- **NEW**: EVM-compatible semantics ensure verification matches execution

---

## Workflow Reminders

1. **Always pull latest changes first**: `git pull origin feat/generic-compilation`
2. **Check PR reviews**: `gh pr view 11` - fix any Bugbot issues
3. **Run tests before committing**:
   - `lake build` (verify proofs)
   - `forge test` (verify contracts)
4. **Commit and push progress**: Don't leave uncommitted work
5. **Update this roadmap**: Mark items complete, add new findings

---

## Current Metrics

| Metric | Value |
|--------|-------|
| Contracts with differential tests | 3/7 (SimpleStorage, Counter, SafeCounter) |
| Random tests passing | 100/100 per contract (300 total) |
| Differential test mismatches | 0 |
| Foundry tests passing | 88/88 (100%) |
| Lean proofs verified | 252/252 (100%) |
| Manual IR lines eliminated | 266 → 0 |
| Contracts using EVM-compatible types | 0/7 (needs Item 2.5) |

---

## Next Actions (Priority Order)

1. **IMMEDIATE**: Implement Item 2.5 Phase 1 - Add modular arithmetic operations
   - Create `DumbContracts/Core/Uint256.lean`
   - Add `Uint256.add/sub/mul/div` with EVM wrapping semantics
   - Add overflow detection predicates

2. **Week 1-2**: Complete Item 2.5 Phases 2-3
   - Update compiler to emit modular ops
   - Migrate all 7 example contracts
   - Validate with differential tests

3. **Week 2-3**: Complete Item 2.5 Phase 4
   - Update proofs for modular arithmetic
   - Add overflow-freedom proofs for SafeCounter

4. **Week 3**: Extend differential testing (Item 2 completion)
   - Add tests for remaining 4 contracts
   - Scale to 1000+ tests per contract

5. **Week 4**: Complete Item 2.5 Phase 5 + Item 2 completion
   - Add EVM context primitives
   - Add bitwise operations
   - Scale differential tests to 10k+ per contract

---

**Last Updated**: 2026-02-10
**Current Focus**: Item 2.5 (EVM Type System Compatibility) - discovered during differential testing work
