# Dumb Contracts Research Status

## Current Iteration: Verification Iteration 4 - SimpleToken (2026-02-10)

### Goal
Add formal verification to SimpleToken, proving complex invariants. Verify that token operations preserve total supply, maintain balance invariants, and correctly implement ERC20-like transfer semantics.

### What I'm About to Do

1. **Create specification files** (DumbContracts/Specs/SimpleToken/):
   - `Spec.lean` - Formal specification of mint, transfer, balanceOf, totalSupply
   - `Invariants.lean` - State invariants (supply = sum of balances, non-negative balances)

2. **Create proof files** (DumbContracts/Proofs/SimpleToken/):
   - `Basic.lean` - Prove token correctness
   - Prove: totalSupply equals sum of all balances
   - Prove: transfer preserves total supply
   - Prove: mint increases total supply correctly
   - Prove: balances remain non-negative

3. **Document proof strategy**:
   - Complex invariant proofs (supply = sum of balances)
   - Cross-operation properties
   - Access control for mint (Owned pattern)
   - Balance preservation properties

### Why This Approach

SimpleToken verification is the next logical step because:
- Most complex contract so far (combines storage, arithmetic, access control)
- Tests verification of complex invariants (supply = sum of balances)
- Realistic token contract (ERC20-like)
- Combines patterns from previous iterations (Owned, Counter, storage)

### Current State
- Previous: Owned verification complete (16 theorems proven, 2 with axioms)
- Core: 82 lines, stable
- Examples: 7 contracts (all runtime-tested)
- Verification: SimpleStorage (11 theorems), Counter (17 theorems), Owned (16 theorems) complete

### Expected Outcomes
- Specs/SimpleToken/ directory with formal specifications
- Proofs/SimpleToken/ directory with proven theorems
- At least 6 complete proofs (supply invariant + transfer correctness)
- Documentation of complex invariant proof strategies
- Foundation for realistic token contracts

### Next Steps After This Iteration
- OwnedCounter verification (composition of Owned + Counter patterns)
- Extended verification (overflow, require modeling, access control enforcement)

---

## Previous Work

### Verification Phase

**Iteration 1: SimpleStorage** ✅ Complete
- 11 theorems proven
- store_retrieve_correct proven
- Foundation established
- See VERIFICATION_ITERATION_1_SUMMARY.md

**Iteration 2: Counter** ✅ Complete
- 17 theorems proven
- increment_adds_one, decrement_subtracts_one proven
- Composition properties proven (increment_twice_adds_two, increment_decrement_cancel)
- See VERIFICATION_ITERATION_2_SUMMARY.md

**Iteration 3: Owned** ✅ Complete
- 16 theorems proven (2 with axioms for require modeling)
- constructor_sets_owner, getOwner_returns_owner, isOwner_returns_correct_value proven
- Access control verification foundation established
- See VERIFICATION_ITERATION_3_SUMMARY.md

### Implementation Phase Complete

**7 iterations completed** (see RESEARCH.md for full details):
1. Bootstrap - 58-line minimal core
2. Counter - Arithmetic operations
3. Owned - Access control (+14 lines)
4. OwnedCounter - Pattern composition
5. Math Safety Stdlib - Extensibility
6. Mapping Support - Key-value storage (+13 lines)
7. SimpleToken - Realistic token contract

**Current State**: 82-line core, 7 examples, 62 tests (100% passing), 44 proofs (SimpleStorage + Counter + Owned)

**New Phase**: Formal verification via Lean proofs (SimpleToken in progress)
