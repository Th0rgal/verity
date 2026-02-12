# Layer 1 Completion Roadmap

**Current Status**: 89% Complete (24/27 theorems proven)
**Last Updated**: 2026-02-12
**Target**: 100% Layer 1 completion

## Executive Summary

Layer 1 (EDSL ≡ ContractSpec) is nearly complete with excellent infrastructure in place. This document provides a clear roadmap for completing the final 11% (3 theorems) and transitioning to Layer 2.

### What's Complete ✅

- **Infrastructure**: SpecInterpreter (310 lines), Automation library (196 lines)
- **Contracts**: SimpleStorage (4/4), Counter (7/7)
- **Partial**: SafeCounter (6/8), Owned (7/8)
- **Documentation**: 1,100+ lines across README, SUMMARY, LAYER1_STATUS
- **Safe Arithmetic**: 6 proven lemmas for safeAdd/safeSub
- **Build Status**: Zero errors, all files compile

### What Remains ⚠️

Three theorems requiring specific automation infrastructure:

1. **SafeCounter.safeIncrement_correct** - Modular arithmetic wraparound
2. **SafeCounter.safeDecrement_correct** - Option.bind automation
3. **Owned.only_owner_can_transfer** - Monadic authorization patterns

## Detailed Completion Plan

### Phase 1: Automation Infrastructure (3-5 days)

#### Task 1.1: Modular Arithmetic Wraparound Lemma ✅ COMPLETE
**For**: `SafeCounter.safeIncrement_correct`

**Status**: ✅ **COMPLETED** (commit ce89ee3)

**Proven Lemma**:
```lean
theorem add_one_preserves_order_iff_no_overflow (a : Uint256) :
    ((a + 1) : Uint256).val > a.val ↔ a.val < MAX_UINT256
```

**Implementation**:
1. Case split on `a.val = MAX_UINT256` vs `a.val < MAX_UINT256`
2. Overflow case: prove `(MAX + 1) mod 2^256 = 0` and `0 ≯ MAX` (contradiction)
3. Non-overflow case: prove `a + 1 < modulus` so mod is identity, order preserved

**Result**: 50-line proven lemma, zero errors
**File**: `Compiler/Proofs/Automation.lean` (lines 312-361)

**Key Insights**:
- Ethereum addresses overflow as: `2^256 - 1 + 1 ≡ 0 (mod 2^256)`
- This is the only case where addition breaks monotonicity
- Successfully proven using case analysis + Nat.mod_eq_of_lt

---

#### Task 1.2: Option.bind Success Propagation ✅ COMPLETE
**For**: `SafeCounter.safeDecrement_correct`, `Owned.only_owner_can_transfer`

**Status**: ✅ **COMPLETED** (commit d52a3ca)

**Proven Lemma**:
```lean
theorem bind_isSuccess_left {α β} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((bind m1 m2).run state).isSuccess = true →
    (m1.run state).isSuccess = true
```

**Implementation**:
1. Case analysis on `m1 state` (success vs revert)
2. Success case: trivially true by simplification
3. Revert case: bind propagates revert → contradiction

**Result**: Clean 9-line proof, zero errors
**File**: `Compiler/Proofs/Automation.lean` (lines 91-104)

**Note**: `bind_success_decompose` not needed - `bind_isSuccess_left` is sufficient for current proofs.

---

#### Task 1.3: Require Condition Extraction ✅ COMPLETE
**For**: `Owned.only_owner_can_transfer`

**Status**: ✅ **COMPLETED** (commit 0cfb3f3)

**Implemented Lemma**:
```lean
-- If require succeeds, condition was true
theorem require_success_implies_cond (cond : Bool) (msg : String) (state : ContractState) :
    ((require cond msg).run state).isSuccess = true →
    cond = true
```

**Implementation**:
1. Case analysis on `cond`
2. When `cond = false`: require returns revert, isSuccess = false (contradiction)
3. When `cond = true`: trivial by reflexivity

**Result**: Clean 8-line proof, zero errors
**File**: `Compiler/Proofs/Automation.lean` (lines 167-179)

---

#### Task 1.4: Boolean Equality for Addresses ✅ COMPLETE
**For**: `Owned.only_owner_can_transfer`

**Status**: ✅ **COMPLETED** (commit 333f693)

**Proven Lemma**:
```lean
theorem address_beq_eq_true_iff_eq (a b : Address) :
    (a == b) = true ↔ a = b
```

**Implementation**:
- Uses `simp only [beq_iff_eq]` from Lean standard library
- Address is String, leverages String's BEq instance
- Provides bidirectional equivalence

**Result**: Minimal 3-line proof, zero errors
**File**: `Compiler/Proofs/Automation.lean` (lines 187-196)

---

### Phase 2: Complete SafeCounter Proofs (2-3 days)

#### Task 2.1: Prove safeIncrement_correct

**Strategy**:
```lean
theorem safeIncrement_correct (state : ContractState) (sender : Address) :
    let edslResult := increment.run { state with sender := sender }
    let specResult := interpretSpec safeCounterSpec ... specTx
    (edslResult.isSuccess = true ↔ specResult.success = true) ∧
    (edslResult.isSuccess = true →
      specResult.finalStorage.getSlot 0 = (edslResult.getState.storage 0).val) := by
  by_cases h : (state.storage 0).val = MAX_UINT256
  case pos =>
    -- Overflow case: both fail
    -- EDSL: safeAdd returns None
    -- Spec: require (newCount > count) fails because (MAX+1) mod 2^256 = 0 ≯ MAX
    use safeIncrement_reverts_at_max (proven)
    use add_one_preserves_order_iff_no_overflow (Task 1.1)
  case neg =>
    -- No overflow: both succeed with same result
    use safeAdd_some_iff_le (proven)
    use add_one_preserves_order_iff_no_overflow (Task 1.1)
```

**Dependencies**: Task 1.1
**Estimated Effort**: 1 day (after automation)
**File**: `Compiler/Proofs/SpecCorrectness/SafeCounter.lean`

---

#### Task 2.2: Prove safeDecrement_correct

**Strategy**:
```lean
theorem safeDecrement_correct (state : ContractState) (sender : Address) :
    ... := by
  by_cases h : (state.storage 0).val = 0
  case pos =>
    -- Underflow case: both fail
    use safeDecrement_reverts_at_zero (proven)
  case neg =>
    -- No underflow: both succeed
    use safeSub_some_iff_ge (proven)
    use bind_success_decompose (Task 1.2)
```

**Dependencies**: Task 1.2
**Estimated Effort**: 1 day (after automation)
**File**: `Compiler/Proofs/SpecCorrectness/SafeCounter.lean`

---

### Phase 3: Complete Owned Proof (1-2 days)

#### Task 3.1: Prove only_owner_can_transfer ⚠️ BLOCKED

**Status**: ⚠️ **BLOCKED** - Requires tactic composition infrastructure

**Challenge Identified** (commit 73380fd):
While all needed automation lemmas exist (Tasks 1.2, 1.3, 1.4), applying them
requires navigating deep monadic structure:

```lean
transferOwnership = onlyOwner >> setStorageAddr owner newOwner
  where onlyOwner = isOwner >>= λcheck => require check msg
    where isOwner = msgSender >>= λs => getStorageAddr o >>= λo => pure (s == o)
```

**Issue**: Direct application of automation lemmas creates complex intermediate
goals that require sophisticated simplification tactics.

**Solution Options**:
1. **Build tactic composition layer** (~1-2 days)
   - Create authorization-specific automation
   - Compose bind_isSuccess_left + require_success_implies_cond + address_beq_eq_true_iff_eq
   - Handle intermediate goal simplification

2. **Manual proof term construction** (~1 day)
   - Brittle but possible
   - Not recommended for maintainability

3. **Lean metaprogramming** (~2-3 days)
   - Most robust solution
   - Create custom tactics for monadic authorization patterns

**Recommendation**: Build tactic composition layer (Option 1) before attempting this proof.

**Dependencies**: Tasks 1.2 ✅, 1.3 ✅, 1.4 ✅, + Tactic Composition
**Estimated Effort**: 0.5 days (after tactic infrastructure)
**File**: `Compiler/Proofs/SpecCorrectness/Owned.lean`

---

### Phase 1.5: Tactic Composition Infrastructure (NEW - 1-2 days)

**Discovery** (2026-02-12): While individual automation lemmas (Tasks 1.2-1.4) are
complete, **composing them in complex monadic contexts requires additional infrastructure**.

**Needed**: Higher-level automation that chains lemmas together.

#### Task 1.5: Build Authorization Tactic

**Goal**: Create automation that composes bind_isSuccess_left, require_success_implies_cond,
and address_beq_eq_true_iff_eq into a single authorization pattern handler.

**Approach**:
```lean
-- High-level tactic that handles: (auth_check >> operation).isSuccess = true → condition
tactic authorization_from_success :
  1. Apply bind_isSuccess_left to extract auth check success
  2. Unfold auth check definition
  3. Apply require_success_implies_cond to extract condition
  4. Apply address_beq_eq_true_iff_eq (or similar) to convert beq
  5. Handle intermediate simplifications
```

**Benefits**:
- Unlocks Task 3.1 (only_owner_can_transfer)
- Unlocks Task 2.2 (safeDecrement_correct)
- Establishes pattern for future authorization proofs

**Estimated Effort**: 1-2 days
**Priority**: HIGH - blocks 2 remaining theorems

---

## Timeline Summary

### Week 1: Automation Infrastructure
- **Days 1-2**: Task 1.1 (Modular arithmetic wraparound) - PENDING
- **Day 3**: ~~Task 1.2 (Option.bind automation)~~ → ✅ COMPLETE
- **Day 4**: ~~Tasks 1.3 + 1.4 (Require and beq lemmas)~~ → ✅ BOTH COMPLETE
- **Day 5**: Testing

### Progress Update (2026-02-12 - Latest)
- ✅ Task 1.1 completed (add_one_preserves_order_iff_no_overflow) - JUST COMPLETED
- ✅ Task 1.2 completed (bind_isSuccess_left)
- ✅ Task 1.3 completed (require_success_implies_cond)
- ✅ Task 1.4 completed (address_beq_eq_true_iff_eq)
- **Base automation: 100% complete (4/4 tasks)** ✅
- 🔍 **Discovery**: Need tactic composition layer (Task 1.5) for remaining 2 theorems
- Remaining: Task 1.5 (Tactic composition) only

### Revised Timeline

**Week 1-2: Complete Infrastructure**
- **Days 1-2**: Task 1.1 (Modular arithmetic wraparound)
- **Days 3-4**: Task 1.5 (Tactic composition for authorization)
- **Day 5**: Testing

**Week 2: Complete Remaining Proofs**
- **Day 1**: Task 2.1 (safeIncrement_correct) - needs Task 1.1
- **Day 2**: Task 2.2 (safeDecrement_correct) - needs Task 1.5
- **Day 3**: Task 3.1 (only_owner_can_transfer) - needs Task 1.5
- **Days 4-5**: Final testing, documentation, cleanup

**Total Estimated Time**: 2-2.5 weeks for one developer

---

## Success Criteria

### Definition of Done

**Layer 1 Complete** when:
- ✅ All 27 theorems proven (no `sorry`)
- ✅ All files compile with zero errors
- ✅ Automation library is complete and documented
- ✅ All proofs follow established patterns
- ✅ README and documentation updated
- ✅ PR review comments addressed

### Quality Standards

All proofs must:
1. **Be maintainable**: Clear structure, well-commented
2. **Follow patterns**: Reuse existing automation
3. **Be well-documented**: Explain key insights
4. **Build cleanly**: No warnings on strategic lemmas
5. **Be tested**: Verify with `lake build`

---

## Risk Assessment

### Low Risk ✅

- **Automation infrastructure**: Well-scoped, clear approach
- **Proof strategies**: Already sketched in comments
- **Build system**: Stable, zero current errors
- **Team knowledge**: Patterns established

### Medium Risk ⚠️

- **Modular arithmetic complexity**: Task 1.1 may need deeper Uint256 reasoning
  - **Mitigation**: Consult Lean 4 Mathlib for nat modulo properties
- **Nested bind chains**: Task 1.2 involves multiple levels
  - **Mitigation**: Prove incrementally, add intermediate lemmas

### Mitigation Strategies

1. **Break down complex proofs**: Add helper lemmas as needed
2. **Test incrementally**: Build after each subtask
3. **Document challenges**: Update this roadmap if approach changes
4. **Ask for help**: Lean Zulip community for modular arithmetic

---

## Post-Layer 1: Transition to Layer 2

### Layer 2 Prep (Parallel with Layer 1 completion)

While completing Layer 1, begin:

1. **Study IR structure**: Understand `Compiler/IR.lean`
2. **Design IR interpreter**: Sketch `interpretIR` semantics
3. **Identify translation patterns**: How ContractSpec→IR works
4. **Plan proof structure**: Organize IRGeneration/ directory

### Layer 2 Kickoff (After Layer 1)

**Prerequisites**:
- ✅ Layer 1 at 100%
- ✅ Automation library finalized
- ✅ IR interpreter implemented
- ✅ Layer 2 proof structures created

**First Layer 2 Task**: Prove expression translation correctness
- File: `Compiler/Proofs/IRGeneration/Expr.lean`
- Goal: `interpretIR_Expr (toIR_Expr e) = evalExpr e`
- Estimated: 1 week

---

## Appendix: Alternative Approaches

### If Automation Proves Too Complex

**Option A**: Axiomatize complex properties
- Add `axiom` declarations for modular arithmetic facts
- Document trust assumptions
- Revisit later with external automation (e.g., omega solver)

**Option B**: Simplify theorem statements
- Weaken correctness guarantees temporarily
- Prove weaker versions first
- Strengthen incrementally

**Recommendation**: Stick with main plan. If stuck >2 days on one lemma, raise flag and consider alternatives.

---

## Contact & Resources

**Documentation**:
- README: `Compiler/Proofs/README.md`
- Status: `Compiler/Proofs/LAYER1_STATUS.md`
- Summary: `Compiler/Proofs/SUMMARY.md`

**Code**:
- Automation: `Compiler/Proofs/Automation.lean`
- Proofs: `Compiler/Proofs/SpecCorrectness/*.lean`

**External Resources**:
- Lean 4 Zulip: [https://leanprover.zulipchat.com/](https://leanprover.zulipchat.com/)
- Mathlib Docs: [https://leanprover-community.github.io/mathlib4_docs/](https://leanprover-community.github.io/mathlib4_docs/)

---

**Status**: Base automation complete (100%)
**Next Action**: Complete SafeCounter.safeIncrement_correct proof using Task 1.1 lemma
