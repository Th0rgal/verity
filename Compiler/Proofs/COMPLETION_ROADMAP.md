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

#### Task 1.1: Modular Arithmetic Wraparound Lemma
**For**: `SafeCounter.safeIncrement_correct`

**Needed Lemma**:
```lean
theorem add_one_preserves_order_iff_no_overflow (a : Uint256) :
    ((a + 1) : Uint256).val > a.val ↔ a.val < MAX_UINT256
```

**Approach**:
1. Unfold Uint256.add to expose modular arithmetic
2. Case split on `a.val = MAX_UINT256` vs `a.val < MAX_UINT256`
3. In overflow case: show `(MAX + 1) mod 2^256 = 0`, and `0 ≯ MAX` (contradiction)
4. In non-overflow case: show `a + 1` doesn't wrap, so order preserved

**Estimated Effort**: 1-2 days
**File**: `Compiler/Proofs/Automation.lean`

**Key Insights**:
- Ethereum addresses overflow as: `2^256 - 1 + 1 ≡ 0 (mod 2^256)`
- This is the only case where addition breaks monotonicity
- Once proven, immediately unlocks `safeIncrement_correct`

---

#### Task 1.2: Option.bind Success Propagation
**For**: `SafeCounter.safeDecrement_correct`, `Owned.only_owner_can_transfer`

**Needed Lemmas**:
```lean
-- If bind succeeds, first action succeeded
theorem bind_isSuccess_left {α β} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((bind m1 m2).run state).isSuccess = true →
    (m1.run state).isSuccess = true

-- Extract value from successful first action
theorem bind_success_decompose {α β} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((bind m1 m2).run state).isSuccess = true →
    ∃ val s, m1.run state = ContractResult.success val s ∧
             ((m2 val).run s).isSuccess = true
```

**Approach**:
1. Unfold `bind` definition
2. Case analysis on `m1.run state`
3. In `success` case: extract value and continue
4. In `revert` case: show bind reverts (contradiction with hypothesis)

**Estimated Effort**: 1 day
**File**: `Compiler/Proofs/Automation.lean`

**Note**: `bind_isSuccess_left` already has skeleton in Automation.lean (line 91), just needs completion.

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

#### Task 1.4: Boolean Equality for Addresses
**For**: `Owned.only_owner_can_transfer`

**Needed Lemma**:
```lean
-- Address beq reflects equality
theorem address_beq_eq_true_iff_eq (a b : Address) :
    (a == b) = true ↔ a = b
```

**Approach**:
- Since Address is String, use String.beq properties
- Forward direction: `(a == b) = true → a = b` (from beq definition)
- Reverse direction: `a = b → (a == b) = true` (reflexivity)

**Estimated Effort**: 0.5 days
**File**: `Compiler/Proofs/Automation.lean`

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

#### Task 3.1: Prove only_owner_can_transfer

**Strategy**:
```lean
theorem only_owner_can_transfer (state : ContractState) (newOwner : Address) (sender : Address) :
    let result := (transferOwnership newOwner).run { state with sender := sender }
    result.isSuccess = true → state.storageAddr 0 = sender := by
  intro h_success

  -- transferOwnership = onlyOwner >> setStorageAddr owner newOwner
  -- onlyOwner = msgSender >>= λs => getStorageAddr owner >>= λo =>
  --             require (s == o) >> return ()

  -- Step 1: Extract that onlyOwner succeeded
  have h_onlyOwner : (onlyOwner.run ...).isSuccess = true :=
    bind_isSuccess_left h_success  -- Task 1.2

  -- Step 2: Decompose onlyOwner to get require success
  have h_require : ... :=
    bind_success_decompose h_onlyOwner  -- Task 1.2 (applied twice)

  -- Step 3: Extract condition from require
  have h_cond : sender == state.storageAddr 0 = true :=
    require_success_implies_cond h_require  -- Task 1.3

  -- Step 4: Convert beq to equality
  exact address_beq_eq_true_iff_eq.mp h_cond  -- Task 1.4
```

**Dependencies**: Tasks 1.2, 1.3, 1.4
**Estimated Effort**: 1 day (after automation)
**File**: `Compiler/Proofs/SpecCorrectness/Owned.lean`

---

## Timeline Summary

### Week 1: Automation Infrastructure
- **Days 1-2**: Task 1.1 (Modular arithmetic wraparound) - PENDING
- **Day 3**: Task 1.2 (Option.bind automation) - PENDING
- **Day 4**: ~~Tasks 1.3 + 1.4 (Require and beq lemmas)~~ → Task 1.3 ✅ COMPLETE
- **Day 5**: Task 1.4 (Boolean equality) + Testing

### Progress Update (2026-02-12)
- ✅ Task 1.3 completed ahead of schedule
- Remaining: Tasks 1.1, 1.2, 1.4 (3 tasks)

### Week 2: Complete Remaining Proofs
- **Day 1**: Task 2.1 (safeIncrement_correct)
- **Day 2**: Task 2.2 (safeDecrement_correct)
- **Day 3**: Task 3.1 (only_owner_can_transfer)
- **Days 4-5**: Final testing, documentation, cleanup

**Total Estimated Time**: 2 weeks for one developer

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

**Status**: Ready to execute
**Next Action**: Begin Task 1.1 (Modular arithmetic wraparound lemma)
