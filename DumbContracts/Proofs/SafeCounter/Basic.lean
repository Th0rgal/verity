/-
  Correctness proofs for SafeCounter contract.

  Proves checked arithmetic operations:
  - increment succeeds when no overflow, reverts on overflow
  - decrement succeeds when no underflow, reverts on underflow
  - getCount returns correct value
  - State preservation and well-formedness
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math
import DumbContracts.Examples.SafeCounter
import DumbContracts.Specs.SafeCounter.Spec
import DumbContracts.Specs.SafeCounter.Invariants

namespace DumbContracts.Proofs.SafeCounter

open DumbContracts
open DumbContracts.Stdlib.Math
open DumbContracts.Examples.SafeCounter
open DumbContracts.Specs.SafeCounter

/-! ## getCount Correctness -/

theorem getCount_meets_spec (s : ContractState) :
  let result := ((getCount).run s).fst
  getCount_spec result s := by
  simp [getCount, getStorage, count, getCount_spec, Contract.run, ContractResult.fst]

theorem getCount_returns_count (s : ContractState) :
  ((getCount).run s).fst = s.storage 0 := by
  simp [getCount, getStorage, count, Contract.run, ContractResult.fst]

theorem getCount_preserves_state (s : ContractState) :
  ((getCount).run s).snd = s := by
  simp [getCount, getStorage, count, Contract.run, ContractResult.snd]

/-! ## Increment Correctness -/

/-- Helper: safeAdd succeeds when no overflow -/
private theorem safeAdd_some (a b : Uint256) (h : a + b ≤ MAX_UINT256) :
  safeAdd a b = some (a + b) := by
  simp only [safeAdd]
  have h_not : ¬(a + b > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- Helper: safeAdd fails on overflow -/
private theorem safeAdd_none (a b : Uint256) (h : a + b > MAX_UINT256) :
  safeAdd a b = none := by
  simp only [safeAdd]
  simp [h]

/-- Helper: safeSub succeeds when no underflow -/
private theorem safeSub_some (a b : Uint256) (h : a ≥ b) :
  safeSub a b = some (a - b) := by
  simp only [safeSub]
  have h_not : ¬(b > a) := Nat.not_lt.mpr h
  simp [h_not]

/-- Helper: safeSub fails on underflow -/
private theorem safeSub_none (a b : Uint256) (h : b > a) :
  safeSub a b = none := by
  simp only [safeSub]
  simp [h]

/-- Helper: unfold increment when no overflow -/
private theorem increment_unfold (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  (increment).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 0) = true then s.storage 0 + 1 else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  have h_safe := safeAdd_some (s.storage 0) 1 h_no_overflow
  simp only [increment, getStorage, setStorage, count, requireSomeUint,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_safe]

theorem increment_meets_spec (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  increment_spec s s' := by
  rw [increment_unfold s h_no_overflow]
  simp only [ContractResult.snd, increment_spec]
  refine ⟨by simp, ?_, trivial, trivial, trivial, trivial⟩
  intro slot h_ne
  simp [beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem increment_adds_one (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  s'.storage 0 = s.storage 0 + 1 := by
  rw [increment_unfold s h_no_overflow]; simp [ContractResult.snd]

theorem increment_preserves_other_slots (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256)
  (slot : Nat) (h_ne : slot ≠ 0) :
  let s' := ((increment).run s).snd
  s'.storage slot = s.storage slot := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem increment_reverts_overflow (s : ContractState)
  (h_overflow : s.storage 0 + 1 > MAX_UINT256) :
  ∃ msg, (increment).run s = ContractResult.revert msg s := by
  have h_none := safeAdd_none (s.storage 0) 1 h_overflow
  simp [increment, getStorage, setStorage, count, requireSomeUint,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    DumbContracts.require, Contract.run, ContractResult.snd, ContractResult.fst,
    h_none]

/-! ## Decrement Correctness -/

/-- Helper: unfold decrement when no underflow -/
private theorem decrement_unfold (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  (decrement).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 0) = true then s.storage 0 - 1 else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  have h_safe := safeSub_some (s.storage 0) 1 h_no_underflow
  simp only [decrement, getStorage, setStorage, count, requireSomeUint,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_safe]

theorem decrement_meets_spec (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  decrement_spec s s' := by
  rw [decrement_unfold s h_no_underflow]
  simp only [ContractResult.snd, decrement_spec]
  refine ⟨by simp, ?_, trivial, trivial, trivial, trivial⟩
  intro slot h_ne
  simp [beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem decrement_subtracts_one (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  s'.storage 0 = s.storage 0 - 1 := by
  rw [decrement_unfold s h_no_underflow]; simp [ContractResult.snd]

theorem decrement_preserves_other_slots (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1)
  (slot : Nat) (h_ne : slot ≠ 0) :
  let s' := ((decrement).run s).snd
  s'.storage slot = s.storage slot := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd, beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem decrement_reverts_underflow (s : ContractState)
  (h_underflow : s.storage 0 = 0) :
  ∃ msg, (decrement).run s = ContractResult.revert msg s := by
  have h_gt : 1 > s.storage 0 := by rw [h_underflow]; decide
  have h_none := safeSub_none (s.storage 0) 1 h_gt
  simp [decrement, getStorage, setStorage, count, requireSomeUint,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    DumbContracts.require, Contract.run, ContractResult.snd, ContractResult.fst,
    h_none]

/-! ## State Preservation -/

theorem increment_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  WellFormedState s' := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

theorem decrement_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  WellFormedState s' := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

/-! ## Bounds Preservation -/

theorem increment_preserves_bounds (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  count_in_bounds s' := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, count_in_bounds]
  exact h_no_overflow

theorem decrement_preserves_bounds (s : ContractState)
  (h_bounds : count_in_bounds s)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  count_in_bounds s' := by
  rw [decrement_unfold s h_no_underflow]
  simp only [ContractResult.snd, count_in_bounds]
  simp only [count_in_bounds] at h_bounds
  exact Nat.le_trans (Nat.sub_le (s.storage 0) 1) h_bounds

/-! ## Composition: increment → getCount -/

theorem increment_getCount_correct (s : ContractState)
  (h_no_overflow : s.storage 0 + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  ((getCount).run s').fst = s.storage 0 + 1 := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, getCount, getStorage, count, Contract.run, ContractResult.fst]

/-! ## Summary of Proven Properties

All theorems fully proven with zero sorry and zero axioms:

Read operations:
1. getCount_meets_spec
2. getCount_returns_count
3. getCount_preserves_state

Increment (overflow-guarded):
4. increment_meets_spec
5. increment_adds_one
6. increment_preserves_other_slots
7. increment_reverts_overflow

Decrement (underflow-guarded):
8. decrement_meets_spec
9. decrement_subtracts_one
10. decrement_preserves_other_slots
11. decrement_reverts_underflow

Well-formedness:
12. increment_preserves_wellformedness
13. decrement_preserves_wellformedness

Bounds preservation:
14. increment_preserves_bounds
15. decrement_preserves_bounds

Composition:
16. increment_getCount_correct
-/

end DumbContracts.Proofs.SafeCounter
