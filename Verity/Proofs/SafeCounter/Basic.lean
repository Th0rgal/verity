/-
  Correctness proofs for SafeCounter contract.

  Proves checked arithmetic operations:
  - increment succeeds when no overflow, reverts on overflow
  - decrement succeeds when no underflow, reverts on underflow
  - getCount returns correct value
  - State preservation and well-formedness
-/

import Verity.Core
import Verity.Stdlib.Math
import Verity.Proofs.Stdlib.Math
import Verity.EVM.Uint256
import Verity.Examples.SafeCounter
import Verity.Specs.SafeCounter.Spec
import Verity.Specs.SafeCounter.Invariants

namespace Verity.Proofs.SafeCounter

open Verity
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math (safeAdd_some safeAdd_none safeSub_some safeSub_none)
open Verity.EVM.Uint256
open Verity.Examples.SafeCounter
open Verity.Specs.SafeCounter

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

/-- Helper: relate EVM modular add to Nat addition when bounded. -/
theorem evm_add_eq_of_no_overflow (a b : Uint256) (_h : (a : Nat) + (b : Nat) ≤ MAX_UINT256) :
  add a b = a + b := by
  rfl

/-- Helper: unfold increment when no overflow -/
private theorem increment_unfold (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  (increment).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 0) = true then s.storage 0 + 1 else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  have h_safe := safeAdd_some (s.storage 0) 1 h_no_overflow
  simp only [increment, getStorage, setStorage, count, requireSomeUint,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_safe]

theorem increment_meets_spec (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  increment_spec s s' := by
  rw [increment_unfold s h_no_overflow]
  simp only [ContractResult.snd, increment_spec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [evm_add_eq_of_no_overflow (s.storage 0) 1 h_no_overflow]
  · intro slot h_ne
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

theorem increment_adds_one (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  s'.storage 0 = add (s.storage 0) 1 := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, evm_add_eq_of_no_overflow (s.storage 0) 1 h_no_overflow]

theorem increment_preserves_other_slots (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256)
  (slot : Nat) (h_ne : slot ≠ 0) :
  let s' := ((increment).run s).snd
  s'.storage slot = s.storage slot := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem increment_reverts_overflow (s : ContractState)
  (h_overflow : (s.storage 0 : Nat) + 1 > MAX_UINT256) :
  ∃ msg, (increment).run s = ContractResult.revert msg s := by
  have h_none := safeAdd_none (s.storage 0) 1 h_overflow
  simp [increment, getStorage, setStorage, count, requireSomeUint,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Verity.require, Contract.run, ContractResult.snd, ContractResult.fst,
    h_none]

/-! ## Decrement Correctness -/

/-- Helper: unfold decrement when no underflow -/
private theorem decrement_unfold (s : ContractState)
  (h_no_underflow : (s.storage 0 : Nat) ≥ 1) :
  (decrement).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 0) = true then s.storage 0 - 1 else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  have h_safe := safeSub_some (s.storage 0) 1 h_no_underflow
  simp only [decrement, getStorage, setStorage, count, requireSomeUint,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_safe]

theorem decrement_meets_spec (s : ContractState)
  (h_no_underflow : (s.storage 0 : Nat) ≥ 1) :
  let s' := ((decrement).run s).snd
  decrement_spec s s' := by
  rw [decrement_unfold s h_no_underflow]
  simp only [ContractResult.snd, decrement_spec]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [HSub.hSub, sub]
  · intro slot h_ne
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

theorem decrement_subtracts_one (s : ContractState)
  (h_no_underflow : (s.storage 0 : Nat) ≥ 1) :
  let s' := ((decrement).run s).snd
  s'.storage 0 = sub (s.storage 0) 1 := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd, HSub.hSub, sub]

theorem decrement_preserves_other_slots (s : ContractState)
  (h_no_underflow : (s.storage 0 : Nat) ≥ 1)
  (slot : Nat) (h_ne : slot ≠ 0) :
  let s' := ((decrement).run s).snd
  s'.storage slot = s.storage slot := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd, beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

theorem decrement_reverts_underflow (s : ContractState)
  (h_underflow : s.storage 0 = 0) :
  ∃ msg, (decrement).run s = ContractResult.revert msg s := by
  have h_gt : (1 : Nat) > (s.storage 0 : Nat) := by
    rw [h_underflow]
    decide
  have h_none := safeSub_none (s.storage 0) 1 h_gt
  simp [decrement, getStorage, setStorage, count, requireSomeUint,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Verity.require, Contract.run, ContractResult.snd, ContractResult.fst,
    h_none]

/-! ## State Preservation -/

theorem increment_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  WellFormedState s' := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

theorem decrement_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_no_underflow : (s.storage 0 : Nat) ≥ 1) :
  let s' := ((decrement).run s).snd
  WellFormedState s' := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

/-! ## Bounds Preservation -/

theorem increment_preserves_bounds (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  count_in_bounds s' := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, count_in_bounds]
  have h_bound := Verity.Core.Uint256.val_le_max (s.storage 0 + 1)
  simp [Verity.Core.Uint256.add_comm] at h_bound
  exact h_bound

theorem decrement_preserves_bounds (s : ContractState)
  (_h_bounds : count_in_bounds s)
  (h_no_underflow : (s.storage 0 : Nat) ≥ 1) :
  let s' := ((decrement).run s).snd
  count_in_bounds s' := by
  rw [decrement_unfold s h_no_underflow]
  simp [ContractResult.snd, count_in_bounds]
  exact Verity.Core.Uint256.val_le_max (s.storage 0 - 1)

/-! ## Composition: increment → getCount -/

theorem increment_getCount_correct (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  ((getCount).run s').fst = add (s.storage 0) 1 := by
  rw [increment_unfold s h_no_overflow]
  simp [ContractResult.snd, getCount, getStorage, count, Contract.run, ContractResult.fst,
    evm_add_eq_of_no_overflow (s.storage 0) 1 h_no_overflow]

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

end Verity.Proofs.SafeCounter
