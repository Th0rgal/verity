/-
  Advanced correctness proofs for SafeCounter contract.

  Proves deeper properties beyond Basic.lean:
  - Standalone invariant proofs matching Invariants.lean definitions
  - Composition: increment → decrement cancellation
  - Composition: decrement → getCount
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.SafeCounter
import DumbContracts.Specs.SafeCounter.Spec
import DumbContracts.Specs.SafeCounter.Invariants
import DumbContracts.Proofs.SafeCounter.Basic

namespace DumbContracts.Proofs.SafeCounter.Correctness

open DumbContracts
open DumbContracts.Stdlib.Math
open DumbContracts.EVM.Uint256
open DumbContracts.Examples.SafeCounter
open DumbContracts.Specs.SafeCounter
open DumbContracts.Proofs.SafeCounter

/-! ## Standalone Invariant Proofs

Prove context_preserved and storage_isolated as standalone theorems
matching the Invariants.lean definitions.
-/

/-- increment preserves context (sender, thisAddress). -/
theorem increment_preserves_context (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  context_preserved s s' := by
  have h := increment_meets_spec s h_no_overflow
  simp [increment_spec] at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- decrement preserves context (sender, thisAddress). -/
theorem decrement_preserves_context (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  context_preserved s s' := by
  have h := decrement_meets_spec s h_no_underflow
  simp [decrement_spec] at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- increment preserves storage isolation. -/
theorem increment_preserves_storage_isolated (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  storage_isolated s s' := by
  simp [storage_isolated]
  intro slot h_ne
  exact increment_preserves_other_slots s h_no_overflow slot h_ne

/-- decrement preserves storage isolation. -/
theorem decrement_preserves_storage_isolated (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  storage_isolated s s' := by
  simp [storage_isolated]
  intro slot h_ne
  exact decrement_preserves_other_slots s h_no_underflow slot h_ne

/-- getCount preserves context (trivially, read-only). -/
theorem getCount_preserves_context (s : ContractState) :
  let s' := ((getCount).run s).snd
  context_preserved s s' := by
  have h := getCount_preserves_state s
  simp [h, context_preserved]

/-- getCount preserves well-formedness. -/
theorem getCount_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getCount).run s).snd
  WellFormedState s' := by
  have h_pres := getCount_preserves_state s
  rw [h_pres]
  exact h

/-! ## Composition: increment → decrement cancellation -/

/-- Increment then decrement returns to original count value.
    Requires no overflow on increment. -/
theorem increment_decrement_cancel (s : ContractState)
  (h_no_overflow : (s.storage 0 : Nat) + 1 ≤ MAX_UINT256) :
  let s' := ((increment).run s).snd
  let s'' := ((decrement).run s').snd
  s''.storage 0 = s.storage 0 := by
  have h_inc := increment_adds_one s h_no_overflow
  have h_add : add (s.storage 0) 1 = s.storage 0 + 1 := by
    exact evm_add_eq_of_no_overflow (s.storage 0) 1 h_no_overflow
  -- After increment, s'.storage 0 = s.storage 0 + 1 ≥ 1
  have h_ge : ((increment).run s).snd.storage 0 ≥ 1 := by
    rw [h_inc, h_add]
    have h_max_lt : MAX_UINT256 < DumbContracts.Core.Uint256.modulus := by
      have h_succ : MAX_UINT256 < MAX_UINT256 + 1 := Nat.lt_succ_self _
      have h_eq : MAX_UINT256 + 1 = DumbContracts.Core.Uint256.modulus :=
        DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus
      simpa [h_eq] using h_succ
    have h_sum_lt :
        (s.storage 0 : Nat) + 1 < DumbContracts.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt h_no_overflow h_max_lt
    have h_val :
        ((s.storage 0 + 1 : Uint256) : Nat) = (s.storage 0 : Nat) + 1 := by
      exact DumbContracts.Core.Uint256.add_eq_of_lt h_sum_lt
    have h_ge_val : (1 : Nat) ≤ (s.storage 0 : Nat) + 1 := Nat.le_add_left _ _
    have h_goal : (1 : Nat) ≤ (s.storage 0 + 1 : Uint256).val := by
      rw [h_val]
      exact h_ge_val
    have h_ge_val' : (1 : Uint256).val ≤ (s.storage 0 + 1 : Uint256).val := by
      simpa [DumbContracts.Core.Uint256.val_one] using h_goal
    simpa [DumbContracts.Core.Uint256.le_def] using h_ge_val'
  have h_dec := decrement_subtracts_one ((increment).run s).snd h_ge
  calc ((decrement).run ((increment).run s).snd).snd.storage 0
      = sub (((increment).run s).snd.storage 0) 1 := h_dec
    _ = ((increment).run s).snd.storage 0 - 1 := by
      rfl
    _ = (s.storage 0 + 1) - 1 := by rw [h_inc, h_add]
    _ = s.storage 0 := by
      exact (DumbContracts.Core.Uint256.sub_add_cancel (s.storage 0) 1)

/-! ## Composition: decrement → getCount -/

/-- decrement followed by getCount returns count - 1. -/
theorem decrement_getCount_correct (s : ContractState)
  (h_no_underflow : s.storage 0 ≥ 1) :
  let s' := ((decrement).run s).snd
  ((getCount).run s').fst = sub (s.storage 0) 1 := by
  have h_dec := decrement_subtracts_one s h_no_underflow
  have h_get := getCount_returns_count ((decrement).run s).snd
  simp only [h_dec] at h_get
  exact h_get

/-! ## Summary

All 9 theorems fully proven with zero sorry:

Standalone invariants:
1. increment_preserves_context
2. decrement_preserves_context
3. increment_preserves_storage_isolated
4. decrement_preserves_storage_isolated
5. getCount_preserves_context
6. getCount_preserves_wellformedness

Composition:
7. increment_decrement_cancel
8. decrement_getCount_correct
-/

end DumbContracts.Proofs.SafeCounter.Correctness
