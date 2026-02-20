/-
  Compiler.Proofs.SpecCorrectness.SafeCounter

  Prove that safeCounterSpec accurately represents the SafeCounter EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for SafeCounter with overflow protection.

  Strategy:
  - Define state conversion between EDSL and Spec
  - Prove increment, decrement, and getCount functions produce equivalent results
  - Handle both success and revert cases for overflow/underflow checks
  - Show spec interpretation matches EDSL execution with safe arithmetic
-/

import Compiler.Specs
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Proofs.Stdlib.Automation
import Verity.Examples.SafeCounter
import Verity.Proofs.SafeCounter.Basic

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity
open Verity.Examples.SafeCounter
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Automation

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for SafeCounter -/
def safeCounterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := []
    mappings2 := []
    events := [] }

/- Helper Lemmas -/

/- Local variable lookup helpers for small letVar lists. -/
private theorem lookup_count_newcount (count newCount : Nat) :
    (List.lookup "count" [("newCount", newCount), ("count", count)]).getD 0 = count := by
  simp [List.lookup]

private theorem lookup_newcount (count newCount : Nat) :
    (List.lookup "newCount" [("newCount", newCount), ("count", count)]).getD 0 = newCount := by
  simp [List.lookup]

private theorem lookup_count_single (count : Nat) :
    (List.lookup "count" [("count", count)]).getD 0 = count := by
  simp [List.lookup]

private theorem add_one_val_eq_mod' (a : Verity.Core.Uint256) :
    (Verity.Core.Uint256.add a 1).val =
      ((a.val + 1) % Verity.Core.Uint256.modulus) := by
  rfl

private theorem increment_spec_success_iff (state : ContractState) (sender : Address) :
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    specResult.success = true ↔
      ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val := by
  by_cases h_le :
      ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus ≤ (state.storage 0).val
  · have h_not_gt :
        ¬((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val :=
      Nat.not_lt_of_ge h_le
    simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
      execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
      lookup_count_newcount, lookup_newcount, List.lookup, one_mod_modulus, h_le, h_not_gt]
  · have h_gt :
        ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val :=
      Nat.lt_of_not_ge h_le
    simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
      execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
      lookup_count_newcount, lookup_newcount, List.lookup, one_mod_modulus, h_le, h_gt]

private theorem increment_spec_storage (state : ContractState) (sender : Address)
    (h_gt : ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val) :
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    specResult.finalStorage.getSlot 0 =
      ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus := by
  have h_not_le :
      ¬((state.storage 0).val + 1) % Verity.Core.Uint256.modulus ≤ (state.storage 0).val :=
    Nat.not_le_of_gt h_gt
  simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
    execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
    lookup_count_newcount, lookup_newcount, List.lookup, one_mod_modulus, h_not_le]

private theorem decrement_spec_success_iff (state : ContractState) (sender : Address) :
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    specResult.success = true ↔ (state.storage 0).val ≥ 1 := by
  by_cases h_ge : (state.storage 0).val ≥ 1
  · have h_not_lt : ¬(state.storage 0).val < 1 :=
      Nat.not_lt_of_ge h_ge
    have h_not_lt' : ¬(state.storage 0).val < 1 % Verity.Core.Uint256.modulus := by
      simpa [one_mod_modulus] using h_not_lt
    have h_ne : (state.storage 0).val ≠ 0 := by
      omega
    simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
      execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
      lookup_count_single, List.lookup, one_mod_modulus, h_not_lt', h_ge, h_ne]
  · have h_lt : (state.storage 0).val < 1 :=
      Nat.lt_of_not_ge h_ge
    have h_lt' : (state.storage 0).val < 1 % Verity.Core.Uint256.modulus := by
      simpa [one_mod_modulus] using h_lt
    have h_zero : (state.storage 0).val = 0 := by
      omega
    simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
      execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
      lookup_count_single, List.lookup, one_mod_modulus, h_lt', h_ge, h_zero]

private theorem decrement_spec_storage (state : ContractState) (sender : Address)
    (h_ge : (state.storage 0).val ≥ 1) :
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    specResult.finalStorage.getSlot 0 = (state.storage 0).val - 1 := by
  have h_not_lt : ¬(state.storage 0).val < 1 :=
    Nat.not_lt_of_ge h_ge
  have h_not_lt' : ¬(state.storage 0).val < 1 % Verity.Core.Uint256.modulus := by
    simpa [one_mod_modulus] using h_not_lt
  have h_ne : (state.storage 0).val ≠ 0 := by
    omega
  simp [interpretSpec, safeCounterSpec, safeCounterEdslToSpecStorage,
    execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
    lookup_count_single, List.lookup, one_mod_modulus, h_not_lt', h_ge, h_ne]

/-- Increment reverts when counter is at MAX_UINT256 -/
theorem safeIncrement_reverts_at_max (state : ContractState) (sender : Address)
    (h : (state.storage 0).val = Verity.Core.MAX_UINT256) :
    let result := increment.run { state with sender := sender }
    result.isSuccess = false := by
  -- When count = MAX_UINT256, count + 1 > MAX_UINT256, so safeAdd returns none
  have h_overflow : ((state.storage 0) : Nat) + 1 > Verity.Core.MAX_UINT256 := by
    rw [h]; omega
  -- Use the existing proof from Verity.Proofs.SafeCounter.Basic
  have h_revert := Verity.Proofs.SafeCounter.increment_reverts_overflow
    { state with sender := sender } h_overflow
  rcases h_revert with ⟨msg, h_eq⟩
  rw [h_eq]
  rfl

/-- Increment succeeds when not at max -/
theorem safeIncrement_succeeds_below_max (state : ContractState) (sender : Address)
    (h : (state.storage 0).val < Verity.Core.MAX_UINT256) :
    let result := increment.run { state with sender := sender }
    result.isSuccess = true := by
  -- When count < MAX_UINT256, count + 1 ≤ MAX_UINT256, so safeAdd succeeds
  -- Unfold increment and show that safeAdd succeeds (returns Some), thus no revert
  unfold increment getStorage setStorage count requireSomeUint Contract.run ContractResult.isSuccess
  simp only [Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  -- Show safeAdd returns Some when no overflow
  have h_no_overflow : ((state.storage 0) : Nat) + 1 ≤ Verity.Core.MAX_UINT256 := by
    omega
  -- Note: MAX_UINT256 in Math and Core are equal (both 2^256-1)
  have h_eq : Verity.Stdlib.Math.MAX_UINT256 = Verity.Core.MAX_UINT256 := rfl
  have h_safe : safeAdd (state.storage 0) 1 = some ((state.storage 0) + 1) := by
    unfold safeAdd
    rw [h_eq]
    have h_not : ¬(((state.storage 0) : Nat) + 1 > Verity.Core.MAX_UINT256) := by omega
    simp [h_not]
  rw [h_safe]
  rfl

/- Correctness Theorems -/

/-- The `increment` function correctly increments with overflow check -/
theorem safeIncrement_correct (state : ContractState) (sender : Address) :
    let edslResult := increment.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    (edslResult.isSuccess = true ↔ specResult.success = true) ∧
    (edslResult.isSuccess = true →
      specResult.finalStorage.getSlot 0 = ((ContractResult.getState edslResult).storage 0).val) := by
  -- Proof strategy using add_one_preserves_order_iff_no_overflow:
  -- Both EDSL (safeAdd) and Spec (require newCount > count) succeed iff count < MAX_UINT256
  -- When successful, both store (count + 1).val
  constructor
  · -- Part 1: Success equivalence (both succeed iff count < MAX)
    constructor
    · -- Forward: EDSL success → Spec success
      intro h_edsl
      -- From EDSL success, we know count < MAX (otherwise EDSL would have failed)
      have h_not_max : (state.storage 0).val ≠ Verity.Core.MAX_UINT256 := by
        intro h_eq
        have h_fail := safeIncrement_reverts_at_max state sender h_eq
        rw [h_fail] at h_edsl
        exact absurd h_edsl (Bool.noConfusion)
      have h_below : (state.storage 0).val < Verity.Core.MAX_UINT256 := by
        have h_le := Verity.Core.Uint256.val_le_max (state.storage 0)
        omega
      -- By wraparound lemma: count < MAX implies (count+1).val > count.val
      have h_gt :=
        (add_one_preserves_order_iff_no_overflow
          (state.storage 0)).mpr h_below
      -- Convert to the Nat-mod form used by the spec interpreter
      have h_gt' :
          ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val := by
        simpa [add_one_val_eq_mod', one_mod_modulus, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_gt
      -- Show spec succeeds by unfolding (require passes)
      exact (increment_spec_success_iff state sender).mpr h_gt'
    · -- Backward: Spec success → EDSL success
      intro h_spec
      -- From spec success, require passed: (count+1).val > count.val
      -- By wraparound lemma, this means count < MAX
      have h_guard_mod :
          ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val :=
        (increment_spec_success_iff state sender).mp h_spec
      -- Convert back to the Uint256 form
      have h_guard' :
          ((state.storage 0) + 1 : Verity.Core.Uint256).val > (state.storage 0).val := by
        simpa [add_one_val_eq_mod', one_mod_modulus, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_guard_mod
      -- By wraparound lemma: (count+1).val > count.val implies count < MAX
      have h_below :=
        (add_one_preserves_order_iff_no_overflow
          (state.storage 0)).mp h_guard'
      -- Use helper: at count < MAX, EDSL succeeds
      exact safeIncrement_succeeds_below_max state sender h_below
  · -- Part 2: Storage equivalence when successful
    intro h_edsl
    -- Both EDSL and Spec compute (count + 1) and store its .val
    -- When EDSL succeeds, count < MAX (shown in Part 1)
    have h_not_max : (state.storage 0).val ≠ Verity.Core.MAX_UINT256 := by
      intro h_eq
      have h_fail := safeIncrement_reverts_at_max state sender h_eq
      rw [h_fail] at h_edsl
      exact absurd h_edsl (Bool.noConfusion)
    -- Below MAX: both store the same value
    have h_below : (state.storage 0).val < Verity.Core.MAX_UINT256 := by
      have h_le := Verity.Core.Uint256.val_le_max (state.storage 0)
      omega
    -- EDSL stores (count + 1).val
    have h_le : ((state.storage 0) : Nat) + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 := by
      have : Verity.Stdlib.Math.MAX_UINT256 = Verity.Core.MAX_UINT256 := rfl
      rw [this]; omega
    let s := { state with sender := sender }
    have h_adds :=
      Verity.Proofs.SafeCounter.increment_adds_one s h_le
    have h_edsl_storage_val :
        ((ContractResult.getState (increment.run s)).storage 0).val =
          ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus := by
      have h_adds' : ((increment.run s).snd.storage 0) =
          Verity.EVM.Uint256.add (state.storage 0) 1 := by simpa [s] using h_adds
      simpa [ContractResult.getState, Verity.EVM.Uint256.add, add_one_val_eq_mod'] using
        congrArg Verity.Core.Uint256.val h_adds'
    -- Spec stores (count + 1).val
    -- The require passes and stores (count + 1).val
    -- We can use the same guard proof as above
    have h_gt :=
      (add_one_preserves_order_iff_no_overflow
        (state.storage 0)).mpr h_below
    have h_gt' :
        ((state.storage 0).val + 1) % Verity.Core.Uint256.modulus > (state.storage 0).val := by
      simpa [add_one_val_eq_mod', one_mod_modulus, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_gt
    -- Unfold spec interpreter to compute finalStorage.getSlot 0
    -- The require passes, so storage is updated to newCount
    -- Combine with the EDSL storage computation
    exact (increment_spec_storage state sender h_gt').trans h_edsl_storage_val.symm

/- Helper Properties -/

/-- Decrement reverts when counter is 0 -/
theorem safeDecrement_reverts_at_zero (state : ContractState) (sender : Address)
    (h : (state.storage 0).val = 0) :
    let result := decrement.run { state with sender := sender }
    result.isSuccess = false := by
  -- When count = 0, safeSub returns none (underflow)
  -- decrement_reverts_underflow expects: s.storage 0 = 0
  have h_storage_zero : (state.storage 0) = 0 := by
    ext
    exact h
  -- Use the existing proof from Verity.Proofs.SafeCounter.Basic
  have h_revert := Verity.Proofs.SafeCounter.decrement_reverts_underflow
    { state with sender := sender } h_storage_zero
  rcases h_revert with ⟨msg, h_eq⟩
  rw [h_eq]
  rfl

/-- Decrement succeeds when above zero -/
theorem safeDecrement_succeeds_above_zero (state : ContractState) (sender : Address)
    (h : (state.storage 0).val > 0) :
    let result := decrement.run { state with sender := sender }
    result.isSuccess = true := by
  -- When count > 0, count ≥ 1, so safeSub succeeds
  unfold decrement getStorage setStorage count requireSomeUint Contract.run ContractResult.isSuccess
  simp only [Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  -- Show safeSub returns Some when no underflow
  have h_no_underflow : ((state.storage 0) : Nat) ≥ 1 := by
    omega
  have h_safe : safeSub (state.storage 0) 1 = some ((state.storage 0) - 1) := by
    unfold safeSub
    have h_not : ¬((1 : Nat) > ((state.storage 0) : Nat)) := by omega
    simp [h_not]
  rw [h_safe]
  rfl

/-- The `decrement` function correctly decrements with underflow check -/
theorem safeDecrement_correct (state : ContractState) (sender : Address) :
    let edslResult := decrement.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    (edslResult.isSuccess = true ↔ specResult.success = true) ∧
    (edslResult.isSuccess = true →
      specResult.finalStorage.getSlot 0 = ((ContractResult.getState edslResult).storage 0).val) := by
  -- Split on whether count ≥ 1
  by_cases h_ge : (state.storage 0 : Nat) ≥ 1
  · -- No underflow: both EDSL and spec succeed and store count - 1
    constructor
    · -- EDSL success ↔ spec success
      constructor
      · intro _h_edsl
        -- Spec requires count ≥ 1, which holds
        exact (decrement_spec_success_iff state sender).mpr h_ge
      · intro _h_spec
        -- EDSL safeSub succeeds when count ≥ 1
        exact safeDecrement_succeeds_above_zero state sender (by omega)
    · -- Storage equivalence when successful
      intro _h_edsl
      -- EDSL: decrement stores (count - 1)
      let s := { state with sender := sender }
      have h_subs :=
        Verity.Proofs.SafeCounter.decrement_subtracts_one s h_ge
      have h_edsl_storage_val :
          ((ContractResult.getState (decrement.run s)).storage 0).val =
            (state.storage 0).val - 1 := by
        have h_subs' : ((decrement.run s).snd.storage 0) =
            Verity.EVM.Uint256.sub (state.storage 0) 1 := by simpa [s] using h_subs
        have h_edsl_storage :=
          congrArg Verity.Core.Uint256.val h_subs'
        have h_lt_mod : (state.storage 0).val - 1 < Verity.Core.Uint256.modulus :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) (state.storage 0).isLt
        simpa [ContractResult.getState, Verity.EVM.Uint256.sub,
          Verity.Core.Uint256.sub, one_mod_modulus, h_ge, Nat.mod_eq_of_lt h_lt_mod] using h_edsl_storage
      -- Spec: require passes and setStorage stores (count - 1)
      exact (decrement_spec_storage state sender h_ge).trans h_edsl_storage_val.symm
  · -- Underflow: count < 1, both EDSL and spec fail
    have h_lt : (state.storage 0 : Nat) < 1 := by omega
    constructor
    · -- Success equivalence (both false)
      constructor
      · intro h_edsl
        -- EDSL cannot succeed when count < 1
        have h_fail := safeDecrement_reverts_at_zero state sender (by omega)
        rw [h_fail] at h_edsl
        exact (Bool.false_ne_true h_edsl).elim
      · intro h_spec
        -- Spec require fails when count < 1
        have h_ge' : (state.storage 0).val ≥ 1 := (decrement_spec_success_iff state sender).mp h_spec
        have h_not_ge : ¬ (state.storage 0).val ≥ 1 := by
          exact Nat.not_le_of_gt h_lt
        exact (h_not_ge h_ge').elim
    · -- Storage equivalence on success is vacuous (EDSL success impossible)
      intro h_edsl
      have h_fail := safeDecrement_reverts_at_zero state sender (by omega)
      rw [h_fail] at h_edsl
      exact (Bool.false_ne_true h_edsl).elim

/-- The `getCount` function correctly retrieves the counter value -/
theorem safeGetCount_correct (state : ContractState) (sender : Address) :
    let edslValue := (getCount.runValue { state with sender := sender }).val
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec safeCounterSpec (safeCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simp [getCount, Contract.runValue, safeCounterSpec, interpretSpec, safeCounterEdslToSpecStorage,
    getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, count]

/- Helper Properties -/

/-- `getCount` does not modify storage -/
theorem safeGetCount_preserves_state (state : ContractState) (sender : Address) :
    let finalState := getCount.runState { state with sender := sender }
    finalState.storage 0 = state.storage 0 := by
  simp [getCount, Contract.runState, getStorage, count]

end Compiler.Proofs.SpecCorrectness
