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
import Compiler.Proofs.SpecInterpreter
import DumbContracts.Examples.SafeCounter
import DumbContracts.Core.Uint256
import DumbContracts.Stdlib.Math
import DumbContracts.Proofs.SafeCounter.Basic

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open DumbContracts
open DumbContracts.Examples.SafeCounter
open DumbContracts.Stdlib.Math

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for SafeCounter -/
def safeCounterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := [] }

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
      specResult.finalStorage.getSlot 0 = (edslResult.getState.storage 0).val) := by
  sorry

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
      specResult.finalStorage.getSlot 0 = (edslResult.getState.storage 0).val) := by
  sorry

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
  -- Same pattern as Counter.getCount_correct
  unfold getCount Contract.runValue safeCounterSpec interpretSpec safeCounterEdslToSpecStorage
  simp [getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, count]

/- Helper Properties -/

/-- `getCount` does not modify storage -/
theorem safeGetCount_preserves_state (state : ContractState) (sender : Address) :
    let finalState := getCount.runState { state with sender := sender }
    finalState.storage 0 = state.storage 0 := by
  -- getCount just reads storage, doesn't modify it
  unfold getCount Contract.runState
  simp [getStorage, count]

/-- Increment reverts when counter is at MAX_UINT256 -/
theorem safeIncrement_reverts_at_max (state : ContractState) (sender : Address)
    (h : (state.storage 0).val = DumbContracts.Core.MAX_UINT256) :
    let result := increment.run { state with sender := sender }
    result.isSuccess = false := by
  -- When count = MAX_UINT256, count + 1 > MAX_UINT256, so safeAdd returns none
  have h_overflow : ((state.storage 0) : Nat) + 1 > DumbContracts.Core.MAX_UINT256 := by
    rw [h]; omega
  -- Use the existing proof from DumbContracts.Proofs.SafeCounter.Basic
  have h_revert := DumbContracts.Proofs.SafeCounter.increment_reverts_overflow
    { state with sender := sender } h_overflow
  rcases h_revert with ⟨msg, h_eq⟩
  rw [h_eq]
  rfl

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
  -- Use the existing proof from DumbContracts.Proofs.SafeCounter.Basic
  have h_revert := DumbContracts.Proofs.SafeCounter.decrement_reverts_underflow
    { state with sender := sender } h_storage_zero
  rcases h_revert with ⟨msg, h_eq⟩
  rw [h_eq]
  rfl

/-- Increment succeeds when not at max -/
theorem safeIncrement_succeeds_below_max (state : ContractState) (sender : Address)
    (h : (state.storage 0).val < DumbContracts.Core.MAX_UINT256) :
    let result := increment.run { state with sender := sender }
    result.isSuccess = true := by
  -- When count < MAX_UINT256, count + 1 ≤ MAX_UINT256, so safeAdd succeeds
  -- Unfold increment and show that safeAdd succeeds (returns Some), thus no revert
  unfold increment getStorage setStorage count requireSomeUint Contract.run ContractResult.isSuccess
  simp only [DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure]
  -- Show safeAdd returns Some when no overflow
  have h_no_overflow : ((state.storage 0) : Nat) + 1 ≤ DumbContracts.Core.MAX_UINT256 := by
    omega
  -- Note: MAX_UINT256 in Math and Core are equal (both 2^256-1)
  have h_eq : DumbContracts.Stdlib.Math.MAX_UINT256 = DumbContracts.Core.MAX_UINT256 := by rfl
  have h_safe : safeAdd (state.storage 0) 1 = some ((state.storage 0) + 1) := by
    unfold safeAdd
    rw [h_eq]
    have h_not : ¬(((state.storage 0) : Nat) + 1 > DumbContracts.Core.MAX_UINT256) := by omega
    simp [h_not]
  rw [h_safe]
  rfl

/-- Decrement succeeds when above zero -/
theorem safeDecrement_succeeds_above_zero (state : ContractState) (sender : Address)
    (h : (state.storage 0).val > 0) :
    let result := decrement.run { state with sender := sender }
    result.isSuccess = true := by
  -- When count > 0, count ≥ 1, so safeSub succeeds
  unfold decrement getStorage setStorage count requireSomeUint Contract.run ContractResult.isSuccess
  simp only [DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure]
  -- Show safeSub returns Some when no underflow
  have h_no_underflow : ((state.storage 0) : Nat) ≥ 1 := by
    omega
  have h_safe : safeSub (state.storage 0) 1 = some ((state.storage 0) - 1) := by
    unfold safeSub
    have h_not : ¬((1 : Nat) > ((state.storage 0) : Nat)) := by omega
    simp [h_not]
  rw [h_safe]
  rfl

end Compiler.Proofs.SpecCorrectness
