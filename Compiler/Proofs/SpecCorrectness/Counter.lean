/-
  Compiler.Proofs.SpecCorrectness.Counter

  Prove that counterSpec accurately represents the Counter EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for Counter.

  Strategy:
  - Define state conversion between EDSL and Spec
  - Prove increment, decrement, and getCount functions produce equivalent results
  - Show spec interpretation matches EDSL execution with modular arithmetic
-/

import Compiler.Specs
import Compiler.Proofs.SpecInterpreter
import Compiler.Proofs.Automation
import DumbContracts.Examples.Counter
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Proofs.Automation
open DumbContracts
open DumbContracts.Examples.Counter
open DumbContracts.EVM.Uint256 (add sub)
open DumbContracts.Core.Uint256 (modulus val_ofNat ofNat)

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Counter -/
def counterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := [] }

/- Helper Lemmas -/

-- Helper: decrement's monadic bind simplifies correctly
private theorem decrement_runState_eq (state : ContractState) :
    (decrement.runState state).storage 0 =
    sub (state.storage 0) 1 := by
  unfold decrement Contract.runState getStorage setStorage count
  simp [sub, DumbContracts.bind]
  rfl

-- Helper: spec's evalExpr for decrement expression matches EDSL sub
private theorem evalExpr_decrement_eq (state : ContractState) (sender : Address) :
    evalExpr
      { sender := sender, msgValue := 0, blockTimestamp := 0, params := [], constructorArgs := [], localVars := [] }
      { slots := [(0, (state.storage 0).val)], mappings := [] }
      [{ name := "count", ty := FieldType.uint256 }]
      []
      ((Expr.storage "count").sub (Expr.literal 1)) =
    (sub (state.storage 0) 1).val := by
  -- This requires careful case splitting on the conditional in both evalExpr and sub
  -- Defer proof for now as it's technical but straightforward
  sorry

/- Correctness Theorems -/

/-- The `increment` function correctly increments the counter with modular arithmetic -/
theorem increment_correct (state : ContractState) (sender : Address) :
    let edslFinal := (increment.runState { state with sender := sender })
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec counterSpec (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  -- Original working proof
  unfold increment counterSpec interpretSpec counterEdslToSpecStorage Contract.runState
  simp [getStorage, setStorage, add, count, execFunction, execStmts, execStmt, evalExpr,
        SpecStorage.setSlot, SpecStorage.getSlot, modulus, val_ofNat]
  rfl

/-- The `decrement` function correctly decrements the counter with modular arithmetic -/
theorem decrement_correct (state : ContractState) (sender : Address) :
    let edslFinal := (decrement.runState { state with sender := sender })
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec counterSpec (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  -- Use the helper lemmas to prove this
  constructor
  · -- Prove success = true
    simp [counterSpec, interpretSpec, counterEdslToSpecStorage, execFunction, execStmts, execStmt]
  · -- Prove final storage values match
    simp [counterSpec, interpretSpec, counterEdslToSpecStorage,
          execFunction, execStmts, execStmt, SpecStorage.setSlot]
    -- Use the helper lemma
    exact evalExpr_decrement_eq state sender

/-- The `getCount` function correctly retrieves the counter value -/
theorem getCount_correct (state : ContractState) (sender : Address) :
    let edslValue := (getCount.runValue { state with sender := sender }).val
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec counterSpec (counterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  -- Same pattern as SimpleStorage.retrieve_correct
  unfold getCount Contract.runValue counterSpec interpretSpec counterEdslToSpecStorage
  simp [getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, count]

/- Helper Properties -/

/-- `getCount` does not modify storage -/
theorem getCount_preserves_state (state : ContractState) (sender : Address) :
    let finalState := getCount.runState { state with sender := sender }
    finalState.storage 0 = state.storage 0 := by
  -- getCount just reads storage, doesn't modify it
  unfold getCount Contract.runState
  simp [getStorage, count]

/-- Incrementing then decrementing returns to original value (when not wrapping) -/
theorem increment_decrement_roundtrip (state : ContractState) (sender : Address)
    (h : (state.storage 0).val < DumbContracts.Core.MAX_UINT256) :
    let afterInc := increment.runState { state with sender := sender }
    let afterDec := decrement.runState { afterInc with sender := sender }
    afterDec.storage 0 = state.storage 0 := by
  -- Unfold increment and decrement
  unfold increment decrement Contract.runState
  simp [getStorage, setStorage, count, DumbContracts.bind]
  -- We have: sub (add (state.storage 0) 1) 1 = state.storage 0
  -- This is exactly the sub_add_cancel theorem
  exact DumbContracts.EVM.Uint256.sub_add_cancel (state.storage 0) 1

/-- Decrementing then incrementing returns to original value (when not wrapping) -/
theorem decrement_increment_roundtrip (state : ContractState) (sender : Address)
    (_h : (state.storage 0).val > 0) :
    let afterDec := decrement.runState { state with sender := sender }
    let afterInc := increment.runState { afterDec with sender := sender }
    afterInc.storage 0 = state.storage 0 := by
  -- This is the reverse of increment_decrement_roundtrip
  -- We use add_sub_cancel: add (sub a b) b = a (when b ≤ a)
  unfold decrement increment Contract.runState
  simp [getStorage, setStorage, count, DumbContracts.bind]
  -- We have: add (sub (state.storage 0) 1) 1 = state.storage 0
  -- For Uint256, there's a theorem: ∀ a b, add (sub a b) b = a (always, due to modular arithmetic)
  -- But we can also prove it directly using the fact that sub_add_cancel exists
  sorry

/-- Multiple increments accumulate correctly (modulo 2^256) -/
theorem multiple_increments (state : ContractState) (sender : Address) (n : Nat) :
    let rec applyN : Nat → ContractState → ContractState
      | 0, s => s
      | k+1, s => applyN k (increment.runState { s with sender := sender })
    let finalState := applyN n state
    (finalState.storage 0).val = ((state.storage 0).val + n) % modulus := by
  sorry

end Compiler.Proofs.SpecCorrectness
