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
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Examples.Counter
import Verity.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity
open Verity.Examples.Counter
open Verity.EVM.Uint256 (add sub)
open Verity.Core.Uint256 (modulus val_ofNat ofNat)

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Counter -/
def counterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := []
    mappings2 := []
    events := [] }

/- Helper Lemmas -/

-- Helper: decrement's monadic bind simplifies correctly
private theorem decrement_runState_eq (state : ContractState) :
    (decrement.runState state).storage 0 =
    sub (state.storage 0) 1 := by
  unfold decrement Contract.runState getStorage setStorage count
  simp [sub, Verity.bind]
  rfl

-- Helper: spec's evalExpr for decrement expression matches EDSL sub
private theorem evalExpr_decrement_eq (state : ContractState) (sender : Address) :
    evalExpr
      { sender := sender,
        msgValue := 0,
        blockTimestamp := 0,
        params := [],
        paramTypes := [],
        constructorArgs := [],
        constructorParamTypes := [],
        localVars := [],
        arrayParams := [] }
      { slots := [(0, (state.storage 0).val)], mappings := [], mappings2 := [], events := [] }
      [{ name := "count", ty := FieldType.uint256 }]
      []
      []
      ((Expr.storage "count").sub (Expr.literal 1)) =
    (sub (state.storage 0) 1).val := by
  -- Both evalExpr and Uint256.sub use the same conditional on val >= 1.
  have h1lt : (1 : Nat) < modulus := by
    dsimp [modulus, Verity.Core.UINT256_MODULUS]
    decide
  have h1mod : (1 % modulus) = (1 : Nat) := Nat.mod_eq_of_lt h1lt
  have hidx :
      (List.findIdx? (fun f : Field => f.name == "count")
          (([{ name := "count", ty := FieldType.uint256 }] : List Field))) = some 0 := by
    simp [List.findIdx?]
  by_cases h : (state.storage 0).val ≥ 1
  · -- No underflow: both sides are val - 1.
    have hle : (1 : Verity.Core.Uint256).val ≤ (state.storage 0).val := by
      simpa using h
    have h_sub : (sub (state.storage 0) 1).val = (state.storage 0).val - 1 := by
      simpa using (Verity.EVM.Uint256.sub_eq_of_le (a := state.storage 0) (b := (1 : Verity.Core.Uint256)) hle)
    -- Reduce evalExpr to the same expression
    simp [evalExpr, SpecStorage.getSlot, List.lookup, hidx, h1mod, h, h_sub]  -- result matches
  · -- Underflow case: val = 0, so result is modulus - 1 on both sides.
    have hlt : (state.storage 0).val < 1 := Nat.lt_of_not_ge h
    have h0 : (state.storage 0).val = 0 := by
      exact (Nat.lt_one_iff.mp hlt)
    have hgt : (1 : Verity.Core.Uint256).val > (state.storage 0).val := by
      simp [h0]
    have h_sub : (sub (state.storage 0) 1).val =
        (modulus - ((1 : Verity.Core.Uint256).val - (state.storage 0).val)) % modulus := by
      simpa using (Verity.Core.Uint256.sub_val_of_gt (a := state.storage 0) (b := (1 : Verity.Core.Uint256)) hgt)
    have hlt_mod : modulus - (1 - (state.storage 0).val) < modulus := by
      -- With val = 0, this is modulus - 1 < modulus.
      have hle : (1 : Nat) ≤ modulus := Nat.succ_le_of_lt Verity.Core.Uint256.modulus_pos
      have hpos : 0 < (1 : Nat) := by decide
      simpa [h0] using (Nat.sub_lt_of_pos_le hpos hle)
    have h_mod : (modulus - (1 - (state.storage 0).val)) % modulus =
        modulus - (1 - (state.storage 0).val) := by
      exact Nat.mod_eq_of_lt hlt_mod
    simp [evalExpr, SpecStorage.getSlot, List.lookup, hidx, h1mod, h, h0, h_sub, h_mod]

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
    (_h : (state.storage 0).val < Verity.Core.MAX_UINT256) :
    let afterInc := increment.runState { state with sender := sender }
    let afterDec := decrement.runState { afterInc with sender := sender }
    afterDec.storage 0 = state.storage 0 := by
  -- Unfold increment and decrement
  unfold increment decrement Contract.runState
  simp [getStorage, setStorage, count, Verity.bind]
  -- We have: sub (add (state.storage 0) 1) 1 = state.storage 0
  -- This is exactly the sub_add_cancel theorem
  exact Verity.EVM.Uint256.sub_add_cancel (state.storage 0) 1

/-- Decrementing then incrementing returns to original value (when not wrapping) -/
theorem decrement_increment_roundtrip (state : ContractState) (sender : Address)
    (_h : (state.storage 0).val > 0) :
    let afterDec := decrement.runState { state with sender := sender }
    let afterInc := increment.runState { afterDec with sender := sender }
    afterInc.storage 0 = state.storage 0 := by
  -- This is the reverse of increment_decrement_roundtrip
  -- We use sub_add_cancel_left: (a - b) + b = a (always holds for Uint256 modular arithmetic)
  unfold decrement increment Contract.runState
  simp [getStorage, setStorage, count, Verity.bind]
  -- We have: add (sub (state.storage 0) 1) 1 = state.storage 0
  -- This is exactly sub_add_cancel_left in infix notation: (a - b) + b = a
  exact Verity.Core.Uint256.sub_add_cancel_left (state.storage 0) 1

/-- Helper: Single increment adds 1 to storage (mod modulus) -/
private theorem increment_adds_one (state : ContractState) (sender : Address) :
    (increment.runState { state with sender := sender }).storage 0 =
    add (state.storage 0) 1 := by
  unfold increment Contract.runState getStorage setStorage count
  simp [Verity.bind]
  rfl

/-- Apply increment n times to a state -/
private def applyNIncrements (sender : Address) : Nat → ContractState → ContractState
  | 0, s => s
  | k+1, s => applyNIncrements sender k (increment.runState { s with sender := sender })

/-- Helper: applyNIncrements value equals initial value + n (mod modulus) -/
private theorem applyNIncrements_val (state : ContractState) (sender : Address) : ∀ (n : Nat),
    ((applyNIncrements sender n state).storage 0).val =
    ((state.storage 0).val + n) % modulus
  | 0 => by
      -- Base case: 0 increments
      simp [applyNIncrements, Nat.add_zero]
      -- Show: (state.storage 0).val = ((state.storage 0).val) % modulus
      -- This is true because Uint256.val < modulus always
      symm
      exact Nat.mod_eq_of_lt (state.storage 0).isLt
  | k+1 => by
      -- Inductive case: k+1 increments
      -- applyN (k+1) state = applyN k (increment state)
      simp only [applyNIncrements]
      let stateAfterOne := increment.runState { state with sender := sender }
      -- Apply IH to stateAfterOne with k increments
      have h_ih := applyNIncrements_val stateAfterOne sender k
      -- stateAfterOne.storage 0 = add (state.storage 0) 1
      have h_one : stateAfterOne.storage 0 = add (state.storage 0) 1 := increment_adds_one state sender
      rw [h_one] at h_ih
      rw [h_ih]
      -- Show: ((add (state.storage 0) 1).val + k) % modulus = ((state.storage 0).val + (k + 1)) % modulus
      -- (add a 1).val = (a.val + 1) % modulus by definition
      have h_add_val : (add (state.storage 0) 1).val = ((state.storage 0).val + 1) % modulus := by
        simp [Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat]
      rw [h_add_val]
      -- Show: (((state.storage 0).val + 1) % modulus + k) % modulus = ((state.storage 0).val + (k + 1)) % modulus
      -- This is a standard modular arithmetic fact
      -- We need to show: (a % m + b) % m = (a + b) % m where a = (state.storage 0).val + 1, b = k
      -- Use the fact that for any a, b, m: (a % m + b) % m ≡ (a + b) % m
      calc
        (((state.storage 0).val + 1) % modulus + k) % modulus
            = (((state.storage 0).val + 1) + k) % modulus := by
                exact (Nat.mod_add_mod ((state.storage 0).val + 1) modulus k)
        _ = ((state.storage 0).val + (k + 1)) % modulus := by
                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Multiple increments accumulate correctly (modulo 2^256) -/
theorem multiple_increments (state : ContractState) (sender : Address) (n : Nat) :
    let finalState := applyNIncrements sender n state
    (finalState.storage 0).val = ((state.storage 0).val + n) % modulus := by
  exact applyNIncrements_val state sender n

end Compiler.Proofs.SpecCorrectness
