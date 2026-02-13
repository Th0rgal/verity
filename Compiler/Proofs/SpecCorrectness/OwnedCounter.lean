/-
  Compiler.Proofs.SpecCorrectness.OwnedCounter

  Prove that ownedCounterSpec accurately represents the OwnedCounter EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for OwnedCounter, which composes
  ownership and counter patterns.

  Strategy:
  - Define state conversion with multiple storage slots (owner + count)
  - Prove constructor correctly initializes owner
  - Prove increment/decrement work only when authorized
  - Prove getCount/getOwner retrieve correct values
  - Show spec interpretation matches EDSL execution with composed patterns
-/

import Compiler.Specs
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import DumbContracts.Proofs.Stdlib.Automation
import Compiler.Hex
import DumbContracts.Examples.OwnedCounter
import DumbContracts.Proofs.OwnedCounter.Basic
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open DumbContracts.Proofs.Stdlib.SpecInterpreter
open DumbContracts.Proofs.Stdlib.Automation
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.OwnedCounter
open DumbContracts.Proofs.OwnedCounter

-- Address encoding lemmas are provided by Automation.

-- Helper: EVM add (Uint256) matches modular Nat addition.
-- (uint256_add_val) is provided by Automation.

-- (uint256_sub_val) is provided by Automation.

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for OwnedCounter -/
def ownedCounterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [
      (0, addressToNat (state.storageAddr 0)),  -- owner at slot 0
      (1, (state.storage 1).val)                -- count at slot 1
    ]
    mappings := [] }

/- Correctness Theorems -/

/-- The `constructor` correctly initializes the owner -/
theorem ownedCounter_constructor_correct (state : ContractState) (initialOwner : Address) (sender : Address) :
    let edslResult := (constructor initialOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := ""
      args := [addressToNat initialOwner]
    }
    let specResult := interpretSpec ownedCounterSpec SpecStorage.empty specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = addressToNat (edslResult.getState.storageAddr 0) := by
  -- Constructor sets owner to initialOwner in both EDSL and spec
  unfold DumbContracts.Examples.OwnedCounter.constructor Contract.run ownedCounterSpec interpretSpec
  simp [setStorageAddr, DumbContracts.Examples.OwnedCounter.owner, DumbContracts.bind, DumbContracts.pure]
  simp [execConstructor, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty]
  -- addressToNat_mod_eq is a simp lemma now.

/-- The `increment` function correctly increments when called by owner -/
theorem ownedCounter_increment_correct_as_owner (state : ContractState) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := increment.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 1 = (edslResult.getState.storage 1).val := by
  constructor
  · -- EDSL success when sender is owner
    unfold DumbContracts.Examples.OwnedCounter.increment Contract.run
    unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
    unfold msgSender getStorageAddr setStorage DumbContracts.Examples.OwnedCounter.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = true := by
      rw [beq_iff_eq, h]
    rw [h_beq]
    simp [ContractResult.isSuccess, getStorage, setStorage]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_owner' : ({ state with sender := sender }).sender =
        ({ state with sender := sender }).storageAddr 0 := by
      simp [h]
    have h_inc :
        ((increment.run { state with sender := sender }).getState.storage 1) =
          DumbContracts.EVM.Uint256.add (state.storage 1) 1 := by
      simpa [ContractResult.getState, ContractResult.snd] using
        (increment_adds_one_when_owner (s := { state with sender := sender }) h_owner')
    have h_inc_val :
        ((increment.run { state with sender := sender }).getState.storage 1).val =
          ((state.storage 1).val + 1) % DumbContracts.Core.Uint256.modulus := by
      have h_inc_val' := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_inc
      simp [uint256_add_val] at h_inc_val'
      exact h_inc_val'
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, h_inc_val, lookup_slot_second]

/-- The `increment` function correctly reverts when called by non-owner -/
theorem ownedCounter_increment_reverts_as_nonowner (state : ContractState) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := increment.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "increment"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  constructor
  · -- EDSL reverts when sender is not owner
    unfold DumbContracts.Examples.OwnedCounter.increment Contract.run
    unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
    unfold msgSender getStorageAddr setStorage DumbContracts.Examples.OwnedCounter.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = false := by
      cases h_eq : (sender == state.storageAddr 0)
      · rfl
      · rw [beq_iff_eq] at h_eq
        exfalso
        exact h h_eq.symm
    rw [h_beq]
    simp [ContractResult.isSuccess, getStorage, setStorage]
  · -- Spec reverts when sender is not owner
    have h_beq : (addressToNat sender == addressToNat (state.storageAddr 0)) = false := by
      cases h_eq : (addressToNat sender == addressToNat (state.storageAddr 0))
      · rfl
      · -- If Nat equality holds, injectivity gives sender = owner, contradicting h
        exfalso
        have h_nat : addressToNat sender = addressToNat (state.storageAddr 0) := by
          simpa [beq_iff_eq] using h_eq
        have h_addr : sender = state.storageAddr 0 :=
          addressToNat_injective sender (state.storageAddr 0) h_nat
        exact h h_addr.symm
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h_beq]

/-- The `decrement` function correctly decrements when called by owner -/
theorem ownedCounter_decrement_correct_as_owner (state : ContractState) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := decrement.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 1 = (edslResult.getState.storage 1).val := by
  constructor
  · -- EDSL success when sender is owner
    unfold DumbContracts.Examples.OwnedCounter.decrement Contract.run
    unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
    unfold msgSender getStorageAddr setStorage DumbContracts.Examples.OwnedCounter.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = true := by
      rw [beq_iff_eq, h]
    rw [h_beq]
    simp [ContractResult.isSuccess, getStorage, setStorage]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_owner' : ({ state with sender := sender }).sender =
        ({ state with sender := sender }).storageAddr 0 := by
      simp [h]
    have h_dec :
        ((decrement.run { state with sender := sender }).getState.storage 1) =
          DumbContracts.EVM.Uint256.sub (state.storage 1) 1 := by
      simpa [ContractResult.getState, ContractResult.snd] using
        (decrement_subtracts_one_when_owner (s := { state with sender := sender }) h_owner')
    have h_dec_val :
        ((decrement.run { state with sender := sender }).getState.storage 1).val =
          (if 1 % DumbContracts.Core.Uint256.modulus ≤ (state.storage 1).val then
            (state.storage 1).val - 1 % DumbContracts.Core.Uint256.modulus
          else
            DumbContracts.Core.Uint256.modulus -
              (1 % DumbContracts.Core.Uint256.modulus - (state.storage 1).val)) := by
      simpa [h_dec] using (uint256_sub_val (state.storage 1) 1)
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, h_dec_val, lookup_slot_second]

/-- The `decrement` function correctly reverts when called by non-owner -/
theorem ownedCounter_decrement_reverts_as_nonowner (state : ContractState) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := decrement.run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "decrement"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  constructor
  · -- EDSL reverts when sender is not owner
    unfold DumbContracts.Examples.OwnedCounter.decrement Contract.run
    unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
    unfold msgSender getStorageAddr setStorage DumbContracts.Examples.OwnedCounter.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = false := by
      cases h_eq : (sender == state.storageAddr 0)
      · rfl
      · rw [beq_iff_eq] at h_eq
        exfalso
        exact h h_eq.symm
    rw [h_beq]
    simp [ContractResult.isSuccess, getStorage, setStorage]
  · -- Spec reverts when sender is not owner
    have h_beq : (addressToNat sender == addressToNat (state.storageAddr 0)) = false := by
      cases h_eq : (addressToNat sender == addressToNat (state.storageAddr 0))
      · rfl
      · exfalso
        have h_nat : addressToNat sender = addressToNat (state.storageAddr 0) := by
          simpa [beq_iff_eq] using h_eq
        have h_addr : sender = state.storageAddr 0 :=
          addressToNat_injective sender (state.storageAddr 0) h_nat
        exact h h_addr.symm
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h_beq]

/-- The `getCount` function correctly retrieves the counter value -/
theorem ownedCounter_getCount_correct (state : ContractState) (sender : Address) :
    let edslValue := (getCount.runValue { state with sender := sender }).val
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getCount"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  unfold DumbContracts.Examples.OwnedCounter.getCount Contract.runValue ownedCounterSpec interpretSpec ownedCounterEdslToSpecStorage
  simp [getStorage, DumbContracts.Examples.OwnedCounter.count, execFunction, execStmts, execStmt, evalExpr,
    SpecStorage.getSlot, lookup_slot_second]

/-- The `getOwner` function correctly retrieves the owner address -/
theorem ownedCounter_getOwner_correct (state : ContractState) (sender : Address) :
    let edslAddr := getOwner.runValue { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getOwner"
      args := []
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some (addressToNat edslAddr) := by
  unfold DumbContracts.Examples.OwnedCounter.getOwner Contract.runValue ownedCounterSpec interpretSpec ownedCounterEdslToSpecStorage
  simp [getStorageAddr, DumbContracts.Examples.OwnedCounter.owner, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot]

/-- The `transferOwnership` function correctly transfers ownership when called by owner -/
theorem ownedCounter_transferOwnership_correct_as_owner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (transferOwnership newOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [addressToNat newOwner]
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = addressToNat newOwner := by
  constructor
  · -- EDSL success when sender is owner
    unfold DumbContracts.Examples.OwnedCounter.transferOwnership Contract.run
    unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
    unfold msgSender getStorageAddr setStorageAddr DumbContracts.Examples.OwnedCounter.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = true := by
      rw [beq_iff_eq, h]
    rw [h_beq]
    simp [ContractResult.isSuccess]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec sets owner to newOwner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_eq]

/- Helper Properties -/

/-- Getter functions preserve state -/
theorem ownedCounter_getters_preserve_state (state : ContractState) (sender : Address) :
    let countState := getCount.runState { state with sender := sender }
    let ownerState := getOwner.runState { state with sender := sender }
    countState.storage 1 = state.storage 1 ∧
    ownerState.storageAddr 0 = state.storageAddr 0 := by
  unfold DumbContracts.Examples.OwnedCounter.getCount DumbContracts.Examples.OwnedCounter.getOwner Contract.runState
  simp [getStorage, getStorageAddr, DumbContracts.Examples.OwnedCounter.count, DumbContracts.Examples.OwnedCounter.owner]

/-- Only owner can modify counter -/
theorem ownedCounter_only_owner_modifies (state : ContractState) (sender : Address) :
    (increment.run { state with sender := sender }).isSuccess = true →
    state.storageAddr 0 = sender := by
  intro h_success
  have h_onlyOwner :
      ((onlyOwner).run { state with sender := sender }).isSuccess = true := by
    simpa [increment, Contract.run] using
      (DumbContracts.Proofs.Stdlib.Automation.bind_isSuccess_left
        (m1 := onlyOwner)
        (m2 := fun _ =>
          DumbContracts.bind (getStorage count) (fun current =>
            setStorage count (DumbContracts.EVM.Uint256.add current 1)))
        (state := { state with sender := sender })
        h_success)
  have h_require_success :
      ((require (sender == state.storageAddr 0) "Caller is not the owner").run
        { state with sender := sender }).isSuccess = true := by
    simpa [onlyOwner, isOwner, msgSender, getStorageAddr, Contract.run, DumbContracts.bind, DumbContracts.pure]
      using h_onlyOwner
  have h_eq : (sender == state.storageAddr 0) = true :=
    DumbContracts.Proofs.Stdlib.Automation.require_success_implies_cond
      (cond := sender == state.storageAddr 0)
      (msg := "Caller is not the owner")
      (state := { state with sender := sender })
      h_require_success
  exact
    (DumbContracts.Proofs.Stdlib.Automation.address_beq_eq_true_iff_eq sender (state.storageAddr 0)).1
        h_eq
      |>.symm

/-- Owner and count slots are independent -/
theorem ownedCounter_slots_independent (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let finalState := (transferOwnership newOwner).runState { state with sender := sender }
    finalState.storage 1 = state.storage 1 := by
  unfold DumbContracts.Examples.OwnedCounter.transferOwnership DumbContracts.Examples.OwnedCounter.onlyOwner
  unfold DumbContracts.Examples.OwnedCounter.isOwner DumbContracts.Examples.OwnedCounter.owner
  unfold msgSender getStorageAddr setStorageAddr Contract.runState
  simp only [DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure, DumbContracts.require]
  have h_beq : (sender == state.storageAddr 0) = true := by
    simp [beq_iff_eq, h]
  simp [h_beq]

end Compiler.Proofs.SpecCorrectness
