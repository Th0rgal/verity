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
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Proofs.Stdlib.Automation
import Verity.Examples.OwnedCounter
import Verity.Proofs.OwnedCounter.Basic

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity.Proofs.Stdlib.Automation
open Verity
open Verity.Examples.OwnedCounter
open Verity.Proofs.OwnedCounter

-- Address encoding lemmas are provided by Automation.

-- Helper: EVM add (Uint256) matches modular Nat addition.
-- (uint256_add_val) is provided by Automation.

-- (uint256_sub_val) is provided by Automation.

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for OwnedCounter -/
def ownedCounterEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [
      (0, (state.storageAddr 0).val),  -- owner at slot 0
      (1, (state.storage 1).val)                -- count at slot 1
    ]
    mappings := []
    mappings2 := []
    events := [] }

/- Correctness Theorems -/

/-- The `constructor` correctly initializes the owner -/
theorem ownedCounter_constructor_correct (state : ContractState) (initialOwner : Address) (sender : Address) :
    let edslResult := (constructor initialOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := ""
      args := [initialOwner.val]
    }
    let specResult := interpretSpec ownedCounterSpec SpecStorage.empty specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslResult.getState.storageAddr 0).val := by
  simp [Verity.Examples.OwnedCounter.constructor, Contract.run, ownedCounterSpec, interpretSpec,
    setStorageAddr, Verity.Examples.OwnedCounter.owner,
    execConstructor, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty]

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
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  refine ⟨?_, ?_, ?_⟩
  · -- EDSL success when sender is owner
    rw [increment_unfold _ h_owner']; simp [ContractResult.isSuccess]
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_inc_val :
        ((increment.run { state with sender := sender }).getState.storage 1).val =
          ((state.storage 1).val + 1) % Verity.Core.Uint256.modulus := by
      have h_inc := increment_adds_one_when_owner (s := { state with sender := sender }) h_owner'
      simpa [ContractResult.getState, ContractResult.snd, uint256_add_val] using
        congrArg Verity.Core.Uint256.val h_inc
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, h_inc_val]

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
  have h_ne : ({ state with sender := sender }).sender ≠
      ({ state with sender := sender }).storageAddr 0 := by simp [Ne.symm h]
  refine ⟨?_, ?_⟩
  · -- EDSL reverts when sender is not owner
    obtain ⟨_, h_revert⟩ := increment_reverts_when_not_owner _ h_ne
    simp [h_revert, ContractResult.isSuccess]
  · -- Spec reverts when sender is not owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot,
      addressToNat_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)]

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
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  refine ⟨?_, ?_, ?_⟩
  · -- EDSL success when sender is owner
    rw [decrement_unfold _ h_owner']; simp [ContractResult.isSuccess]
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_dec_val :
        ((decrement.run { state with sender := sender }).getState.storage 1).val =
          (if 1 % Verity.Core.Uint256.modulus ≤ (state.storage 1).val then
            (state.storage 1).val - 1 % Verity.Core.Uint256.modulus
          else
            Verity.Core.Uint256.modulus -
              (1 % Verity.Core.Uint256.modulus - (state.storage 1).val)) := by
      have h_dec := decrement_subtracts_one_when_owner (s := { state with sender := sender }) h_owner'
      simpa [ContractResult.getState, ContractResult.snd] using
        (congrArg Verity.Core.Uint256.val h_dec).trans (uint256_sub_val (state.storage 1) 1)
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, h_dec_val]

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
  have h_ne : ({ state with sender := sender }).sender ≠
      ({ state with sender := sender }).storageAddr 0 := by simp [Ne.symm h]
  refine ⟨?_, ?_⟩
  · -- EDSL reverts when sender is not owner
    obtain ⟨_, h_revert⟩ := decrement_reverts_when_not_owner _ h_ne
    simp [h_revert, ContractResult.isSuccess]
  · -- Spec reverts when sender is not owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot,
      addressToNat_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)]

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
  simp [Verity.Examples.OwnedCounter.getCount, Contract.runValue, ownedCounterSpec, interpretSpec,
    ownedCounterEdslToSpecStorage, getStorage, Verity.Examples.OwnedCounter.count, execFunction,
    execStmts, execStmt, evalExpr, SpecStorage.getSlot]

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
    specResult.returnValue = some edslAddr.val := by
  simp [Verity.Examples.OwnedCounter.getOwner, Contract.runValue, ownedCounterSpec, interpretSpec,
    ownedCounterEdslToSpecStorage, getStorageAddr, Verity.Examples.OwnedCounter.owner, execFunction,
    execStmts, execStmt, evalExpr, SpecStorage.getSlot]

/-- The `transferOwnership` function correctly transfers ownership when called by owner -/
theorem ownedCounter_transferOwnership_correct_as_owner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (transferOwnership newOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [newOwner.val]
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = newOwner.val := by
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  refine ⟨?_, ?_, ?_⟩
  · -- EDSL success when sender is owner
    rw [transferOwnership_unfold _ _ h_owner']; simp [ContractResult.isSuccess]
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec sets owner to newOwner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_eq]

/-- The `transferOwnership` function correctly reverts when called by non-owner -/
theorem ownedCounter_transferOwnership_reverts_as_nonowner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (transferOwnership newOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [newOwner.val]
    }
    let specResult := interpretSpec ownedCounterSpec (ownedCounterEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  have h_ne : ({ state with sender := sender }).sender ≠
      ({ state with sender := sender }).storageAddr 0 := by simp [Ne.symm h]
  refine ⟨?_, ?_⟩
  · -- EDSL reverts when sender is not owner
    obtain ⟨_, h_revert⟩ := transferOwnership_reverts_when_not_owner _ newOwner h_ne
    simp [h_revert, ContractResult.isSuccess]
  · -- Spec reverts when sender is not owner
    simp [ownedCounterSpec, requireOwner, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot,
      addressToNat_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)]

/- Helper Properties -/

/-- Getter functions preserve state -/
theorem ownedCounter_getters_preserve_state (state : ContractState) (sender : Address) :
    let countState := getCount.runState { state with sender := sender }
    let ownerState := getOwner.runState { state with sender := sender }
    countState.storage 1 = state.storage 1 ∧
    ownerState.storageAddr 0 = state.storageAddr 0 := by
  simp [Verity.Examples.OwnedCounter.getCount, Verity.Examples.OwnedCounter.getOwner, Contract.runState,
    getStorage, getStorageAddr, Verity.Examples.OwnedCounter.count, Verity.Examples.OwnedCounter.owner]

/-- Only owner can modify counter -/
theorem ownedCounter_only_owner_modifies (state : ContractState) (sender : Address) :
    (increment.run { state with sender := sender }).isSuccess = true →
    state.storageAddr 0 = sender := by
  intro h_success
  have h_onlyOwner_success :
      (onlyOwner.run { state with sender := sender }).isSuccess = true := by
    simpa [increment, Contract.run, Verity.bind] using
      Verity.Proofs.Stdlib.Automation.bind_isSuccess_left
        (m1 := onlyOwner)
        (m2 := fun _ =>
          Verity.bind (getStorage count) (fun current =>
            setStorage count (Verity.EVM.Uint256.add current 1)))
        (state := { state with sender := sender })
        h_success
  simpa [onlyOwner, isOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, Verity.pure]
    using Verity.Proofs.Stdlib.Automation.owner_guard_success_implies_storageAddr_eq_sender
      (slot := owner)
      (msg := "Caller is not the owner")
      (state := { state with sender := sender })
      h_onlyOwner_success

/-- Owner and count slots are independent -/
theorem ownedCounter_slots_independent (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let finalState := (transferOwnership newOwner).runState { state with sender := sender }
    finalState.storage 1 = state.storage 1 := by
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  change ((transferOwnership newOwner).run { state with sender := sender }).snd.storage 1 = state.storage 1
  rw [transferOwnership_unfold _ _ h_owner']; rfl

end Compiler.Proofs.SpecCorrectness
