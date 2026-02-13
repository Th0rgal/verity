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
import Compiler.Proofs.SpecInterpreter
import Compiler.Proofs.SpecCorrectness.AddressEncoding
import Compiler.Proofs.Automation
import Compiler.Hex
import DumbContracts.Examples.OwnedCounter
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Proofs.Automation
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.OwnedCounter

-- Trust assumption: address encoding is injective for valid addresses.
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
  simp [execConstructor, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot,
    SpecStorage.empty, addressToNat_mod_address]

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
    have h_beq : (sender == state.storageAddr 0) = true := by
      simp [beq_iff_eq, h]
    simp [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure,
      h_beq, ContractResult.isSuccess, getStorage, setStorage]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_edsl :
        ((increment.run { state with sender := sender }).getState.storage 1).val =
          ((state.storage 1).val + 1) % DumbContracts.Core.Uint256.modulus := by
      have h_state :
          (increment.run { state with sender := sender }).getState.storage 1 =
            DumbContracts.EVM.Uint256.add (state.storage 1) 1 := by
        unfold DumbContracts.Examples.OwnedCounter.increment
        unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
        unfold msgSender getStorageAddr getStorage setStorage DumbContracts.Examples.OwnedCounter.owner
        have h_beq : (sender == state.storageAddr 0) = true := by
          simp [beq_iff_eq, h]
        simp [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure,
          h_beq, Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          DumbContracts.Examples.OwnedCounter.count]
      have h_state_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_state
      simpa [uint256_add_val] using h_state_val
    have h_lookup :
        (List.lookup 1 [(0, addressToNat sender), (1, (state.storage 1).val)]).getD 0 =
          (state.storage 1).val := by
      simp [List.lookup]
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_address,
      h_lookup, h_edsl]

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
    simp [ContractResult.isSuccess]
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
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h_beq, addressToNat_mod_address]

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
    have h_beq : (sender == state.storageAddr 0) = true := by
      simp [beq_iff_eq, h]
    simp [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure,
      h_beq, ContractResult.isSuccess, getStorage, setStorage]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec storage count equals EDSL count
    have h_edsl :
        ((decrement.run { state with sender := sender }).getState.storage 1).val =
          (if 1 ≤ (state.storage 1).val then
              ((state.storage 1).val - 1) % DumbContracts.Core.Uint256.modulus
            else
              (DumbContracts.Core.Uint256.modulus - (1 - (state.storage 1).val)) %
                DumbContracts.Core.Uint256.modulus) := by
      have h_state :
          (decrement.run { state with sender := sender }).getState.storage 1 =
            DumbContracts.EVM.Uint256.sub (state.storage 1) 1 := by
        unfold DumbContracts.Examples.OwnedCounter.decrement
        unfold DumbContracts.Examples.OwnedCounter.onlyOwner DumbContracts.Examples.OwnedCounter.isOwner
        unfold msgSender getStorageAddr getStorage setStorage DumbContracts.Examples.OwnedCounter.owner
        have h_beq : (sender == state.storageAddr 0) = true := by
          simp [beq_iff_eq, h]
        simp [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure,
          h_beq, Contract.run, ContractResult.getState, ContractResult.snd, ContractResult.fst,
          DumbContracts.Examples.OwnedCounter.count]
      have h_state_val := congrArg (fun v : DumbContracts.Core.Uint256 => v.val) h_state
      simpa [DumbContracts.EVM.Uint256.sub, DumbContracts.Core.Uint256.sub, DumbContracts.Core.Uint256.val_ofNat]
        using h_state_val
    have h_lookup :
        (List.lookup 1 [(0, addressToNat sender), (1, (state.storage 1).val)]).getD 0 =
          (state.storage 1).val := by
      simp [List.lookup]
    have h_mod_one : 1 % DumbContracts.Core.Uint256.modulus = 1 := by
      exact Nat.mod_eq_of_lt (by decide : 1 < DumbContracts.Core.Uint256.modulus)
    have h_norm :
        (if 1 ≤ (state.storage 1).val then (state.storage 1).val - 1
          else DumbContracts.Core.Uint256.modulus - (1 - (state.storage 1).val)) =
        (if 1 ≤ (state.storage 1).val then ((state.storage 1).val - 1) % DumbContracts.Core.Uint256.modulus
          else (DumbContracts.Core.Uint256.modulus - (1 - (state.storage 1).val)) %
            DumbContracts.Core.Uint256.modulus) := by
      by_cases h_le : 1 ≤ (state.storage 1).val
      · have h_lt : (state.storage 1).val - 1 < DumbContracts.Core.Uint256.modulus := by
          exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (state.storage 1).isLt
        simp [h_le, Nat.mod_eq_of_lt h_lt]
      · have h_lt1 : (state.storage 1).val < 1 := Nat.lt_of_not_ge h_le
        have h_le0 : (state.storage 1).val ≤ 0 := (Nat.lt_succ_iff).mp h_lt1
        have h_zero : (state.storage 1).val = 0 := Nat.le_antisymm h_le0 (Nat.zero_le _)
        have h_lt : DumbContracts.Core.Uint256.modulus - (1 - (state.storage 1).val) <
            DumbContracts.Core.Uint256.modulus := by
          simpa [h_zero] using
            (Nat.sub_lt (by decide : 0 < DumbContracts.Core.Uint256.modulus) (by decide : 0 < 1))
        simp [h_le, h_zero, Nat.mod_eq_of_lt h_lt]
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_address,
      h_lookup, h_edsl, h_mod_one, h_norm]

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
    simp [ContractResult.isSuccess]
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
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
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
    SpecStorage.getSlot, addressToNat_mod_address, List.lookup]

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
  simp [getStorageAddr, DumbContracts.Examples.OwnedCounter.owner, execFunction, execStmts, execStmt, evalExpr,
    SpecStorage.getSlot, addressToNat_mod_address, List.lookup]

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
    have h_beq : (sender == state.storageAddr 0) = true := by
      simp [beq_iff_eq, h]
    simp [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure,
      h_beq, ContractResult.isSuccess, getStorageAddr, setStorageAddr]
  constructor
  · -- Spec success when sender is owner
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_address]
  · -- Spec sets owner to newOwner
    simp [ownedCounterSpec, interpretSpec, ownedCounterEdslToSpecStorage, execFunction, execStmts,
      execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_address]

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
    (increment.run { state with sender := sender }).isSuccess = true → state.storageAddr 0 = sender := by
  intro h_success
  have h_onlyOwner :
      ((onlyOwner).run { state with sender := sender }).isSuccess = true := by
    simpa [increment, Contract.run] using
      (Automation.bind_isSuccess_left
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
    Automation.require_success_implies_cond
      (cond := sender == state.storageAddr 0)
      (msg := "Caller is not the owner")
      (state := { state with sender := sender })
      h_require_success
  exact ((Automation.address_beq_eq_true_iff_eq sender (state.storageAddr 0)).1 h_eq).symm

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
