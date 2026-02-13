/-
  Compiler.Proofs.SpecCorrectness.Owned

  Prove that ownedSpec accurately represents the Owned EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for Owned with ownership pattern.

  Strategy:
  - Define state conversion between EDSL and Spec (address → Nat)
  - Prove constructor correctly initializes owner
  - Prove transferOwnership and getOwner functions produce equivalent results
  - Handle authorization checks (require statements)
  - Show spec interpretation matches EDSL execution with access control
-/

import Compiler.Specs
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import DumbContracts.Proofs.Stdlib.Automation
import Compiler.Hex
import DumbContracts.Examples.Owned
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open DumbContracts.Proofs.Stdlib.SpecInterpreter
open DumbContracts.Proofs.Stdlib.Automation
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.Owned

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Owned -/
def ownedEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, addressToNat (state.storageAddr 0))]
    mappings := [] }

-- Address encoding lemmas are provided by Automation.

/- Correctness Theorems -/

/-- The `constructor` correctly initializes the owner -/
theorem owned_constructor_correct (state : ContractState) (initialOwner : Address) (sender : Address) :
    let edslResult := (constructor initialOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := ""  -- constructor has no name
      args := [addressToNat initialOwner]
    }
    let specResult := interpretSpec ownedSpec SpecStorage.empty specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = addressToNat (edslResult.getState.storageAddr 0) := by
  -- Constructor sets owner to initialOwner in both EDSL and spec
  unfold DumbContracts.Examples.Owned.constructor Contract.run ownedSpec interpretSpec
  simp [setStorageAddr, DumbContracts.Examples.Owned.owner, DumbContracts.bind, DumbContracts.pure]
  simp [execConstructor, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty]
  -- addressToNat_mod_eq is a simp lemma now.

/-- The `transferOwnership` function correctly transfers ownership when called by owner -/
theorem transferOwnership_correct_as_owner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let edslResult := (transferOwnership newOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [addressToNat newOwner]
    }
    let specResult := interpretSpec ownedSpec (ownedEdslToSpecStorage state) specTx
    edslResult.isSuccess = true ∧
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = addressToNat newOwner := by
  -- When sender is owner, both EDSL and spec succeed
  constructor
  · -- Part 1: edslResult.isSuccess = true
    unfold DumbContracts.Examples.Owned.transferOwnership Contract.run
    unfold DumbContracts.Examples.Owned.onlyOwner DumbContracts.Examples.Owned.isOwner
    unfold msgSender getStorageAddr setStorageAddr DumbContracts.Examples.Owned.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    have h_beq : (sender == state.storageAddr 0) = true := by
      rw [beq_iff_eq, h]
    rw [h_beq]
    simp [ContractResult.isSuccess]
  constructor
  · -- Part 2: specResult.success = true
    -- After unfolding, the spec evaluates: if sender == owner then execute else revert
    -- When h: sender = owner, the spec succeeds
    -- This requires simplifying nested Option.bind chains with evalExpr
    simp [ownedSpec, requireOwner, interpretSpec, ownedEdslToSpecStorage, execFunction, execStmts, execStmt,
      evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Part 3: specResult.finalStorage.getSlot 0 = addressToNat newOwner
    -- Similar to Part 2: requires Option.bind chain simplification
    -- When authorized, spec stores newOwner at slot 0
    simp [ownedSpec, requireOwner, interpretSpec, ownedEdslToSpecStorage, execFunction, execStmts, execStmt,
      evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h, addressToNat_mod_eq]

/-- The `transferOwnership` function correctly reverts when called by non-owner -/
theorem transferOwnership_reverts_as_nonowner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 ≠ sender) :
    let edslResult := (transferOwnership newOwner).run { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "transferOwnership"
      args := [addressToNat newOwner]
    }
    let specResult := interpretSpec ownedSpec (ownedEdslToSpecStorage state) specTx
    edslResult.isSuccess = false ∧
    specResult.success = false := by
  -- When sender is not owner, both EDSL and spec revert
  constructor
  · -- Part 1: edslResult.isSuccess = false
    unfold DumbContracts.Examples.Owned.transferOwnership Contract.run
    unfold DumbContracts.Examples.Owned.onlyOwner DumbContracts.Examples.Owned.isOwner
    unfold msgSender getStorageAddr setStorageAddr DumbContracts.Examples.Owned.owner
    simp only [DumbContracts.bind, Bind.bind, DumbContracts.require, DumbContracts.pure, Pure.pure]
    -- Show that (sender == state.storageAddr 0) = false when sender ≠ state.storageAddr 0
    have h_beq : (sender == state.storageAddr 0) = false := by
      cases h_eq : (sender == state.storageAddr 0)
      · rfl
      · -- If sender == state.storageAddr 0 is true, then they're equal
        rw [beq_iff_eq] at h_eq
        -- But this contradicts h
        exfalso
        exact h h_eq.symm
    rw [h_beq]
    simp [ContractResult.isSuccess]
  · -- Part 2: specResult.success = false
    -- Similar reasoning: spec checks sender == owner, which fails when h: sender ≠ owner
    -- By addressToNat_injective, we know addressToNat sender ≠ addressToNat owner
    -- So the require fails and spec reverts
    have h_beq : (addressToNat sender == addressToNat (state.storageAddr 0)) = false := by
      cases h_eq : (addressToNat sender == addressToNat (state.storageAddr 0))
      · rfl
      · -- If the Nat equality test is true, injectivity gives sender = owner, contradicting h
        exfalso
        have h_nat : addressToNat sender = addressToNat (state.storageAddr 0) := by
          -- beq_iff_eq for Nat
          simpa [beq_iff_eq] using h_eq
        have h_addr : sender = state.storageAddr 0 :=
          addressToNat_injective sender (state.storageAddr 0) h_nat
        exact h h_addr.symm
    -- Now the require in the spec fails, so success = false
    simp [ownedSpec, requireOwner, interpretSpec, ownedEdslToSpecStorage, execFunction, execStmts, execStmt,
      evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h_beq]

/-- The `getOwner` function correctly retrieves the owner address -/
theorem getOwner_correct (state : ContractState) (sender : Address) :
    let edslAddr := getOwner.runValue { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "getOwner"
      args := []
    }
    let specResult := interpretSpec ownedSpec (ownedEdslToSpecStorage state) specTx
    specResult.success = true ∧
    specResult.returnValue = some (addressToNat edslAddr) := by
  -- Same pattern as Counter.getCount_correct and SafeCounter.getCount_correct
  unfold DumbContracts.Examples.Owned.getOwner Contract.runValue ownedSpec interpretSpec ownedEdslToSpecStorage
  simp [getStorageAddr, DumbContracts.Examples.Owned.owner, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot]

/- Helper Properties -/

/-- `getOwner` does not modify storage -/
theorem getOwner_preserves_state (state : ContractState) (sender : Address) :
    let finalState := getOwner.runState { state with sender := sender }
    finalState.storageAddr 0 = state.storageAddr 0 := by
  -- getOwner just reads storage, doesn't modify it
  unfold DumbContracts.Examples.Owned.getOwner Contract.runState
  simp [getStorageAddr, DumbContracts.Examples.Owned.owner]

/-- Only owner can transfer ownership -/
theorem only_owner_can_transfer (state : ContractState) (newOwner : Address) (sender : Address) :
    ((transferOwnership newOwner).run { state with sender := sender }).isSuccess = true →
    state.storageAddr 0 = sender := by
  intro h_success
  -- If transferOwnership succeeds, onlyOwner must have succeeded.
  have h_onlyOwner :
      ((onlyOwner).run { state with sender := sender }).isSuccess = true := by
    -- Use bind success propagation from Automation
    simpa [transferOwnership, Contract.run] using
      (DumbContracts.Proofs.Stdlib.Automation.bind_isSuccess_left
        (m1 := onlyOwner)
        (m2 := fun _ => setStorageAddr owner newOwner)
        (state := { state with sender := sender })
        h_success)
  -- onlyOwner is just a require on isOwner, so success implies the condition holds.
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
  -- Convert boolean equality to propositional equality.
  exact
    (DumbContracts.Proofs.Stdlib.Automation.address_beq_eq_true_iff_eq sender (state.storageAddr 0)).1
        h_eq
      |>.symm

/-- Constructor sets initial owner correctly -/
theorem constructor_sets_owner (state : ContractState) (initialOwner : Address) (sender : Address) :
    let finalState := (constructor initialOwner).runState { state with sender := sender }
    finalState.storageAddr 0 = initialOwner := by
  -- Constructor simply sets storage at slot 0 to initialOwner
  unfold DumbContracts.Examples.Owned.constructor Contract.runState
  simp [setStorageAddr, DumbContracts.Examples.Owned.owner, DumbContracts.bind]

/-- TransferOwnership updates owner when authorized -/
theorem transferOwnership_updates_owner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let finalState := (DumbContracts.Examples.Owned.transferOwnership newOwner).runState { state with sender := sender }
    finalState.storageAddr 0 = newOwner := by
  -- Unfold all definitions
  unfold DumbContracts.Examples.Owned.transferOwnership DumbContracts.Examples.Owned.onlyOwner DumbContracts.Examples.Owned.isOwner DumbContracts.Examples.Owned.owner
  unfold msgSender getStorageAddr setStorageAddr Contract.runState
  simp only [DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure, DumbContracts.require]

  -- The key is that sender == state.storageAddr 0, so the require passes
  have h_beq : (sender == state.storageAddr 0) = true := by
    simp [beq_iff_eq, h]
  simp [h_beq]

end Compiler.Proofs.SpecCorrectness
