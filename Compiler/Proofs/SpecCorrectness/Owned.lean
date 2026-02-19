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
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Proofs.Stdlib.Automation
import Verity.Examples.Owned
import Verity.Proofs.Owned.Basic
import Verity.Proofs.Owned.Correctness

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity.Proofs.Stdlib.Automation
open Compiler.Hex
open Verity
open Verity.Examples.Owned

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Owned -/
def ownedEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, addressToNat (state.storageAddr 0))]
    mappings := []
    mappings2 := []
    events := [] }

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
  simp [Verity.Examples.Owned.constructor, Contract.run, ownedSpec, interpretSpec,
    setStorageAddr, Verity.Examples.Owned.owner, Verity.bind, Verity.pure]
  simp [execConstructor, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot, SpecStorage.empty]

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
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  refine ⟨?_, ?_, ?_⟩
  · -- EDSL success when sender is owner
    rw [Verity.Proofs.Owned.transferOwnership_unfold _ _ h_owner']
    simp [ContractResult.isSuccess]
  · -- Spec success when sender is owner
    simp [ownedSpec, requireOwner, interpretSpec, ownedEdslToSpecStorage, execFunction, execStmts, execStmt,
      evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, h]
  · -- Spec sets owner to newOwner
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
  have h_ne : ({ state with sender := sender }).sender ≠
      ({ state with sender := sender }).storageAddr 0 := by simp [Ne.symm h]
  refine ⟨?_, ?_⟩
  · -- EDSL reverts when sender is not owner
    obtain ⟨_, h_revert⟩ := Verity.Proofs.Owned.Correctness.transferOwnership_reverts_when_not_owner _ newOwner h_ne
    simp [h_revert, ContractResult.isSuccess]
  · -- Spec reverts when sender is not owner
    simp [ownedSpec, requireOwner, interpretSpec, ownedEdslToSpecStorage, execFunction, execStmts, execStmt,
      evalExpr, SpecStorage.getSlot, SpecStorage.setSlot,
      addressToNat_beq_false_of_ne sender (state.storageAddr 0) (Ne.symm h)]

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
  simp [Verity.Examples.Owned.getOwner, Contract.runValue, ownedSpec, interpretSpec, ownedEdslToSpecStorage,
    getStorageAddr, Verity.Examples.Owned.owner, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot]

/- Helper Properties -/

/-- `getOwner` does not modify storage -/
theorem getOwner_preserves_state (state : ContractState) (sender : Address) :
    let finalState := getOwner.runState { state with sender := sender }
    finalState.storageAddr 0 = state.storageAddr 0 := by
  simp [Verity.Examples.Owned.getOwner, Contract.runState, getStorageAddr, Verity.Examples.Owned.owner]

/-- Only owner can transfer ownership -/
theorem only_owner_can_transfer (state : ContractState) (newOwner : Address) (sender : Address) :
    ((transferOwnership newOwner).run { state with sender := sender }).isSuccess = true →
    state.storageAddr 0 = sender := by
  intro h_success
  have h_require_success :
      ((require (sender == state.storageAddr 0) "Caller is not the owner").run
        { state with sender := sender }).isSuccess = true := by
    simpa [onlyOwner, isOwner, msgSender, getStorageAddr, Contract.run, Verity.bind, Verity.pure,
      transferOwnership] using
      Verity.Proofs.Stdlib.Automation.bind_isSuccess_left
        (m1 := onlyOwner)
        (m2 := fun _ => setStorageAddr owner newOwner)
        (state := { state with sender := sender })
        h_success
  exact (require_beq_success_implies_eq sender (state.storageAddr 0)
    "Caller is not the owner" _ h_require_success).symm

/-- Constructor sets initial owner correctly -/
theorem constructor_sets_owner (state : ContractState) (initialOwner : Address) (sender : Address) :
    let finalState := (constructor initialOwner).runState { state with sender := sender }
    finalState.storageAddr 0 = initialOwner := by
  simp [Verity.Examples.Owned.constructor, Contract.runState, setStorageAddr, Verity.Examples.Owned.owner, Verity.bind]

/-- TransferOwnership updates owner when authorized -/
theorem transferOwnership_updates_owner (state : ContractState) (newOwner : Address) (sender : Address)
    (h : state.storageAddr 0 = sender) :
    let finalState := (Verity.Examples.Owned.transferOwnership newOwner).runState { state with sender := sender }
    finalState.storageAddr 0 = newOwner := by
  have h_owner' : ({ state with sender := sender }).sender =
      ({ state with sender := sender }).storageAddr 0 := by simp [h]
  change ((Verity.Examples.Owned.transferOwnership newOwner).run { state with sender := sender }).snd.storageAddr 0 = newOwner
  rw [Verity.Proofs.Owned.transferOwnership_unfold _ _ h_owner']; rfl

end Compiler.Proofs.SpecCorrectness
