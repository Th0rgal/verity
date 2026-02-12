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
import Compiler.Proofs.SpecInterpreter
import Compiler.Hex
import DumbContracts.Examples.Owned
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open Compiler.Hex
open DumbContracts
open DumbContracts.Examples.Owned

/- State Conversion -/

/-- Convert EDSL ContractState to SpecStorage for Owned -/
def ownedEdslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, addressToNat (state.storageAddr 0))]
    mappings := [] }

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
  simp [ContractResult.isSuccess, ContractResult.getState]

  -- After simplification, we need: addressToNat initialOwner % (2^256) = addressToNat initialOwner
  -- This holds because Ethereum addresses are 160-bit, so addressToNat < 2^160 < 2^256
  -- Therefore: addressToNat % 2^256 = addressToNat (modulo is identity)
  sorry  -- TODO: Prove addressToNat bounds (requires parseHexNat? specification)

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
  unfold DumbContracts.Examples.Owned.transferOwnership Contract.run ownedSpec interpretSpec ownedEdslToSpecStorage
  unfold DumbContracts.Examples.Owned.onlyOwner DumbContracts.Examples.Owned.isOwner
  simp [msgSender, getStorageAddr, setStorageAddr, DumbContracts.Examples.Owned.owner, DumbContracts.bind, DumbContracts.require, DumbContracts.pure]
  simp [execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot]
  -- The require passes when sender = owner
  simp [h]
  -- Show: addressToNat newOwner % modulus = addressToNat newOwner
  sorry -- Address encoding lemma needed

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
  unfold DumbContracts.Examples.Owned.transferOwnership Contract.run ownedSpec interpretSpec ownedEdslToSpecStorage
  unfold DumbContracts.Examples.Owned.onlyOwner DumbContracts.Examples.Owned.isOwner
  simp [msgSender, getStorageAddr, setStorageAddr, DumbContracts.Examples.Owned.owner, DumbContracts.bind, DumbContracts.require, DumbContracts.pure]
  simp [execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, SpecStorage.setSlot, ContractResult.isSuccess]
  -- The require fails when sender ≠ owner
  -- Need to show: sender = state.storageAddr 0 is false
  sorry -- Authorization check needs more work

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
    let result := (transferOwnership newOwner).run { state with sender := sender }
    result.isSuccess = true → state.storageAddr 0 = sender := by
  intro h_success

  -- Strategy: The key insight is that transferOwnership = onlyOwner >> setStorageAddr
  -- If it succeeds, onlyOwner must have succeeded, which means require (sender == owner) passed
  --
  -- This proof requires careful reasoning about:
  -- 1. Monadic bind: (m1 >> m2).isSuccess → m1.isSuccess
  -- 2. Require success: require cond succeeds → cond = true
  -- 3. Boolean equality: (a == b) = true → a = b for Address
  --
  -- All of these require automation lemmas that aren't yet in the Automation module.
  -- Rather than adding incomplete/hacky lemmas, we document this as a clear TODO.

  sorry -- TODO: Add automation for monadic authorization patterns

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
