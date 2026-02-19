/-
  Compiler.Proofs.SpecCorrectness.SimpleStorage

  Prove that simpleStorageSpec accurately represents the SimpleStorage EDSL.

  This establishes that the manually written ContractSpec matches
  the verified EDSL semantics for SimpleStorage.

  Strategy:
  - Define simple state conversion between EDSL and Spec
  - Prove store and retrieve functions produce equivalent results
  - Show spec interpretation matches EDSL execution
-/

import Compiler.Specs
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Examples.SimpleStorage

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Verity.Proofs.Stdlib.SpecInterpreter
open Verity
open Verity.Examples
open Verity.Core.Uint256

/-!
## State Conversion

SimpleStorage has one uint256 field at slot 0.
Convert between EDSL ContractState (which stores Uint256)
and SpecStorage (which stores Nat).
-/

-- Convert EDSL state to SpecStorage
def edslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := []
    mappings2 := []
    events := [] }

/-!
## Correctness Theorems

Prove that spec functions match EDSL functions.
All proofs are complete with no sorry placeholders.
-/

-- Store function correctness
theorem store_correct (state : ContractState) (value : Nat) (sender : Address) :
    let edslFinal := (store (ofNat value)).runState { state with sender := sender }
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "store"
      args := [value]
    }
    let specResult := interpretSpec simpleStorageSpec (edslToSpecStorage state) specTx
    -- Both succeed and update slot 0 to value
    specResult.success = true ∧
    specResult.finalStorage.getSlot 0 = (edslFinal.storage 0).val := by
  simp [store, simpleStorageSpec, interpretSpec, edslToSpecStorage, Contract.runState,
    setStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.setSlot, SpecStorage.getSlot, storedData, modulus, val_ofNat]

-- Retrieve function correctness
theorem retrieve_correct (state : ContractState) (sender : Address) :
    let edslValue := (retrieve.runValue { state with sender := sender }).val
    let specTx : DiffTestTypes.Transaction := {
      sender := sender
      functionName := "retrieve"
      args := []
    }
    let specResult := interpretSpec simpleStorageSpec (edslToSpecStorage state) specTx
    -- Both succeed and return same value
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  simp [retrieve, Contract.runValue, simpleStorageSpec, interpretSpec, edslToSpecStorage,
    getStorage, execFunction, execStmts, execStmt, evalExpr, SpecStorage.getSlot, storedData]

/-!
## Helper Properties

Properties that follow from the spec being correct.
-/

-- Retrieve doesn't modify state
theorem retrieve_preserves_state (state : ContractState) (sender : Address) :
    let result := retrieve.runState { state with sender := sender }
    result.storage = state.storage := by
  simp [retrieve, Contract.runState, getStorage]

-- Store-retrieve roundtrip
theorem store_retrieve_roundtrip (value : Nat) (sender : Address) (state : ContractState) :
    let state1 := (store (ofNat value)).runState { state with sender := sender }
    let retrieved := retrieve.runValue { state1 with sender := sender }
    retrieved.val = value % modulus := by
  simp [store, retrieve, Contract.runState, Contract.runValue, setStorage, getStorage, storedData, val_ofNat]

end Compiler.Proofs.SpecCorrectness
