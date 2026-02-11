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
import Compiler.Proofs.SpecInterpreter
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Core.Uint256

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open Compiler.Specs
open Compiler.Proofs
open DumbContracts
open DumbContracts.Examples
open DumbContracts.Core.Uint256

/-!
## State Conversion

SimpleStorage has one uint256 field at slot 0.
Convert between EDSL ContractState (which stores Uint256)
and SpecStorage (which stores Nat).
-/

-- Convert EDSL state to SpecStorage
def edslToSpecStorage (state : ContractState) : SpecStorage :=
  { slots := [(0, (state.storage 0).val)]
    mappings := [] }

/-!
## Correctness Theorems

Prove that spec functions match EDSL functions.
We use `sorry` placeholders as this is a template proof structure.
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
  sorry

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
  sorry

/-!
## Helper Properties

Properties that follow from the spec being correct.
-/

-- Retrieve doesn't modify state
theorem retrieve_preserves_state (state : ContractState) (sender : Address) :
    let result := retrieve.runState { state with sender := sender }
    result.storage = state.storage := by
  -- This follows from getStorage not modifying storage
  -- Proof requires: unfold retrieve, getStorage, Contract.runState
  -- and case analysis on ContractResult
  sorry

-- Store-retrieve roundtrip
theorem store_retrieve_roundtrip (value : Nat) (sender : Address) (state : ContractState) :
    let state1 := (store (ofNat value)).runState { state with sender := sender }
    let retrieved := retrieve.runValue { state1 with sender := sender }
    retrieved.val = value % modulus := by
  -- This follows from:
  -- 1. store sets slot 0 to (ofNat value)
  -- 2. retrieve reads slot 0
  -- 3. (ofNat value).val = value % modulus
  -- Proof requires additional automation lemmas for runState/runValue
  sorry

end Compiler.Proofs.SpecCorrectness
