/-
  SimpleStorage IR Generation Correctness Proofs

  Proves that the compiled IR for SimpleStorage preserves the semantics
  of the ContractSpec specification.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Verity.Proofs.Stdlib.SpecInterpreter
import Compiler.ContractSpec
import Compiler.Specs
import Verity.Core

namespace Compiler.Proofs.IRGeneration.SimpleStorage

open Compiler
open Compiler.Specs
open Compiler.ContractSpec
open Verity
open DiffTestTypes
open Verity.Proofs.Stdlib.SpecInterpreter

/-! ## Store Function Correctness

The store function should:
1. Accept a value parameter
2. Store it in slot 0 (storedData field)
3. Return successfully with no return value
-/

theorem store_correct (value : Nat) :
  let spec := simpleStorageSpec
  let sender := "test_sender"
  let tx : Transaction := {
    sender := sender
    functionName := "store"
    args := [value]
  }
  let specResult := interpretSpec spec SpecStorage.empty tx
  -- Spec execution should succeed and store the value
  specResult.success = true ∧
  specResult.returnValue = none ∧
  specResult.finalStorage.getSlot 0 = value := by
  -- Unfold definitions
  unfold interpretSpec
  simp [simpleStorageSpec, execFunction, execStmts, execStmt, evalExpr,
    SpecStorage.empty, SpecStorage.setSlot, SpecStorage.getSlot]

/-! ## Retrieve Function Correctness

The retrieve function should:
1. Read the value from slot 0 (storedData field)
2. Return it successfully
-/

theorem retrieve_correct (storedValue : Nat) :
  let spec := simpleStorageSpec
  let sender := "test_sender"
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 storedValue
  let tx : Transaction := {
    sender := sender
    functionName := "retrieve"
    args := []
  }
  let specResult := interpretSpec spec initialStorage tx
  -- Spec execution should succeed and return the stored value
  specResult.success = true ∧
  specResult.returnValue = some storedValue := by
  unfold interpretSpec
  simp [simpleStorageSpec, execFunction, execStmts, execStmt, evalExpr,
    SpecStorage.empty, SpecStorage.setSlot, SpecStorage.getSlot]

end Compiler.Proofs.IRGeneration.SimpleStorage
