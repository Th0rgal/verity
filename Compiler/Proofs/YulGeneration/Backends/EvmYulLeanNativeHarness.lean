import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics
import EvmYul.Yul.Interpreter

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge

/-!
Executable native EVMYulLean runtime harness for #1737.

This module deliberately sits beside the historical adapter.  The adapter is
part of the existing proof/report dependency graph; importing the state bridge
there would create a cycle through the reference oracle.  Keeping the native
harness separate lets tests and future proofs run `EvmYul.Yul.callDispatcher`
directly without disturbing the current verified backend path.
-/

/-- Build a native EVMYulLean state for a generated runtime contract.

The bridge starts from the flat Verity `YulState` projection, then installs the
lowered `YulContract` both in the execution environment and in the current
account. Runtime entrypoints are mutable by default (`perm := true`);
static-call-specific harnesses can override this later when #1737 widens to
external-call semantics.
-/
def initialState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    EvmYul.Yul.State :=
  let verityState := YulState.initial tx storage
  let shared := toSharedState verityState observableSlots
  let addr := natToAddress tx.thisAddress
  let account : EvmYul.Account .Yul :=
    match shared.accountMap.find? addr with
    | some acc => { acc with code := contract }
    | none =>
        { nonce := ⟨0⟩
          balance := ⟨0⟩
          storage := projectStorage storage observableSlots
          code := contract
          tstorage := Batteries.RBMap.empty }
  let shared' : EvmYul.SharedState .Yul :=
    { shared with
      accountMap := shared.accountMap.insert addr account
      executionEnv :=
        { shared.executionEnv with
          code := contract
          perm := true } }
  .Ok shared' ∅

/-- Project the account storage for the current contract back to Verity's
    `Nat → Nat` storage view. -/
def projectStorageFromState (tx : YulTransaction) (state : EvmYul.Yul.State) :
    Nat → Nat :=
  extractStorage state.sharedState (natToAddress tx.thisAddress)

/-- Convert a native `callDispatcher` result to the current Verity observable
    result shape. Reverts and hard native errors conservatively roll storage
    back to the supplied initial storage function. -/
def projectResult
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    YulResult :=
  match result with
  | .ok (state, values) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := values.head?.map uint256ToNat
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := [] }
  | .error (.YulHalt state value) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := some (uint256ToNat value)
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := [] }
  | .error _ =>
      { success := false
        returnValue := none
        finalStorage := initialStorage
        finalMappings := Compiler.Proofs.storageAsMappings initialStorage
        events := [] }

/-- Lower and execute Verity runtime Yul through EVMYulLean's native
    dispatcher. -/
def interpretRuntimeNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat := []) :
    Except AdapterError YulResult := do
  let contract ← lowerRuntimeContractNative runtimeCode
  let initial := initialState contract tx storage observableSlots
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage result)

end Compiler.Proofs.YulGeneration.Backends.Native
