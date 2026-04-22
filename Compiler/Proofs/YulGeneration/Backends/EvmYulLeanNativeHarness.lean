import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics
import Compiler.Codegen
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

/-- Decode one 32-byte big-endian word from an EVMYulLean byte array. -/
def byteArrayWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => (acc * 256 + ((bytes.get? (offset + i)).getD 0).toNat) %
      Compiler.Constants.evmModulus)
    0

/-- Decode the word-granular payload used by Verity's proof-side log model. -/
def byteArrayLogWords (bytes : ByteArray) : List Nat :=
  (List.range (bytes.size / 32)).map (fun i => byteArrayWord bytes (i * 32))

/-- Project native EVMYulLean logs to the current Verity observable event shape:
    topics followed by word-aligned log data. -/
def projectLogEntry (entry : EvmYul.LogEntry) : List Nat :=
  entry.topics.toList.map uint256ToNat ++ byteArrayLogWords entry.data

def projectLogsFromState (state : EvmYul.Yul.State) : List (List Nat) :=
  state.sharedState.substate.logSeries.toList.map projectLogEntry

/-- Project a native Yul halt produced by `return`/`stop` to Verity's single-word
    return observable. EVMYulLean represents `stop` as `YulHalt _ 0`; `return`
    goes through `H_return`, matching the proof oracle's 32-byte return case. -/
def projectHaltReturn (state : EvmYul.Yul.State) (haltValue : EvmYul.Yul.Ast.Literal) :
    Option Nat :=
  if haltValue = ⟨0⟩ then
    none
  else if state.sharedState.H_return.size = 32 then
    some (byteArrayWord state.sharedState.H_return 0)
  else
    some 0

/-- Convert a native `callDispatcher` result to the current Verity observable
    result shape. Reverts and hard native errors conservatively roll storage
    back to the supplied initial storage function. -/
def projectResult
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
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
        events := initialEvents ++ projectLogsFromState state }
  | .error (.YulHalt state value) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := projectHaltReturn state value
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := initialEvents ++ projectLogsFromState state }
  | .error _ =>
      { success := false
        returnValue := none
        finalStorage := initialStorage
        finalMappings := Compiler.Proofs.storageAsMappings initialStorage
        events := initialEvents }

@[simp] theorem projectResult_revert
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert) =
    { success := false
      returnValue := none
      finalStorage := initialStorage
      finalMappings := Compiler.Proofs.storageAsMappings initialStorage
      events := initialEvents } := by
  rfl

/-- Lower and execute Verity runtime Yul through EVMYulLean's native
    dispatcher. -/
def interpretRuntimeNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (events : List (List Nat) := []) :
    Except AdapterError YulResult := do
  let contract ← lowerRuntimeContractNative runtimeCode
  let initial := initialState contract tx storage observableSlots
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage events result)

/-- Native EVMYulLean execution target for emitted IR-contract runtime Yul.

This is the executable target that #1737 will promote into the public theorem
path once the state/result bridge lemmas are proved. It intentionally returns
`Except AdapterError YulResult` today because native lowering can still fail
closed for duplicate helper definitions or unsupported runtime shapes.

The observable slot set is explicit because the native state bridge only
materializes pre-state storage for the listed slots. Passing `[]` is valid for
storage-free smoke tests, but storage-reading callers must provide every slot
they intend the native EVMYulLean state to observe.
-/
def interpretIRRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    Except AdapterError YulResult :=
  interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
    (YulTransaction.ofIR tx) state.storage observableSlots state.events

@[simp] theorem interpretIRRuntimeNative_eq_interpretRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) state.storage observableSlots state.events := by
  rfl

end Compiler.Proofs.YulGeneration.Backends.Native
