import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget

namespace Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

private def seededStorage : Nat -> Nat := fun slot =>
  if slot = 7 then 77 else 0

private def sampleIRTx (selector : Nat) (args : List Nat := []) : IRTransaction :=
  { sender := 0xCAFE
    msgValue := 7
    thisAddress := 0x1234
    blockTimestamp := 12345
    blockNumber := 678
    chainId := 31337
    blobBaseFee := 19
    functionSelector := selector
    args := args }

private def sampleIRState : IRState :=
  { vars := []
    storage := seededStorage
    transientStorage := fun _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := 0
    msgValue := 0
    thisAddress := 0
    blockTimestamp := 0
    blockNumber := 0
    chainId := 0
    blobBaseFee := 0
    selector := 0
    events := [[9, 9]] }

private def dispatchSmokeContract : IRContract :=
  { name := "NativeDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "left"
        selector := 0x11111111
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 11, .lit 101])
        ] },
      { name := "right"
        selector := 0x22222222
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 11, .lit 202])
        ] }
    ]
    usesMapping := false }

private def storageReadIRContract : IRContract :=
  { name := "NativeStorageReadOracleSmoke"
    deploy := []
    functions := [
      { name := "copySlot"
        selector := 0x44444444
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 8, .call "sload" [.lit 7]])
        ] }
    ]
    usesMapping := false }

private def returnDispatchSmokeContract : IRContract :=
  { name := "NativeReturnDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "answer"
        selector := 0x33333333
        params := []
        ret := .uint256
        body := [
          .expr (.call "mstore" [.lit 0, .lit 42]),
          .expr (.call "return" [.lit 0, .lit 32])
        ] }
    ]
    usesMapping := false }

private def multiWordReturnDispatchSmokeContract : IRContract :=
  { name := "NativeMultiWordReturnDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "pair"
        selector := 0x55555555
        params := []
        ret := .unit
        body := [
          .expr (.call "mstore" [.lit 0, .lit 41]),
          .expr (.call "mstore" [.lit 32, .lit 42]),
          .expr (.call "return" [.lit 0, .lit 64])
        ] }
    ]
    usesMapping := false }

private def memoryRevertDispatchSmokeContract : IRContract :=
  { name := "NativeMemoryRevertDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "fail"
        selector := 0x66666666
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 7, .lit 99]),
          .expr (.call "mstore" [.lit 0, .lit 0xDEAD]),
          .expr (.call "revert" [.lit 0, .lit 32])
        ] }
    ]
    usesMapping := false }

private def referenceRuntimeWithBackendFuel
    (fuel : Nat) (runtimeCode : List Compiler.Yul.YulStmt)
    (tx : YulTransaction) (storage : Nat -> Nat) (events : List (List Nat)) :
    YulResult :=
  let initialState := YulState.initial tx storage events
  yulResultOfExecWithRollback initialState
    (execYulFuelWithBackend .evmYulLean fuel initialState (.stmts runtimeCode))

private def resultsMatchOnSlots
    (slots : List Nat) (nativeResult referenceResult : YulResult) : Bool :=
  nativeResult.success == referenceResult.success &&
    nativeResult.returnValue == referenceResult.returnValue &&
    nativeResult.events == referenceResult.events &&
    slots.all (fun slot =>
      nativeResult.finalStorage slot == referenceResult.finalStorage slot)

private def emittedDispatchMatchesReference
    (contract : IRContract) (tx : IRTransaction)
    (observableSlots compareSlots : List Nat) : Except String Bool :=
  let yulTx := YulTransaction.ofIR tx
  let reference :=
    referenceRuntimeWithBackendFuel 256 (Compiler.emitYul contract).runtimeCode
      yulTx sampleIRState.storage sampleIRState.events
  match Native.interpretIRRuntimeNative 256 contract tx sampleIRState observableSlots with
  | .ok nativeResult => .ok (resultsMatchOnSlots compareSlots nativeResult reference)
  | .error _ => .error "native runtime lowering failed"

private def check (label : String) (actual : Except String Bool) : IO Unit := do
  match actual with
  | .ok true => IO.println s!"ok: {label}"
  | .ok false => throw (IO.userError s!"native/reference mismatch: {label}")
  | .error err => throw (IO.userError s!"{label}: {err}")

def main : IO Unit := do
  check "emitted dispatcher selects first storage-writing case"
    (emittedDispatchMatchesReference dispatchSmokeContract
      (sampleIRTx 0x11111111) [11] [11])
  check "emitted dispatcher selects second storage-writing case"
    (emittedDispatchMatchesReference dispatchSmokeContract
      (sampleIRTx 0x22222222) [11] [11])
  check "emitted dispatcher forwards observable storage reads"
    (emittedDispatchMatchesReference storageReadIRContract
      (sampleIRTx 0x44444444) [7, 8] [7, 8])
  check "emitted dispatcher projects 32-byte return halts"
    (emittedDispatchMatchesReference returnDispatchSmokeContract
      (sampleIRTx 0x33333333) [] [])
  check "emitted dispatcher projects multi-word return fallback"
    (emittedDispatchMatchesReference multiWordReturnDispatchSmokeContract
      (sampleIRTx 0x55555555) [] [])
  check "emitted dispatcher rolls back memory-backed revert"
    (emittedDispatchMatchesReference memoryRevertDispatchSmokeContract
      (sampleIRTx 0x66666666) [7] [7])

end Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest

def main : IO Unit :=
  Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest.main
