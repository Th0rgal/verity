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
    msgValue := 0
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

private def mappingWriteSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot 21 5

private def mappingHelperDispatchSmokeContract : IRContract :=
  { name := "NativeMappingHelperDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "storeMapped"
        selector := 0x88888888
        params := [{ name := "key", ty := .uint256 }]
        ret := .unit
        body := [
          .expr (.call "sstore" [
            .call "mappingSlot" [.lit 21, .call "calldataload" [.lit 4]],
            .lit 909])
        ] }
    ]
    usesMapping := true }

private def calldataArgDispatchSmokeContract : IRContract :=
  { name := "NativeCalldataArgDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "storeArg"
        selector := 0x77777777
        params := [{ name := "x", ty := .uint256 }]
        ret := .unit
        body := [
          .let_ "x" (.call "calldataload" [.lit 4]),
          .expr (.call "sstore" [.lit 12, .ident "x"])
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

private def emittedDispatchMatchesReferenceWithExpected
    (contract : IRContract) (tx : IRTransaction)
    (observableSlots compareSlots : List Nat)
    (expectedSuccess : Bool) (expectedReturn : Option Nat)
    (expectedSlots : List (Nat × Nat)) : Except String Bool := do
  let yulTx := YulTransaction.ofIR tx
  let reference :=
    referenceRuntimeWithBackendFuel 256 (Compiler.emitYul contract).runtimeCode
      yulTx sampleIRState.storage sampleIRState.events
  let nativeResult ←
    match Native.interpretIRRuntimeNative 256 contract tx sampleIRState observableSlots with
    | .ok result => .ok result
    | .error _ => .error "native runtime lowering failed"
  pure (
    resultsMatchOnSlots compareSlots nativeResult reference &&
    nativeResult.success == expectedSuccess &&
    reference.success == expectedSuccess &&
    nativeResult.returnValue == expectedReturn &&
    reference.returnValue == expectedReturn &&
    expectedSlots.all (fun (slot, value) =>
      nativeResult.finalStorage slot == value &&
        reference.finalStorage slot == value))

private def check (label : String) (actual : Except String Bool) : IO Unit := do
  match actual with
  | .ok true => IO.println s!"ok: {label}"
  | .ok false => throw (IO.userError s!"native/reference mismatch: {label}")
  | .error err => throw (IO.userError s!"{label}: {err}")

def main : IO Unit := do
  check "emitted dispatcher selects first storage-writing case"
    (emittedDispatchMatchesReferenceWithExpected dispatchSmokeContract
      (sampleIRTx 0x11111111) [11] [11] true none [(11, 101)])
  check "emitted dispatcher selects second storage-writing case"
    (emittedDispatchMatchesReferenceWithExpected dispatchSmokeContract
      (sampleIRTx 0x22222222) [11] [11] true none [(11, 202)])
  check "emitted dispatcher forwards observable storage reads"
    (emittedDispatchMatchesReferenceWithExpected storageReadIRContract
      (sampleIRTx 0x44444444) [7, 8] [7, 8] true none [(7, 77), (8, 77)])
  check "emitted dispatcher decodes ABI argument words"
    (emittedDispatchMatchesReferenceWithExpected calldataArgDispatchSmokeContract
      (sampleIRTx 0x77777777 [0xABCD]) [12] [12] true none [(12, 0xABCD)])
  check "emitted dispatcher executes mappingSlot helper writes"
    (emittedDispatchMatchesReferenceWithExpected mappingHelperDispatchSmokeContract
      (sampleIRTx 0x88888888 [5]) [mappingWriteSlot] [mappingWriteSlot] true none
      [(mappingWriteSlot, 909)])
  check "emitted dispatcher projects 32-byte return halts"
    (emittedDispatchMatchesReferenceWithExpected returnDispatchSmokeContract
      (sampleIRTx 0x33333333) [] [] true (some 42) [])
  check "emitted dispatcher projects multi-word return fallback"
    (emittedDispatchMatchesReferenceWithExpected multiWordReturnDispatchSmokeContract
      (sampleIRTx 0x55555555) [] [] true (some 0) [])
  check "emitted dispatcher rolls back memory-backed revert"
    (emittedDispatchMatchesReferenceWithExpected memoryRevertDispatchSmokeContract
      (sampleIRTx 0x66666666) [7] [7] false none [(7, 77)])

end Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest

def main : IO Unit :=
  Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest.main
