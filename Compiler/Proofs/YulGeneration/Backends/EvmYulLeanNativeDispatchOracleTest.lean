import Compiler.CompilationModel
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget

namespace Compiler.Proofs.YulGeneration.Backends.NativeDispatchOracleTest

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

private def mappingReadSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot 21 5

private def mappingWriteSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot 21 5

private def nestedMappingWriteSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot (Compiler.Proofs.abstractMappingSlot 22 3) 4

private def packedMappingSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot 23 6

private def multiWordMappingBaseSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot 24 7

private def multiWordMappingMemberSlot : Nat :=
  multiWordMappingBaseSlot + 1

private def nestedMultiWordMappingBaseSlot : Nat :=
  Compiler.Proofs.abstractMappingSlot (Compiler.Proofs.abstractMappingSlot 25 3) 4

private def nestedMultiWordMappingMemberSlot : Nat :=
  nestedMultiWordMappingBaseSlot + 1

private def seededStorage : IRStorageSlot -> IRStorageWord := fun slot =>
  if slot = IRStorageSlot.ofNat 7 then IRStorageWord.ofNat 77 else
  if slot = IRStorageSlot.ofNat mappingReadSlot then IRStorageWord.ofNat 515 else
  if slot = IRStorageSlot.ofNat packedMappingSlot then IRStorageWord.ofNat 0x123456 else
  if slot = IRStorageSlot.ofNat multiWordMappingBaseSlot then IRStorageWord.ofNat 0xAAAA else
  if slot = IRStorageSlot.ofNat multiWordMappingMemberSlot then IRStorageWord.ofNat 0xBBBB else
  if slot = IRStorageSlot.ofNat nestedMultiWordMappingBaseSlot then IRStorageWord.ofNat 0xCCCC else
  if slot = IRStorageSlot.ofNat nestedMultiWordMappingMemberSlot then IRStorageWord.ofNat 0xDDDD else IRStorageWord.ofNat 0

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

private def mappingHelperReadDispatchSmokeContract : IRContract :=
  { name := "NativeMappingHelperReadDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "loadMapped"
        selector := 0x99999999
        params := [{ name := "key", ty := .uint256 }]
        ret := .unit
        body := [
          .expr (.call "sstore" [
            .lit 15,
            .call "sload" [
              .call "mappingSlot" [.lit 21, .call "calldataload" [.lit 4]]
            ]])
        ] }
    ]
    usesMapping := true }

private def nestedMappingHelperDispatchSmokeContract : IRContract :=
  { name := "NativeNestedMappingHelperDispatchOracleSmoke"
    deploy := []
    functions := [
      { name := "storeNestedMapped"
        selector := 0xAAAAAAAA
        params := [
          { name := "outerKey", ty := .uint256 },
          { name := "innerKey", ty := .uint256 }
        ]
        ret := .unit
        body := [
          .expr (.call "sstore" [
            .call "mappingSlot" [
              .call "mappingSlot" [.lit 22, .call "calldataload" [.lit 4]],
              .call "calldataload" [.lit 36]
            ],
            .lit 808])
        ] }
    ]
    usesMapping := true }

private def packedMember : Compiler.CompilationModel.StructMember :=
  { name := "flags"
    wordOffset := 0
    packed := some { offset := 8, width := 8 } }

private def packedMappingModel : Compiler.CompilationModel.CompilationModel :=
  { name := "NativePackedMappingOracleSmoke"
    fields := [
      { name := "positions"
        ty := .mappingStruct .uint256 [packedMember]
        slot := some 23 },
      { name := "scratch"
        ty := .uint256
        slot := some 16 }
    ]
    constructor := none
    functions := [
      { name := "readFlags"
        params := [{ name := "key", ty := .uint256 }]
        returnType := none
        body := [
          .setStorage "scratch" (.structMember "positions" (.param "key") "flags")
        ] },
      { name := "writeFlags"
        params := [
          { name := "key", ty := .uint256 },
          { name := "value", ty := .uint256 }
        ]
        returnType := none
        body := [
          .setStructMember "positions" (.param "key") "flags" (.param "value")
        ] }
    ] }

private def packedMappingDispatchSmokeContract : Except String IRContract :=
  Compiler.CompilationModel.compile packedMappingModel [0xBBBBBBBB, 0xCCCCCCCC]

private def multiWordMember : Compiler.CompilationModel.StructMember :=
  { name := "balance"
    wordOffset := 1
    packed := none }

private def multiWordMappingModel : Compiler.CompilationModel.CompilationModel :=
  { name := "NativeMultiWordMappingOracleSmoke"
    fields := [
      { name := "accounts"
        ty := .mappingStruct .uint256 [multiWordMember]
        slot := some 24 },
      { name := "nestedAccounts"
        ty := .mappingStruct2 .uint256 .uint256 [multiWordMember]
        slot := some 25 },
      { name := "scratch"
        ty := .uint256
        slot := some 17 }
    ]
    constructor := none
    functions := [
      { name := "readBalance"
        params := [{ name := "key", ty := .uint256 }]
        returnType := none
        body := [
          .setStorage "scratch" (.structMember "accounts" (.param "key") "balance")
        ] },
      { name := "writeBalance"
        params := [
          { name := "key", ty := .uint256 },
          { name := "value", ty := .uint256 }
        ]
        returnType := none
        body := [
          .setStructMember "accounts" (.param "key") "balance" (.param "value")
        ] },
      { name := "readNestedBalance"
        params := [
          { name := "outerKey", ty := .uint256 },
          { name := "innerKey", ty := .uint256 }
        ]
        returnType := none
        body := [
          .setStorage "scratch"
            (.structMember2 "nestedAccounts" (.param "outerKey") (.param "innerKey") "balance")
        ] },
      { name := "writeNestedBalance"
        params := [
          { name := "outerKey", ty := .uint256 },
          { name := "innerKey", ty := .uint256 },
          { name := "value", ty := .uint256 }
        ]
        returnType := none
        body := [
          .setStructMember2 "nestedAccounts" (.param "outerKey") (.param "innerKey")
            "balance" (.param "value")
        ] }
    ] }

private def multiWordMappingDispatchSmokeContract : Except String IRContract :=
  Compiler.CompilationModel.compile multiWordMappingModel
    [0xDDDDDDDD, 0xEEEEEEEE, 0xDADADADA, 0xEFEFEFEF]

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
    (tx : YulTransaction) (storage : IRStorageSlot -> IRStorageWord) (events : List (List Nat)) :
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
      nativeResult.finalStorage (IRStorageSlot.ofNat slot) ==
        referenceResult.finalStorage (IRStorageSlot.ofNat slot))

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
      nativeResult.finalStorage (IRStorageSlot.ofNat slot) == IRStorageWord.ofNat value &&
        reference.finalStorage (IRStorageSlot.ofNat slot) == IRStorageWord.ofNat value))

private def emittedCompiledDispatchMatchesReferenceWithExpected
    (contract : Except String IRContract) (tx : IRTransaction)
    (observableSlots compareSlots : List Nat)
    (expectedSuccess : Bool) (expectedReturn : Option Nat)
    (expectedSlots : List (Nat × Nat)) : Except String Bool := do
  let irContract ← contract
  emittedDispatchMatchesReferenceWithExpected irContract tx observableSlots compareSlots
    expectedSuccess expectedReturn expectedSlots

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
  check "emitted dispatcher executes mappingSlot helper reads"
    (emittedDispatchMatchesReferenceWithExpected mappingHelperReadDispatchSmokeContract
      (sampleIRTx 0x99999999 [5]) [mappingReadSlot, 15] [mappingReadSlot, 15] true none
      [(mappingReadSlot, 515), (15, 515)])
  check "emitted dispatcher executes nested mappingSlot helper writes"
    (emittedDispatchMatchesReferenceWithExpected nestedMappingHelperDispatchSmokeContract
      (sampleIRTx 0xAAAAAAAA [3, 4]) [nestedMappingWriteSlot] [nestedMappingWriteSlot]
      true none [(nestedMappingWriteSlot, 808)])
  check "compiled dispatcher reads packed mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected packedMappingDispatchSmokeContract
      (sampleIRTx 0xBBBBBBBB [6]) [packedMappingSlot, 16] [packedMappingSlot, 16]
      true none [(packedMappingSlot, 0x123456), (16, 0x34)])
  check "compiled dispatcher writes packed mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected packedMappingDispatchSmokeContract
      (sampleIRTx 0xCCCCCCCC [6, 0xABCD]) [packedMappingSlot] [packedMappingSlot]
      true none [(packedMappingSlot, 0x12CD56)])
  check "compiled dispatcher reads multi-word mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected multiWordMappingDispatchSmokeContract
      (sampleIRTx 0xDDDDDDDD [7])
      [multiWordMappingBaseSlot, multiWordMappingMemberSlot, 17]
      [multiWordMappingBaseSlot, multiWordMappingMemberSlot, 17]
      true none
      [(multiWordMappingBaseSlot, 0xAAAA), (multiWordMappingMemberSlot, 0xBBBB), (17, 0xBBBB)])
  check "compiled dispatcher writes multi-word mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected multiWordMappingDispatchSmokeContract
      (sampleIRTx 0xEEEEEEEE [7, 0x1234])
      [multiWordMappingBaseSlot, multiWordMappingMemberSlot]
      [multiWordMappingBaseSlot, multiWordMappingMemberSlot]
      true none
      [(multiWordMappingBaseSlot, 0xAAAA), (multiWordMappingMemberSlot, 0x1234)])
  check "compiled dispatcher reads nested multi-word mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected multiWordMappingDispatchSmokeContract
      (sampleIRTx 0xDADADADA [3, 4])
      [nestedMultiWordMappingBaseSlot, nestedMultiWordMappingMemberSlot, 17]
      [nestedMultiWordMappingBaseSlot, nestedMultiWordMappingMemberSlot, 17]
      true none
      [(nestedMultiWordMappingBaseSlot, 0xCCCC), (nestedMultiWordMappingMemberSlot, 0xDDDD),
        (17, 0xDDDD)])
  check "compiled dispatcher writes nested multi-word mapping struct members"
    (emittedCompiledDispatchMatchesReferenceWithExpected multiWordMappingDispatchSmokeContract
      (sampleIRTx 0xEFEFEFEF [3, 4, 0x5678])
      [nestedMultiWordMappingBaseSlot, nestedMultiWordMappingMemberSlot]
      [nestedMultiWordMappingBaseSlot, nestedMultiWordMappingMemberSlot]
      true none
      [(nestedMultiWordMappingBaseSlot, 0xCCCC), (nestedMultiWordMappingMemberSlot, 0x5678)])
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
