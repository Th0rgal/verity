import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration.SourceSemanticsFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration

private def storageArraySourceSpec : CompilationModel :=
  { name := "StorageArraySource"
    fields := [{ name := "queue", ty := .dynamicArray .uint256, «slot» := some 7 }]
    constructor := none
    functions :=
      [ { name := "length"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayLength "queue")] }
      , { name := "first"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayElement "queue" (.literal 0))] }
      , { name := "push"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.storageArrayPush "queue" (.param "value"), .stop] }
      , { name := "write0"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.setStorageArrayElement "queue" (.literal 0) (.param "value"), .stop] }
      , { name := "pop"
          params := []
          returnType := none
          body := [Stmt.storageArrayPop "queue", .stop] } ] }

private def storageArrayInitialWorld : Verity.ContractState :=
  { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }

private def signedScalarSourceSpec : CompilationModel :=
  { name := "SignedScalarSource"
    fields := []
    constructor := none
    functions :=
      [ { name := "echoSigned"
          params := [{ name := "x", ty := .int256 }]
          returnType := none
          returns := [.int256]
          body := [Stmt.return (Expr.param "x")] } ] }

private def emitSourceSpec : CompilationModel :=
  { name := "EmitSource"
    fields := []
    events := [{ name := "Ping", params := [{ name := "value", ty := .uint256, kind := .unindexed }] }]
    constructor := none
    functions :=
      [ { name := "emitPing"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.emit "Ping" [Expr.param "value"], .stop] } ] }

private def indexedEmitSourceSpec : CompilationModel :=
  { name := "IndexedEmitSource"
    fields := []
    events := [
      { name := "Ping"
        params := [
          { name := "topic", ty := .uint256, kind := .indexed },
          { name := "value", ty := .uint256, kind := .unindexed }
        ] }
    ]
    constructor := none
    functions :=
      [ { name := "emitPing"
          params := [
            { name := "topic", ty := .uint256 },
            { name := "value", ty := .uint256 }
          ]
          returnType := none
          body := [Stmt.emit "Ping" [Expr.param "topic", Expr.param "value"], .stop] } ] }

private def storageWordFields : List Field :=
  [{ name := "root", ty := .uint256, «slot» := some 10 }]

private def storageWordSpec : CompilationModel :=
  { name := "StorageWordSource"
    fields := storageWordFields
    constructor := none
    functions := [] }

private def storageWordState : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState, bindings := [] }

private def resultStorageAt? (slot : Nat) : SourceSemantics.StmtResult → Option Nat
  | .continue st => some (st.world.storage slot).val
  | .stop st => some (st.world.storage slot).val
  | .return _ st => some (st.world.storage slot).val
  | .revert => none

private def resultStorageAddrAt? (slot : Nat) : SourceSemantics.StmtResult → Option Verity.Address
  | .continue st => some (st.world.storageAddr slot)
  | .stop st => some (st.world.storageAddr slot)
  | .return _ st => some (st.world.storageAddr slot)
  | .revert => none

example :
    (sourceContractSemantics simpleStorageSupportedSpecModel [0x2e64cec1]
      { sender := 7, functionSelector := 0x2e64cec1, args := [] }
      Verity.defaultState).success = true := by
  native_decide

example :
    (sourceContractSemantics counterSupportedSpecModel
      [0xa87d942c]
      { sender := 9, functionSelector := 0xa87d942c, args := [] }
      Verity.defaultState).returnValue = some 42 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x11111111, args := [] }
      storageArrayInitialWorld).returnValue = some 2 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      storageArrayInitialWorld).returnValue = some 11 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x33333333, args := [23] }
      storageArrayInitialWorld).finalStorage 7 = 3 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x44444444, args := [29] }
      storageArrayInitialWorld).success = true := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      storageArrayInitialWorld).finalStorage 7 = 1 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      Verity.defaultState).success = false := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      Verity.defaultState).success = false := by
  native_decide

example :
    SourceSemantics.decodeSupportedParamWord .int256 (2 ^ 256 - 1) = some (2 ^ 256 - 1) := by
  native_decide

example :
    (sourceContractSemantics signedScalarSourceSpec
      [0xabcdef01]
      { sender := 9, functionSelector := 0xabcdef01, args := [2 ^ 256 - 1] }
      Verity.defaultState).returnValue = some (2 ^ 256 - 1) := by
  native_decide

example :
    (sourceContractSemantics emitSourceSpec
      [0x13572468]
      { sender := 9, functionSelector := 0x13572468, args := [77] }
      Verity.defaultState).success = true := by
  native_decide

example :
    (sourceContractSemantics indexedEmitSourceSpec
      [0x24681357]
      { sender := 9, functionSelector := 0x24681357, args := [11, 22] }
      Verity.defaultState).events =
        SourceSemantics.encodeEvents
          [{ name := "Ping"
             args := [Verity.Core.Uint256.ofNat (22 % Compiler.Constants.evmModulus)]
             indexedArgs := [
               SourceSemantics.eventSignatureTopic
                 { name := "Ping"
                   params := [
                     { name := "topic", ty := .uint256, kind := .indexed },
                     { name := "value", ty := .uint256, kind := .unindexed }
                   ] },
               Verity.Core.Uint256.ofNat (11 % Compiler.Constants.evmModulus)] }] := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmtWithEvents storageWordFields [] storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAddrAt? 12
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) =
        some (Verity.wordToAddress (99 : Verity.Uint256)) := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmtWithHelpers storageWordSpec storageWordFields 1 storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAt? 10
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 0 := by
  native_decide

end Compiler.Proofs.IRGeneration.SourceSemanticsFeatureTest
