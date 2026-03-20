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

end Compiler.Proofs.IRGeneration.SourceSemanticsFeatureTest
