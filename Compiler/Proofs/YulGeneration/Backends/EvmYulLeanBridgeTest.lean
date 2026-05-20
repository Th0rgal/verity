/-
  EvmYulLeanBridgeTest: compile-time smoke checks for the native EVMYulLean
  builtin surface.

  The old Verity builtin-comparison target has been removed. These
  tests now exercise direct native dispatch and selected boundary values.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

namespace Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest

open Compiler.Proofs.YulGeneration.Backends
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

private def testStorage : IRStorageSlot → IRStorageWord :=
  fun slot => if slot.toNat = 7 then 0xABCD else 0

private def testSender : Nat := 42
private def testMsgValue : Nat := 99
private def testThisAddress : Nat := 0xC0FFEE
private def testBlockTimestamp : Nat := 0x123456
private def testBlockNumber : Nat := 0xABCDEF
private def testChainId : Nat := 1
private def testBlobBaseFee : Nat := 0xB10B
private def testSelector : Nat := 0x12345678
private def testCalldata : List Nat := [0xDEADBEEF]

private def nativeEval (func : String) (args : List Nat) : Option Nat :=
  evalBuiltinCallViaEvmYulLean testStorage testSender testSelector testCalldata func args

private def nativeEvalWithContext (func : String) (args : List Nat) : Option Nat :=
  evalBuiltinCallWithEvmYulLeanContext
    testStorage
    testSender
    testMsgValue
    testThisAddress
    testBlockTimestamp
    testBlockNumber
    testChainId
    testBlobBaseFee
    testSelector
    testCalldata
    func
    args

example : nativeEval "add" [3, 5] = evalPureBuiltinViaEvmYulLean "add" [3, 5] := by
  native_decide

example :
    nativeEval "sub" [0, 1] =
      evalPureBuiltinViaEvmYulLean "sub" [0, 1] := by
  native_decide

example :
    nativeEval "mul" [Compiler.Constants.evmModulus - 1, 2] =
      evalPureBuiltinViaEvmYulLean "mul" [Compiler.Constants.evmModulus - 1, 2] := by
  native_decide

example : nativeEval "div" [42, 0] = evalPureBuiltinViaEvmYulLean "div" [42, 0] := by
  native_decide

example :
    nativeEval "and" [0xF0, 0x0F] =
      evalPureBuiltinViaEvmYulLean "and" [0xF0, 0x0F] := by
  native_decide

example :
    nativeEval "shl" [8, 1] =
      evalPureBuiltinViaEvmYulLean "shl" [8, 1] := by
  native_decide

example :
    nativeEval "sar" [1, Compiler.Constants.evmModulus - 2] =
      evalPureBuiltinViaEvmYulLean "sar" [1, Compiler.Constants.evmModulus - 2] := by
  native_decide

example : nativeEvalWithContext "caller" [] = some testSender := by
  native_decide

example :
    nativeEvalWithContext "callvalue" [] =
      some (testMsgValue % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "address" [] =
      some (testThisAddress % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "timestamp" [] =
      some (testBlockTimestamp % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "number" [] =
      some (testBlockNumber % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "chainid" [] =
      some (testChainId % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "blobbasefee" [] =
      some (testBlobBaseFee % Compiler.Constants.evmModulus) := by
  native_decide

example :
    nativeEvalWithContext "calldatasize" [] =
      some ((4 + testCalldata.length * 32) % Compiler.Constants.evmModulus) := by
  native_decide

example : nativeEval "sload" [7] = some 0xABCD := by
  native_decide

example :
    nativeEval "mappingSlot" [5, 11] =
      some (Compiler.Proofs.abstractMappingSlot 5 11) := by
  rfl

end Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest
