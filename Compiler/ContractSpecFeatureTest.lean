import Compiler.ContractSpec
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace Compiler.ContractSpecFeatureTest

open Compiler
open Compiler.ContractSpec

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

private def assertContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if !contains rendered needle then
      throw (IO.userError s!"✗ {label}: missing '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def assertNotContains (label rendered : String) (needles : List String) : IO Unit := do
  for needle in needles do
    if contains rendered needle then
      throw (IO.userError s!"✗ {label}: unexpected '{needle}' in:\n{rendered}")
  IO.println s!"✓ {label}"

private def featureSpec : ContractSpec := {
  name := "FeatureSpec"
  fields := []
  constructor := none
  events := [
    { name := "ValueSet"
      params := [
        { name := "who", ty := ParamType.address, kind := EventParamKind.indexed },
        { name := "value", ty := ParamType.uint256, kind := EventParamKind.unindexed }
      ]
    },
    { name := "BoolSet"
      params := [
        { name := "ok", ty := ParamType.bool, kind := EventParamKind.indexed }
      ]
    }
  ]
  functions := [
    { name := "setFlag"
      params := [{ name := "flag", ty := ParamType.bool }]
      returnType := none
      body := [Stmt.stop]
    },
    { name := "pair"
      params := [
        { name := "a", ty := ParamType.uint256 },
        { name := "b", ty := ParamType.uint256 }
      ]
      returnType := none
      returns := [ParamType.uint256, ParamType.uint256]
      body := [Stmt.returnValues [Expr.param "a", Expr.param "b"]]
    },
    { name := "emitValue"
      params := [
        { name := "who", ty := ParamType.address },
        { name := "value", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [Stmt.emit "ValueSet" [Expr.param "who", Expr.param "value"], Stmt.stop]
    },
    { name := "emitBool"
      params := []
      returnType := none
      body := [Stmt.emit "BoolSet" [Expr.literal 2], Stmt.stop]
    },
    { name := "echoArray"
      params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnArray "arr"]
    },
    { name := "sumStaticTuple"
      params := [
        { name := "t", ty := ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.bool] },
        { name := "z", ty := ParamType.uint256 }
      ]
      returnType := none
      body := [Stmt.return (Expr.add (Expr.param "t_0") (Expr.param "z"))]
    },
    { name := "dynamicTupleTail"
      params := [
        { name := "td", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] },
        { name := "x", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.param "x")]
    },
    { name := "nestedStaticTupleTail"
      params := [
        { name := "u"
          ty := ParamType.tuple [
            ParamType.fixedArray ParamType.uint256 2,
            ParamType.tuple [ParamType.address, ParamType.bool],
            ParamType.uint256
          ]
        },
        { name := "y", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.add (Expr.param "u_0_1") (Expr.param "y"))]
    },
    { name := "fixedArrayTupleTail"
      params := [
        { name := "fa", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bool]) 2 },
        { name := "q", ty := ParamType.uint256 }
      ]
      returnType := some FieldType.uint256
      body := [Stmt.return (Expr.add (Expr.param "fa_1_0") (Expr.param "q"))]
    },
    { name := "echoBytes"
      params := [{ name := "data", ty := ParamType.bytes }]
      returnType := none
      returns := [ParamType.bytes]
      body := [Stmt.returnBytes "data"]
    },
    { name := "extSloadsLike"
      params := [{ name := "slots", ty := ParamType.array ParamType.bytes32 }]
      returnType := none
      returns := [ParamType.array ParamType.uint256]
      body := [Stmt.returnStorageWords "slots"]
    }
  ]
}

#eval! do
  match compile featureSpec [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] with
  | .error err =>
      throw (IO.userError s!"✗ feature spec compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "bool param normalization" rendered ["iszero(iszero(calldataload(4)))"]
      assertContains "multi-return ABI encoding" rendered ["return(0, 64)"]
      assertContains "indexed event log opcode" rendered ["log2("]
      assertContains "indexed bool topic normalization" rendered ["iszero(iszero(2))"]
      assertContains "event topic hashing uses free memory pointer" rendered ["keccak256(__evt_ptr,"]
      assertContains "event topic hash cached before data writes" rendered ["let __evt_topic0 := keccak256(__evt_ptr,", "log2(__evt_ptr, 32, __evt_topic0"]
      assertContains "dynamic array ABI return" rendered ["calldatacopy(64"]
      assertContains "static tuple decode head offsets" rendered ["let t_0 := calldataload(4)", "let t_1 := and(calldataload(36)", "let t_2 := iszero(iszero(calldataload(68)))", "let z := calldataload(100)"]
      assertContains "dynamic tuple keeps offset head word" rendered ["let td_offset := calldataload(4)", "let x := calldataload(36)"]
      assertContains "nested static tuple decode head offsets" rendered ["let u_0_0 := calldataload(4)", "let u_0_1 := calldataload(36)", "let u_1_0 := and(calldataload(68)", "let u_1_1 := iszero(iszero(calldataload(100)))", "let u_2 := calldataload(132)", "let y := calldataload(164)"]
      assertContains "fixed array of static tuples decode offsets" rendered ["let fa_0_0 := calldataload(4)", "let fa_0_1 := iszero(iszero(calldataload(36)))", "let fa_1_0 := calldataload(68)", "let fa_1_1 := iszero(iszero(calldataload(100)))", "let q := calldataload(132)"]
      assertContains "dynamic bytes ABI return" rendered ["calldatacopy(64, data_data_offset, data_length)", "mstore(add(64, data_length), 0)", "return(0, add(64, and(add(data_length, 31), not(31))))"]
      assertContains "storage-word array return ABI" rendered ["let __slot := calldataload(add(slots_data_offset, mul(__i, 32)))", "mstore(add(64, mul(__i, 32)), sload(__slot))", "return(0, add(64, mul(slots_length, 32)))"]

#eval! do
  let conflictingReturnsSpec : ContractSpec := {
    name := "ConflictingReturns"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := []
        returnType := some FieldType.uint256
        returns := [ParamType.uint256, ParamType.uint256]
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      }
    ]
  }
  match compile conflictingReturnsSpec [1] with
  | .error err =>
      if !contains err "conflicting return declarations" then
        throw (IO.userError s!"✗ conflicting returns should fail with clear message, got: {err}")
      IO.println "✓ conflicting return declaration validation"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting returns to fail compilation")

#eval! do
  let invalidReturnBytesSpec : ContractSpec := {
    name := "InvalidReturnBytes"
    fields := []
    constructor := none
    functions := [
      { name := "badBytes"
        params := [{ name := "arr", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        returns := [ParamType.bytes]
        body := [Stmt.returnBytes "arr"]
      }
    ]
  }
  match compile invalidReturnBytesSpec [1] with
  | .error err =>
      if !contains err "returnBytes 'arr' requires bytes parameter" then
        throw (IO.userError s!"✗ returnBytes type validation message mismatch: {err}")
      IO.println "✓ returnBytes parameter type validation"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid returnBytes parameter to fail compilation")

#eval! do
  let payableMsgValueSpec : ContractSpec := {
    name := "PayableMsgValue"
    fields := []
    constructor := some {
      params := []
      isPayable := true
      body := [Stmt.stop]
    }
    functions := [
      { name := "payableLike"
        params := []
        returnType := some FieldType.uint256
        isPayable := true
        body := [Stmt.return Expr.msgValue]
      }
    ]
  }
  match compile payableMsgValueSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected payable msgValue usage to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "payable msgValue compiles" rendered ["mstore(0, callvalue())"]
      assertNotContains "payable function skips non-payable guard" rendered ["if callvalue()"]

#eval! do
  let nonPayableGuardSpec : ContractSpec := {
    name := "NonPayableGuard"
    fields := []
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile nonPayableGuardSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected non-payable function to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "non-payable function emits msg.value guard" rendered ["if callvalue()"]

#eval! do
  let lowLevelCallSpec : ContractSpec := {
    name := "LowLevelCallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "delegatecall" [Expr.param "target"])]
      }
    ]
  }
  match compile lowLevelCallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'delegatecall'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ low-level call diagnostic mismatch: {err}")
      IO.println "✓ low-level call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected low-level call usage to fail compilation")

#eval! do
  let ctorMsgValueSpec : ContractSpec := {
    name := "CtorMsgValuePayable"
    fields := []
    constructor := some {
      params := []
      isPayable := true
      body := [Stmt.letVar "v" Expr.msgValue, Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorMsgValueSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected payable constructor msgValue usage to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "payable constructor msgValue compiles" rendered ["let v := callvalue()"]
      assertNotContains "payable constructor skips non-payable guard" rendered ["if callvalue()"]

#eval! do
  let ctorNonPayableGuardSpec : ContractSpec := {
    name := "CtorNonPayableGuard"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorNonPayableGuardSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected non-payable constructor to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "non-payable constructor emits msg.value guard" rendered ["if callvalue()"]

#eval! do
  let ctorLowLevelCallSpec : ContractSpec := {
    name := "CtorLowLevelCallUnsupported"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.letVar "v" (Expr.externalCall "call" []), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorLowLevelCallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'call'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ constructor low-level call diagnostic mismatch: {err}")
      IO.println "✓ constructor low-level call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected constructor low-level call usage to fail compilation")

#eval! do
  let extCodeSizeSpec : ContractSpec := {
    name := "ExtCodeSizeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodesize" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeSizeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodesize'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodesize diagnostic mismatch: {err}")
      IO.println "✓ extcodesize unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodesize usage to fail compilation")

#eval! do
  let externalCreate2Spec : ContractSpec := {
    name := "ExternalCreate2Unsupported"
    fields := []
    constructor := none
    externals := [
      { name := "create2"
        params := [ParamType.uint256]
        returnType := some ParamType.address
        axiomNames := []
      }
    ]
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile externalCreate2Spec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'create2'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external create2 diagnostic mismatch: {err}")
      IO.println "✓ external create2 unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external create2 declaration to fail compilation")

#eval! do
  let indexedDynamicEventSpec : ContractSpec := {
    name := "IndexedDynamicEventUnsupported"
    fields := []
    constructor := none
    events := [
      { name := "BadIndexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBad"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "BadIndexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicEventSpec [1] with
  | .error err =>
      if !(contains err "indexed dynamic/tuple param 'payload'" &&
          contains err "Issue #586" &&
          contains err "Use an unindexed field for now") then
        throw (IO.userError s!"✗ indexed dynamic event diagnostic mismatch: {err}")
      IO.println "✓ indexed dynamic event diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected indexed dynamic event param usage to fail compilation")

#eval! do
  let fallbackSpec : ContractSpec := {
    name := "FallbackSupported"
    fields := []
    constructor := none
    functions := [
      { name := "fallback"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile fallbackSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected fallback entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "fallback default branch emission" rendered ["default {", "/* fallback() */", "stop()"]

#eval! do
  let receiveSpec : ContractSpec := {
    name := "ReceiveSupported"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected receive entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "receive empty-calldata dispatch branch" rendered
        ["let __is_empty_calldata := eq(calldatasize(), 0)", "if __is_empty_calldata {", "/* receive() */", "stop()"]
      assertContains "receive missing fallback reverts for non-empty calldata" rendered
        ["if iszero(__is_empty_calldata) {", "revert(0, 0)"]

#eval! do
  let receiveFallbackSpec : ContractSpec := {
    name := "ReceiveFallbackSupported"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        isPayable := true
        body := [Stmt.stop]
      },
      { name := "fallback"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveFallbackSpec [] with
  | .error err =>
      throw (IO.userError s!"✗ expected receive+fallback entrypoint modeling to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "receive+fallback split dispatch" rendered
        ["if __is_empty_calldata {", "/* receive() */", "if iszero(__is_empty_calldata) {", "/* fallback() */"]

#eval! do
  let receiveNotPayableSpec : ContractSpec := {
    name := "ReceiveNotPayableRejected"
    fields := []
    constructor := none
    functions := [
      { name := "receive"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile receiveNotPayableSpec [] with
  | .error err =>
      if !(contains err "function 'receive' must be payable" && contains err "Issue #586") then
        throw (IO.userError s!"✗ receive payable diagnostic mismatch: {err}")
      IO.println "✓ receive payable validation"
  | .ok _ =>
      throw (IO.userError "✗ expected non-payable receive entrypoint to fail compilation")

end Compiler.ContractSpecFeatureTest
