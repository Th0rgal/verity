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
  errors := [
    { name := "Unauthorized"
      params := [ParamType.address, ParamType.uint256]
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
    },
    { name := "guarded"
      params := [{ name := "who", ty := ParamType.address }, { name := "min", ty := ParamType.uint256 }]
      returnType := none
      body := [
        Stmt.requireError (Expr.lt (Expr.param "min") (Expr.literal 1)) "Unauthorized" [Expr.param "who", Expr.param "min"],
        Stmt.stop
      ]
    }
  ]
}

#eval! do
  match compile featureSpec [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] with
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
      assertContains "custom error revert payload emission" rendered ["let __err_hash := keccak256(__err_ptr,", "mstore(0, __err_selector)", "mstore(4, and(who,", "let __err_tail := 64", "revert(0, add(4, __err_tail))"]

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
  let staticcallSpec : ContractSpec := {
    name := "StaticcallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "staticcall" [Expr.param "target"])]
      }
    ]
  }
  match compile staticcallSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'staticcall'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ staticcall diagnostic mismatch: {err}")
      IO.println "✓ staticcall unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected staticcall usage to fail compilation")

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
  let ctorCallcodeSpec : ContractSpec := {
    name := "CtorCallcodeUnsupported"
    fields := []
    constructor := some {
      params := []
      body := [Stmt.letVar "v" (Expr.externalCall "callcode" []), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorCallcodeSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'callcode'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ constructor callcode diagnostic mismatch: {err}")
      IO.println "✓ constructor callcode unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected constructor callcode usage to fail compilation")

#eval! do
  let ctorBoolParamSpec : ContractSpec := {
    name := "CtorBoolParamNormalization"
    fields := []
    constructor := some {
      params := [{ name := "flag", ty := ParamType.bool }]
      body := [Stmt.letVar "seen" (Expr.constructorArg 0), Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorBoolParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected bool constructor param normalization to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor bool param normalization" rendered
        ["let flag := iszero(iszero(mload(0)))", "let arg0 := flag"]

#eval! do
  let ctorDynamicParamSpec : ContractSpec := {
    name := "CtorDynamicParamSupported"
    fields := []
    constructor := some {
      params := [{ name := "payload", ty := ParamType.bytes }]
      body := [Stmt.stop]
    }
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile ctorDynamicParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected dynamic constructor parameter support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor dynamic param decode" rendered
        ["let payload_offset := mload(0)", "let payload_length := mload(payload_offset)",
         "let payload_data_offset := add(payload_offset, 32)", "let arg0 := payload_offset"]

#eval! do
  let ctorMixedParamSpec : ContractSpec := {
    name := "CtorMixedParamDecode"
    fields := []
    constructor := some {
      params := [
        { name := "owner", ty := ParamType.address },
        { name := "payload", ty := ParamType.bytes }
      ]
      body := [Stmt.stop]
    }
    events := []
    errors := []
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile ctorMixedParamSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected mixed constructor parameter support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor mixed param decode" rendered
        ["let owner := and(mload(0),", "let payload_offset := mload(32)",
         "let payload_length := mload(payload_offset)", "let arg0 := owner",
         "let arg1 := payload_offset"]

#eval! do
  let ctorDynamicReadSpec : ContractSpec := {
    name := "CtorDynamicReadSource"
    fields := []
    constructor := some {
      params := [{ name := "numbers", ty := ParamType.array ParamType.uint256 }]
      body := [
        Stmt.letVar "firstWord" (Expr.arrayElement "numbers" (Expr.literal 0)),
        Stmt.stop
      ]
    }
    events := []
    errors := []
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile ctorDynamicReadSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected constructor dynamic read support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "constructor dynamic read source" rendered
        ["let firstWord := mload(add(numbers_data_offset, mul(0, 32)))"]
      assertNotContains "constructor dynamic read source" rendered
        ["let firstWord := calldataload(add(numbers_data_offset, mul(0, 32)))"]

#eval! do
  let callSpec : ContractSpec := {
    name := "CallUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "unsafe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "call" [Expr.param "target"])]
      }
    ]
  }
  match compile callSpec [1] with
  | .error err =>
      if !(contains err "unsupported low-level call 'call'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ call diagnostic mismatch: {err}")
      IO.println "✓ call unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected call usage to fail compilation")

#eval! do
  let balanceSpec : ContractSpec := {
    name := "BalanceUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "balance" [Expr.param "target"])]
      }
    ]
  }
  match compile balanceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'balance'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ balance diagnostic mismatch: {err}")
      IO.println "✓ balance unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected balance usage to fail compilation")

#eval! do
  let gasPriceSpec : ContractSpec := {
    name := "GasPriceUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "gasprice" [])]
      }
    ]
  }
  match compile gasPriceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'gasprice'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ gasprice diagnostic mismatch: {err}")
      IO.println "✓ gasprice unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected gasprice usage to fail compilation")

#eval! do
  let blobBaseFeeSpec : ContractSpec := {
    name := "BlobBaseFeeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "blobbasefee" [])]
      }
    ]
  }
  match compile blobBaseFeeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobbasefee'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ blobbasefee diagnostic mismatch: {err}")
      IO.println "✓ blobbasefee unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected blobbasefee usage to fail compilation")

#eval! do
  let blobHashSpec : ContractSpec := {
    name := "BlobHashUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "index", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "blobhash" [Expr.param "index"])]
      }
    ]
  }
  match compile blobHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobhash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ blobhash diagnostic mismatch: {err}")
      IO.println "✓ blobhash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected blobhash usage to fail compilation")

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
  let extCodeCopySpec : ContractSpec := {
    name := "ExtCodeCopyUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodecopy" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeCopySpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodecopy'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodecopy diagnostic mismatch: {err}")
      IO.println "✓ extcodecopy unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodecopy usage to fail compilation")

#eval! do
  let extCodeHashSpec : ContractSpec := {
    name := "ExtCodeHashUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "extcodehash" [Expr.param "target"])]
      }
    ]
  }
  match compile extCodeHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'extcodehash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ extcodehash diagnostic mismatch: {err}")
      IO.println "✓ extcodehash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected extcodehash usage to fail compilation")

#eval! do
  let returnDataSizeSpec : ContractSpec := {
    name := "ReturnDataSizeUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "returndatasize" [])]
      }
    ]
  }
  match compile returnDataSizeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'returndatasize'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ returndatasize diagnostic mismatch: {err}")
      IO.println "✓ returndatasize unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected returndatasize usage to fail compilation")

#eval! do
  let returnDataCopySpec : ContractSpec := {
    name := "ReturnDataCopyUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "returndatacopy" [])]
      }
    ]
  }
  match compile returnDataCopySpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'returndatacopy'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ returndatacopy diagnostic mismatch: {err}")
      IO.println "✓ returndatacopy unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected returndatacopy usage to fail compilation")

#eval! do
  let selfDestructSpec : ContractSpec := {
    name := "SelfDestructUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "target", ty := ParamType.address }]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "selfdestruct" [Expr.param "target"]), Stmt.stop]
      }
    ]
  }
  match compile selfDestructSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'selfdestruct'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ selfdestruct diagnostic mismatch: {err}")
      IO.println "✓ selfdestruct unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected selfdestruct usage to fail compilation")

#eval! do
  let invalidBuiltinSpec : ContractSpec := {
    name := "InvalidBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "invalid" [])]
      }
    ]
  }
  match compile invalidBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'invalid'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ invalid builtin diagnostic mismatch: {err}")
      IO.println "✓ invalid builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid builtin usage to fail compilation")

#eval! do
  let mloadBuiltinSpec : ContractSpec := {
    name := "MloadBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "offset", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "mload" [Expr.param "offset"])]
      }
    ]
  }
  match compile mloadBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'mload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ mload builtin diagnostic mismatch: {err}")
      IO.println "✓ mload builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected mload builtin usage to fail compilation")

#eval! do
  let sstoreBuiltinSpec : ContractSpec := {
    name := "SstoreBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [
          { name := "slot", ty := ParamType.uint256 },
          { name := "value", ty := ParamType.uint256 }
        ]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "sstore" [Expr.param "slot", Expr.param "value"]), Stmt.stop]
      }
    ]
  }
  match compile sstoreBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'sstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ sstore builtin diagnostic mismatch: {err}")
      IO.println "✓ sstore builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected sstore builtin usage to fail compilation")

#eval! do
  let tloadBuiltinSpec : ContractSpec := {
    name := "TloadBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [{ name := "slot", ty := ParamType.uint256 }]
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.externalCall "tload" [Expr.param "slot"])]
      }
    ]
  }
  match compile tloadBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ tload builtin diagnostic mismatch: {err}")
      IO.println "✓ tload builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected tload builtin usage to fail compilation")

#eval! do
  let tstoreBuiltinSpec : ContractSpec := {
    name := "TstoreBuiltinUnsupported"
    fields := []
    constructor := none
    functions := [
      { name := "probe"
        params := [
          { name := "slot", ty := ParamType.uint256 },
          { name := "value", ty := ParamType.uint256 }
        ]
        returnType := none
        body := [Stmt.letVar "_ignored" (Expr.externalCall "tstore" [Expr.param "slot", Expr.param "value"]), Stmt.stop]
      }
    ]
  }
  match compile tstoreBuiltinSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ tstore builtin diagnostic mismatch: {err}")
      IO.println "✓ tstore builtin unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected tstore builtin usage to fail compilation")

#eval! do
  let externalBalanceSpec : ContractSpec := {
    name := "ExternalBalanceUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "balance"
        params := [ParamType.address]
        returnType := some ParamType.uint256
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
  match compile externalBalanceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'balance'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external balance diagnostic mismatch: {err}")
      IO.println "✓ external balance unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external balance declaration to fail compilation")

#eval! do
  let externalGasPriceSpec : ContractSpec := {
    name := "ExternalGasPriceUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "gasprice"
        params := []
        returnType := some ParamType.uint256
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
  match compile externalGasPriceSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'gasprice'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external gasprice diagnostic mismatch: {err}")
      IO.println "✓ external gasprice unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external gasprice declaration to fail compilation")

#eval! do
  let externalBlobBaseFeeSpec : ContractSpec := {
    name := "ExternalBlobBaseFeeUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "blobbasefee"
        params := []
        returnType := some ParamType.uint256
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
  match compile externalBlobBaseFeeSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobbasefee'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external blobbasefee diagnostic mismatch: {err}")
      IO.println "✓ external blobbasefee unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external blobbasefee declaration to fail compilation")

#eval! do
  let externalBlobHashSpec : ContractSpec := {
    name := "ExternalBlobHashUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "blobhash"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
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
  match compile externalBlobHashSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'blobhash'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external blobhash diagnostic mismatch: {err}")
      IO.println "✓ external blobhash unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external blobhash declaration to fail compilation")

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
  let externalCreateSpec : ContractSpec := {
    name := "ExternalCreateUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "create"
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
  match compile externalCreateSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'create'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external create diagnostic mismatch: {err}")
      IO.println "✓ external create unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external create declaration to fail compilation")

#eval! do
  let externalMloadSpec : ContractSpec := {
    name := "ExternalMloadUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "mload"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
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
  match compile externalMloadSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'mload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external mload diagnostic mismatch: {err}")
      IO.println "✓ external mload unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external mload declaration to fail compilation")

#eval! do
  let externalSstoreSpec : ContractSpec := {
    name := "ExternalSstoreUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "sstore"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := none
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
  match compile externalSstoreSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'sstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external sstore diagnostic mismatch: {err}")
      IO.println "✓ external sstore unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external sstore declaration to fail compilation")

#eval! do
  let externalTloadSpec : ContractSpec := {
    name := "ExternalTloadUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "tload"
        params := [ParamType.uint256]
        returnType := some ParamType.uint256
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
  match compile externalTloadSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tload'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external tload diagnostic mismatch: {err}")
      IO.println "✓ external tload unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external tload declaration to fail compilation")

#eval! do
  let externalTstoreSpec : ContractSpec := {
    name := "ExternalTstoreUnsupported"
    fields := []
    constructor := none
    externals := [
      { name := "tstore"
        params := [ParamType.uint256, ParamType.uint256]
        returnType := none
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
  match compile externalTstoreSpec [1] with
  | .error err =>
      if !(contains err "unsupported interop builtin call 'tstore'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ external tstore diagnostic mismatch: {err}")
      IO.println "✓ external tstore unsupported diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected external tstore declaration to fail compilation")

#eval! do
  let unknownCustomErrorSpec : ContractSpec := {
    name := "UnknownCustomError"
    fields := []
    constructor := none
    functions := [
      { name := "bad"
        params := []
        returnType := none
        body := [Stmt.revertError "MissingError" []]
      }
    ]
  }
  match compile unknownCustomErrorSpec [1] with
  | .error err =>
      if !(contains err "unknown custom error 'MissingError'" && contains err "Issue #586") then
        throw (IO.userError s!"✗ unknown custom error diagnostic mismatch: {err}")
      IO.println "✓ unknown custom error diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected unknown custom error usage to fail compilation")

#eval! do
  let bytesCustomErrorSpec : ContractSpec := {
    name := "BytesCustomErrorSupported"
    fields := []
    constructor := none
    errors := [
      { name := "BadPayload"
        params := [ParamType.bytes]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.revertError "BadPayload" [Expr.param "payload"]]
      }
    ]
  }
  match compile bytesCustomErrorSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected bytes custom error support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "bytes custom error ABI encoding" rendered
        ["mstore(4, __err_tail)",
         "let __err_arg0_len := payload_length",
         "calldatacopy(add(__err_arg0_dst, 32), payload_data_offset, __err_arg0_len)",
         "let __err_arg0_padded := and(add(__err_arg0_len, 31), not(31))",
         "revert(0, add(4, __err_tail))"]

#eval! do
  let bytesCustomErrorArgShapeSpec : ContractSpec := {
    name := "BytesCustomErrorArgShapeUnsupported"
    fields := []
    constructor := none
    errors := [
      { name := "BadPayload"
        params := [ParamType.bytes]
      }
    ]
    functions := [
      { name := "bad"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.revertError "BadPayload" [Expr.param "x"]]
      }
    ]
  }
  match compile bytesCustomErrorArgShapeSpec [1] with
  | .error err =>
      if !(contains err "expects bytes arg to reference a bytes parameter" && contains err "Issue #586") then
        throw (IO.userError s!"✗ bytes custom error arg-shape diagnostic mismatch: {err}")
      IO.println "✓ bytes custom error arg-shape diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid bytes custom error arg shape to fail compilation")

#eval! do
  let unindexedBytesEventSpec : ContractSpec := {
    name := "UnindexedBytesEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitBytes"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "UnindexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedBytesEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed bytes event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed bytes event ABI data encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_len := payload_length",
         "calldatacopy(add(__evt_arg0_dst, 32), payload_data_offset, __evt_arg0_len)",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedTupleEventSpec : ContractSpec := {
    name := "UnindexedTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address], kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address] }]
        returnType := none
        body := [Stmt.emit "UnindexedTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed static tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed static tuple event encoding" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), and(payload_1,",
         "log1(__evt_ptr, 64, __evt_topic0)"]

#eval! do
  let unindexedFixedArrayEventSpec : ContractSpec := {
    name := "UnindexedFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray ParamType.uint256 2, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitFixed"
        params := [{ name := "payload", ty := ParamType.fixedArray ParamType.uint256 2 }]
        returnType := none
        body := [Stmt.emit "UnindexedFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed static fixed-array event encoding" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), payload_1)",
         "log1(__evt_ptr, 64, __evt_topic0)"]

#eval! do
  let unindexedDynamicArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.uint256, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 32)",
         "let __evt_arg0_i := 0",
         "let __evt_topic0 := keccak256(__evt_ptr,",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicStaticTupleArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicStaticTupleArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicStaticTupleArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]), kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]) }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicStaticTupleArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicStaticTupleArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic static-tuple array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic static-tuple array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 64)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), iszero(iszero(calldataload(add(__evt_arg0_elem_base, 32)))))",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicBytes32ArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicBytes32ArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicBytes32Array"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes32, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes32 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicBytes32Array" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicBytes32ArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic bytes32 array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic bytes32 array event encoding" rendered
        ["let __evt_data_tail := 32",
         "let __evt_arg0_byte_len := mul(__evt_arg0_len, 32)",
         "let __evt_arg0_i := 0",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "mstore(add(__evt_arg0_out_base, 0), calldataload(add(__evt_arg0_elem_base, 0)))",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicBytesArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicBytesArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicBytesArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicBytesArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicBytesArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic bytes array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic bytes array event encoding" rendered
        ["let __evt_data_tail := 32",
         "let __evt_arg0_head_len := mul(__evt_arg0_len, 32)",
         "mstore(__evt_arg0_elem_dst, __evt_arg0_elem_len)",
         "mstore(add(add(__evt_arg0_dst, 32), mul(__evt_arg0_i, 32)), __evt_arg0_tail_len)",
         "calldatacopy(add(__evt_arg0_elem_dst, 32), __evt_arg0_elem_data, __evt_arg0_elem_len)",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicCompositeArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicCompositeArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicCompositeArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]), kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicCompositeArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]) }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicCompositeArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicCompositeArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic composite array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic composite array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(__evt_arg0_dst, __evt_arg0_arr_len)",
         "let __evt_arg0_arr_tail_len := __evt_arg0_arr_head_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicTupleEventSpec : ContractSpec := {
    name := "UnindexedDynamicTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes], kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic tuple event to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic tuple event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "__evt_arg0_tail_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let unindexedDynamicFixedArrayEventSpec : ContractSpec := {
    name := "UnindexedDynamicFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "UnindexedDynamicFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bytes]) 2, kind := EventParamKind.unindexed }
        ]
      }
    ]
    functions := [
      { name := "emitDynamicFixedArray"
        params := [{ name := "payload", ty := ParamType.fixedArray (ParamType.tuple [ParamType.uint256, ParamType.bytes]) 2 }]
        returnType := none
        body := [Stmt.emit "UnindexedDynamicFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile unindexedDynamicFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected unindexed dynamic fixed-array event to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "unindexed dynamic fixed-array event encoding" rendered
        ["let __evt_data_tail := 32",
         "mstore(add(__evt_ptr, 0), __evt_data_tail)",
         "__evt_arg0_fa_tail_len",
         "log1(__evt_ptr, __evt_data_tail, __evt_topic0)"]

#eval! do
  let indexedBytesEventSpec : ContractSpec := {
    name := "IndexedBytesEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBytes"
        params := [{ name := "payload", ty := ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "IndexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedBytesEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed bytes event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed bytes topic hashing" rendered
        ["calldatacopy(__evt_ptr, payload_data_offset, payload_length)",
         "let __evt_topic1 := keccak256(__evt_ptr, payload_length)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedBytesEventArgTypeMismatchSpec : ContractSpec := {
    name := "IndexedBytesEventArgTypeMismatch"
    fields := []
    constructor := none
    events := [
      { name := "IndexedBytes"
        params := [
          { name := "payload", ty := ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBadBytes"
        params := [{ name := "payload", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "IndexedBytes" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedBytesEventArgTypeMismatchSpec [1] with
  | .error err =>
      if !(contains err "event 'IndexedBytes' param 'payload' expects" &&
          contains err "ParamType.bytes" &&
          contains err "Issue #586") then
        throw (IO.userError s!"✗ indexed bytes event arg type diagnostic mismatch: {err}")
      IO.println "✓ indexed bytes event arg type diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid indexed bytes event arg type usage to fail compilation")

#eval! do
  let indexedTupleEventSpec : ContractSpec := {
    name := "IndexedTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address], kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitTuple"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.address] }]
        returnType := none
        body := [Stmt.emit "IndexedTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed static tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed static tuple topic hashing" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), and(payload_1",
         "let __evt_topic1 := keccak256(__evt_ptr, 64)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedFixedArrayEventSpec : ContractSpec := {
    name := "IndexedFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedFixedArray"
        params := [
          { name := "payload", ty := ParamType.fixedArray ParamType.uint256 2, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitFixed"
        params := [{ name := "payload", ty := ParamType.fixedArray ParamType.uint256 2 }]
        returnType := none
        body := [Stmt.emit "IndexedFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed static fixed-array topic hashing" rendered
        ["mstore(add(__evt_ptr, 0), payload_0)",
         "mstore(add(__evt_ptr, 32), payload_1)",
         "let __evt_topic1 := keccak256(__evt_ptr, 64)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicTupleEventSpec : ContractSpec := {
    name := "IndexedDynamicTupleEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "BadIndexedDynamicTuple"
        params := [
          { name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes], kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBad"
        params := [{ name := "payload", ty := ParamType.tuple [ParamType.uint256, ParamType.bytes] }]
        returnType := none
        body := [Stmt.emit "BadIndexedDynamicTuple" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicTupleEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic tuple event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic tuple topic hashing" rendered
        ["let __evt_arg0_indexed_tuple_out_len := 0",
         "let __evt_arg0_indexed_tuple_elem_rel_1 := calldataload(add(add(4, payload_offset), 32))",
         "let __evt_arg0_indexed_tuple_elem_1_len := calldataload(__evt_arg0_indexed_tuple_elem_src_1)",
         "calldatacopy(__evt_arg0_indexed_tuple_elem_dst_1, add(__evt_arg0_indexed_tuple_elem_src_1, 32), __evt_arg0_indexed_tuple_elem_1_len)",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_indexed_tuple_out_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.uint256, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.uint256 }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 32)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicStaticTupleArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicStaticTupleArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicStaticTupleArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.address, ParamType.bool]) }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicStaticTupleArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicStaticTupleArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic static-tuple array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic static-tuple array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 64)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), iszero(iszero(calldataload(add(__evt_arg0_elem_base, 32)))))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicBytes32ArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicBytes32ArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicBytes32Array"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes32, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes32 }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicBytes32Array" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicBytes32ArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic bytes32 array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic bytes32 array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 32)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "let __evt_arg0_elem_base := add(payload_data_offset, mul(__evt_arg0_i, 32))",
         "mstore(add(__evt_arg0_out_base, 0), calldataload(add(__evt_arg0_elem_base, 0)))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicBytesArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicBytesArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicBytesArray"
        params := [
          { name := "payload", ty := ParamType.array ParamType.bytes, kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array ParamType.bytes }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicBytesArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicBytesArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic bytes array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic bytes array topic hashing" rendered
        ["let __evt_arg0_tail_len := 0",
         "let __evt_arg0_elem_offset := calldataload(add(payload_data_offset, mul(__evt_arg0_i, 32)))",
         "let __evt_arg0_elem_len := calldataload(__evt_arg0_elem_len_pos)",
         "calldatacopy(__evt_arg0_elem_dst, __evt_arg0_elem_data, __evt_arg0_elem_len)",
         "let __evt_arg0_elem_padded := and(add(__evt_arg0_elem_len, 31), not(31))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_tail_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicStaticFixedArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicStaticFixedArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "IndexedDynamicStaticFixedArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.fixedArray ParamType.address 2), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitArray"
        params := [{ name := "payload", ty := ParamType.array (ParamType.fixedArray ParamType.address 2) }]
        returnType := none
        body := [Stmt.emit "IndexedDynamicStaticFixedArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicStaticFixedArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic static fixed-array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic static fixed-array topic hashing" rendered
        ["let __evt_arg0_byte_len := mul(payload_length, 64)",
         "let __evt_arg0_i := 0",
         "lt(__evt_arg0_i, payload_length)",
         "mstore(add(__evt_arg0_out_base, 0), and(calldataload(add(__evt_arg0_elem_base, 0))",
         "mstore(add(__evt_arg0_out_base, 32), and(calldataload(add(__evt_arg0_elem_base, 32))",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_byte_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let indexedDynamicCompositeArrayEventSpec : ContractSpec := {
    name := "IndexedDynamicCompositeArrayEventSupported"
    fields := []
    constructor := none
    events := [
      { name := "BadIndexedDynamicCompositeArray"
        params := [
          { name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]), kind := EventParamKind.indexed }
        ]
      }
    ]
    functions := [
      { name := "emitBad"
        params := [{ name := "payload", ty := ParamType.array (ParamType.tuple [ParamType.uint256, ParamType.bytes]) }]
        returnType := none
        body := [Stmt.emit "BadIndexedDynamicCompositeArray" [Expr.param "payload"], Stmt.stop]
      }
    ]
  }
  match compile indexedDynamicCompositeArrayEventSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected indexed dynamic composite array event support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "indexed dynamic composite array event topic hashing" rendered
        ["let __evt_arg0_indexed_arr_len := calldataload(add(4, payload_offset))",
         "let __evt_arg0_indexed_arr_elem_rel := calldataload(add(__evt_arg0_indexed_arr_data, mul(__evt_arg0_indexed_arr_i, 32)))",
         "let __evt_arg0_indexed_arr_elem_tuple_elem_rel_1 := calldataload(add(__evt_arg0_indexed_arr_elem_src, 32))",
         "calldatacopy(__evt_arg0_indexed_arr_elem_tuple_elem_dst_1, add(__evt_arg0_indexed_arr_elem_tuple_elem_src_1, 32), __evt_arg0_indexed_arr_elem_tuple_elem_1_len)",
         "let __evt_topic1 := keccak256(__evt_ptr, __evt_arg0_indexed_arr_out_len)",
         "log2(__evt_ptr, 0, __evt_topic0, __evt_topic1)"]

#eval! do
  let internalVoidReturnSpec : ContractSpec := {
    name := "InternalVoidReturnRejected"
    fields := []
    constructor := none
    functions := [
      { name := "badInternal"
        params := []
        returnType := none
        isInternal := true
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile internalVoidReturnSpec [] with
  | .error err =>
      if !contains err "uses Stmt.return but declares no return values" then
        throw (IO.userError s!"✗ internal void return diagnostic mismatch: {err}")
      IO.println "✓ internal void return validation"
  | .ok _ =>
      throw (IO.userError "✗ expected internal void Stmt.return usage to fail compilation")

#eval! do
  let internalMultiReturnSpec : ContractSpec := {
    name := "InternalMultiReturnSupported"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := [
          { name := "left", ty := ParamType.uint256 },
          { name := "right", ty := ParamType.uint256 }
        ]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.param "left", Expr.param "right"]]
      },
      { name := "project"
        params := [
          { name := "left", ty := ParamType.uint256 },
          { name := "right", ty := ParamType.uint256 }
        ]
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        body := [
          Stmt.internalCallAssign ["a", "b"] "pair" [Expr.param "left", Expr.param "right"],
          Stmt.returnValues [Expr.localVar "a", Expr.localVar "b"]
        ]
      }
    ]
  }
  match compile internalMultiReturnSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ expected internal multi-return support to compile, got: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "internal multi-return codegen" rendered
        ["function internal_pair(left, right) -> __ret0, __ret1",
         "__ret0 := left",
         "__ret1 := right",
         "let a, b := internal_pair(left, right)",
         "return(0, 64)"]

#eval! do
  let exprInternalCallMultiReturnSpec : ContractSpec := {
    name := "ExprInternalCallMultiReturnRejected"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      },
      { name := "badExprUse"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.internalCall "pair" [])]
      }
    ]
  }
  match compile exprInternalCallMultiReturnSpec [1] with
  | .error err =>
      if !(contains err "uses Expr.internalCall 'pair' but callee returns 2 values" &&
          contains err "Issue #625") then
        throw (IO.userError s!"✗ expr internalCall multi-return diagnostic mismatch: {err}")
      IO.println "✓ expr internalCall multi-return diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected Expr.internalCall on multi-return internal function to fail compilation")

#eval! do
  let internalCallAssignArityMismatchSpec : ContractSpec := {
    name := "InternalCallAssignArityMismatch"
    fields := []
    constructor := none
    functions := [
      { name := "pair"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        isInternal := true
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      },
      { name := "badBind"
        params := []
        returnType := some FieldType.uint256
        body := [
          Stmt.internalCallAssign ["onlyOne"] "pair" [],
          Stmt.return (Expr.localVar "onlyOne")
        ]
      }
    ]
  }
  match compile internalCallAssignArityMismatchSpec [1] with
  | .error err =>
      if !(contains err "binds 1 values from internal function 'pair', but callee returns 2" &&
          contains err "Issue #625") then
        throw (IO.userError s!"✗ internalCallAssign arity diagnostic mismatch: {err}")
      IO.println "✓ internalCallAssign arity diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected internalCallAssign arity mismatch to fail compilation")

#eval! do
  let multiReturnWithSingleReturnStmtSpec : ContractSpec := {
    name := "MultiReturnWithSingleStmtRejected"
    fields := []
    constructor := none
    functions := [
      { name := "badExternal"
        params := []
        returnType := none
        returns := [ParamType.uint256, ParamType.uint256]
        body := [Stmt.return (Expr.literal 1)]
      }
    ]
  }
  match compile multiReturnWithSingleReturnStmtSpec [1] with
  | .error err =>
      if !contains err "declares multiple return values; use Stmt.returnValues" then
        throw (IO.userError s!"✗ single-return stmt on multi-return function diagnostic mismatch: {err}")
      IO.println "✓ multi-return Stmt.return validation"
  | .ok _ =>
      throw (IO.userError "✗ expected single-value return statement on multi-return function to fail compilation")

#eval! do
  let returnValuesArityMismatchSpec : ContractSpec := {
    name := "ReturnValuesArityMismatch"
    fields := []
    constructor := none
    functions := [
      { name := "badArity"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.returnValues [Expr.literal 1, Expr.literal 2]]
      }
    ]
  }
  match compile returnValuesArityMismatchSpec [1] with
  | .error err =>
      if !contains err "returnValues count mismatch: expected 1, got 2" then
        throw (IO.userError s!"✗ returnValues arity diagnostic mismatch: {err}")
      IO.println "✓ returnValues arity validation"
  | .ok _ =>
      throw (IO.userError "✗ expected returnValues arity mismatch to fail compilation")

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

#eval! do
  let explicitFieldSlotSpec : ContractSpec := {
    name := "ExplicitFieldSlotSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 5 },
      { name := "b", ty := FieldType.uint256 },
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9 }
    ]
    constructor := none
    functions := [
      { name := "setA"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "a" (Expr.param "x"), Stmt.stop]
      },
      { name := "setB"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "b" (Expr.param "x"), Stmt.stop]
      },
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile explicitFieldSlotSpec [1, 2, 3] with
  | .error err =>
      throw (IO.userError s!"✗ explicit field slot compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "explicit slot setStorage lowering" rendered ["sstore(5, x)"]
      assertContains "legacy positional slot fallback lowering" rendered ["sstore(1, x)"]
      assertContains "explicit slot mapping lowering" rendered ["mappingSlot(9, who)"]

#eval! do
  let aliasSlotMirrorWriteSpec : ContractSpec := {
    name := "AliasSlotMirrorWriteSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 8, aliasSlots := [20] },
      { name := "balances", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 9, aliasSlots := [21] }
    ]
    constructor := none
    functions := [
      { name := "setA"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "a" (Expr.param "x"), Stmt.stop]
      },
      { name := "setBal"
        params := [{ name := "who", ty := ParamType.address }, { name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setMapping "balances" (Expr.param "who") (Expr.param "x"), Stmt.stop]
      }
    ]
  }
  match compile aliasSlotMirrorWriteSpec [1, 2] with
  | .error err =>
      throw (IO.userError s!"✗ alias slot mirror-write compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "setStorage mirror writes to alias slots" rendered
        ["sstore(8, __compat_value)", "sstore(20, __compat_value)"]
      assertContains "setMapping mirror writes to alias slots" rendered
        ["mappingSlot(9, __compat_key)", "mappingSlot(21, __compat_key)"]

#eval! do
  let packedSubfieldSpec : ContractSpec := {
    name := "PackedSubfieldSpec"
    fields := [
      { name := "lower", ty := FieldType.uint256, slot := some 4, packedBits := some { offset := 0, width := 128 } },
      { name := "upper", ty := FieldType.uint256, slot := some 4, packedBits := some { offset := 128, width := 128 } }
    ]
    constructor := none
    functions := [
      { name := "setLower"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "lower" (Expr.param "x"), Stmt.stop]
      },
      { name := "setUpper"
        params := [{ name := "x", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "upper" (Expr.param "x"), Stmt.stop]
      },
      { name := "getLower"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.storage "lower")]
      },
      { name := "getUpper"
        params := []
        returnType := some FieldType.uint256
        body := [Stmt.return (Expr.storage "upper")]
      }
    ]
  }
  match compile packedSubfieldSpec [1, 2, 3, 4] with
  | .error err =>
      throw (IO.userError s!"✗ packed subfield compile failed: {err}")
  | .ok ir =>
      let rendered := Yul.render (emitYul ir)
      assertContains "packed setStorage lowers masked read-modify-write" rendered
        ["let __compat_slot_word := sload(4)", "sstore(4, or(__compat_slot_cleared, shl(0, __compat_packed)))", "sstore(4, or(__compat_slot_cleared, shl(128, __compat_packed)))"]
      assertContains "packed Expr.storage lowers masked shifted reads" rendered
        ["and(shr(0, sload(4)),", "and(shr(128, sload(4)),"]

#eval! do
  let overlappingPackedSubfieldSpec : ContractSpec := {
    name := "OverlappingPackedSubfieldSpec"
    fields := [
      { name := "a", ty := FieldType.uint256, slot := some 7, packedBits := some { offset := 0, width := 128 } },
      { name := "b", ty := FieldType.uint256, slot := some 7, packedBits := some { offset := 64, width := 128 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile overlappingPackedSubfieldSpec [1] with
  | .error err =>
      if !(contains err "storage slot 7 has overlapping write ranges for 'a' and 'b'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ overlapping packed subfield diagnostic mismatch: {err}")
      IO.println "✓ overlapping packed subfield diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected overlapping packed subfields to fail compilation")

#eval! do
  let invalidPackedBitsSpec : ContractSpec := {
    name := "InvalidPackedBitsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 2, packedBits := some { offset := 200, width := 80 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile invalidPackedBitsSpec [1] with
  | .error err =>
      if !(contains err "field 'x' has invalid packedBits offset=200 width=80" && contains err "Issue #623") then
        throw (IO.userError s!"✗ invalid packedBits diagnostic mismatch: {err}")
      IO.println "✓ invalid packedBits diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected invalid packedBits to fail compilation")

#eval! do
  let packedMappingRejectedSpec : ContractSpec := {
    name := "PackedMappingRejectedSpec"
    fields := [
      { name := "m", ty := FieldType.mappingTyped (MappingType.simple MappingKeyType.address), slot := some 5, packedBits := some { offset := 0, width := 128 } }
    ]
    constructor := none
    functions := [{ name := "noop", params := [], returnType := none, body := [Stmt.stop] }]
  }
  match compile packedMappingRejectedSpec [1] with
  | .error err =>
      if !(contains err "field 'm' is a mapping and cannot declare packedBits" && contains err "Issue #623") then
        throw (IO.userError s!"✗ packed mapping diagnostic mismatch: {err}")
      IO.println "✓ packed mapping diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected mapping packedBits to fail compilation")

#eval! do
  let conflictingFieldSlotsSpec : ContractSpec := {
    name := "ConflictingFieldSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3 },
      { name := "y", ty := FieldType.address, slot := some 3 }
    ]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile conflictingFieldSlotsSpec [1] with
  | .error err =>
      if !(contains err "storage slot 3 has overlapping write ranges for 'x' and 'y'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ conflicting explicit field slot diagnostic mismatch: {err}")
      IO.println "✓ conflicting explicit field slot diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting explicit field slots to fail compilation")

#eval! do
  let conflictingAliasSlotsSpec : ContractSpec := {
    name := "ConflictingAliasSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3, aliasSlots := [7] },
      { name := "y", ty := FieldType.address, slot := some 4, aliasSlots := [7] }
    ]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile conflictingAliasSlotsSpec [1] with
  | .error err =>
      if !(contains err "storage slot 7 has overlapping write ranges for 'x.aliasSlots[0]' and 'y.aliasSlots[0]'" && contains err "Issue #623") then
        throw (IO.userError s!"✗ conflicting alias slot diagnostic mismatch: {err}")
      IO.println "✓ conflicting alias slot diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected conflicting alias slots to fail compilation")

#eval! do
  let reservedSlotsSpec : ContractSpec := {
    name := "ReservedSlotsSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 3 },
      { name := "y", ty := FieldType.uint256, slot := some 4, aliasSlots := [12] }
    ]
    reservedSlotRanges := [{ start := 20, end_ := 23 }]
    constructor := none
    functions := [
      { name := "setX"
        params := [{ name := "v", ty := ParamType.uint256 }]
        returnType := none
        body := [Stmt.setStorage "x" (Expr.param "v"), Stmt.stop]
      }
    ]
  }
  match compile reservedSlotsSpec [1] with
  | .error err =>
      throw (IO.userError s!"✗ reserved slot ranges compile failed: {err}")
  | .ok _ =>
      IO.println "✓ reserved slot ranges accepted when disjoint from field write slots"

#eval! do
  let reservedSlotConflictSpec : ContractSpec := {
    name := "ReservedSlotConflictSpec"
    fields := [
      { name := "x", ty := FieldType.uint256, slot := some 21 }
    ]
    reservedSlotRanges := [{ start := 20, end_ := 23 }]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile reservedSlotConflictSpec [1] with
  | .error err =>
      if !(contains err "field write slot 21 ('x') overlaps reservedSlotRanges[0]=20..23" && contains err "Issue #623") then
        throw (IO.userError s!"✗ reserved slot conflict diagnostic mismatch: {err}")
      IO.println "✓ reserved slot conflict diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected reserved slot conflict to fail compilation")

#eval! do
  let overlappingReservedRangesSpec : ContractSpec := {
    name := "OverlappingReservedRangesSpec"
    fields := [{ name := "x", ty := FieldType.uint256, slot := some 3 }]
    reservedSlotRanges := [{ start := 20, end_ := 23 }, { start := 23, end_ := 30 }]
    constructor := none
    functions := [
      { name := "noop"
        params := []
        returnType := none
        body := [Stmt.stop]
      }
    ]
  }
  match compile overlappingReservedRangesSpec [1] with
  | .error err =>
      if !(contains err "reserved slot ranges reservedSlotRanges[0]=20..23 and reservedSlotRanges[1]=23..30 overlap" && contains err "Issue #623") then
        throw (IO.userError s!"✗ reserved range overlap diagnostic mismatch: {err}")
      IO.println "✓ reserved range overlap diagnostic"
  | .ok _ =>
      throw (IO.userError "✗ expected overlapping reserved slot ranges to fail compilation")

end Compiler.ContractSpecFeatureTest
