/-
  Compiler.Modules.Calls: Generic External Call Modules

  Standard ECM for ABI-encoded external calls with a single uint256 return:
  - `withReturn`: call/staticcall with selector + args, revert-forward on failure,
    validate return data, bind result variable
  - `callWithValue`: generic ETH-aware call over an already prepared calldata
    slice, revert-forward on failure
  - `callWithValueBytes`: generic ETH-aware call over a bytes parameter,
    copying the payload to memory before the call

  Trust assumption: the target contract's function matches the declared
  selector and ABI encoding. For `callWithValue`, the caller is responsible for
  preparing calldata at the supplied memory slice. `callWithValueBytes` copies a
  bytes parameter into memory before calling.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Calls

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

/-- Generic external call with single uint256 return.
    ABI-encodes `selector(args...)`, calls/staticcalls target, reverts on failure,
    validates returndatasize >= 32, and binds the result.

    The module is parameterized by:
    - `resultVar`: name for the bound result variable
    - `selector`: the 4-byte function selector
    - `numArgs`: number of ABI-encoded arguments (not counting target)
    - `isStatic`: true for staticcall, false for call

    Arguments passed to compile: [target] ++ argExprs -/
def withReturnModule (resultVar : String) (selector : Nat) (numArgs : Nat) (isStatic : Bool)
    : ExternalCallModule where
  name := "externalCallWithReturn"
  numArgs := 1 + numArgs  -- target + args
  resultVars := [resultVar]
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  compile := fun _ctx args => do
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "externalCallWithReturn expects at least 1 argument (target)"
    let argExprs := args.drop 1
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (4 + i * 32), argExpr])
    let calldataSize := 4 + numArgs * 32
    let callExpr :=
      if isStatic then
        YulExpr.call "staticcall" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0, YulExpr.lit calldataSize,
          YulExpr.lit 0, YulExpr.lit 32
        ]
      else
        YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0,
          YulExpr.lit 0, YulExpr.lit calldataSize,
          YulExpr.lit 0, YulExpr.lit 32
        ]
    let letSuccess := YulStmt.let_ "__ecwr_success" callExpr
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecwr_success"]) [
      YulStmt.let_ "__ecwr_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecwr_rds"]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecwr_rds"])
    ]
    let sizeCheck := YulStmt.if_ (YulExpr.call "lt" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let callBlock := YulStmt.block ([storeSelector] ++ storeArgs ++ [letSuccess, revertBlock, sizeCheck])
    let bindResult := YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit 0])
    pure [callBlock, bindResult]

/-- Convenience: create a `Stmt.ecm` for an external call with return.
    Replaces the former `Stmt.externalCallWithReturn` variant. -/
def withReturn (resultVar : String) (target : Expr) (selector : Nat)
    (args : List Expr) (isStatic : Bool := false) : Stmt :=
  .ecm (withReturnModule resultVar selector args.length isStatic) ([target] ++ args)

/-- ETH-aware generic external call over an already prepared calldata slice.

    Arguments passed to compile: [target, value, inOffset, inSize].
    The module emits `call(gas(), target, value, inOffset, inSize, 0, 0)`,
    bubbles revert returndata on failure, and ignores successful returndata.

    This is intentionally lower-level than `withReturn`: it is the standard ECM
    for adapter/router patterns that need arbitrary calldata plus `call{value:v}`.
    The caller is responsible for constructing calldata and decoding or ignoring
    any successful returndata. -/
def callWithValueModule : ExternalCallModule where
  name := "callWithValue"
  numArgs := 4
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_call_with_value_interface"]
  compile := fun _ctx args => do
    match args with
    | [targetExpr, valueExpr, inOffsetExpr, inSizeExpr] =>
        let callExpr := YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          valueExpr,
          inOffsetExpr, inSizeExpr,
          YulExpr.lit 0, YulExpr.lit 0
        ]
        let letSuccess := YulStmt.let_ "__cwv_success" callExpr
        let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__cwv_success"]) [
          YulStmt.let_ "__cwv_rds" (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
        ]
        pure [YulStmt.block [letSuccess, revertBlock]]
    | _ =>
        throw "callWithValue expects 4 arguments (target, value, inOffset, inSize)"

/-- Convenience: create a `Stmt.ecm` for an ETH-aware generic call. -/
def callWithValue (target value inOffset inSize : Expr) : Stmt :=
  .ecm callWithValueModule [target, value, inOffset, inSize]

/-- ETH-aware generic external call over a bytes parameter.

    Arguments passed to compile: [target, value].
    The module reads `{bytesParam}_data_offset` and `{bytesParam}_length` from
    the function decoder, copies that bytes payload to memory offset 0, emits
    `call(gas(), target, value, 0, {bytesParam}_length, 0, 0)`, bubbles revert
    returndata on failure, and ignores successful returndata.

    This is the higher-level `(target, value, data)` surface for adapter/router
    patterns. The raw-slice `callWithValueModule` remains available when callers
    have already prepared calldata in memory. -/
def callWithValueBytesModule (bytesParam : String) : ExternalCallModule where
  name := "callWithValue"
  numArgs := 2
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_call_with_value_interface"]
  compile := fun ctx args => do
    if bytesParam.isEmpty then
      throw "callWithValueBytes: bytesParam must be non-empty"
    match args with
    | [targetExpr, valueExpr] =>
        let dataOffsetExpr := YulExpr.ident s!"{bytesParam}_data_offset"
        let dataSizeExpr := YulExpr.ident s!"{bytesParam}_length"
        let copyData := dynamicCopyData ctx (YulExpr.lit 0) dataOffsetExpr dataSizeExpr
        let callExpr := YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          valueExpr,
          YulExpr.lit 0, dataSizeExpr,
          YulExpr.lit 0, YulExpr.lit 0
        ]
        let letSuccess := YulStmt.let_ "__cwv_success" callExpr
        let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__cwv_success"]) [
          YulStmt.let_ "__cwv_rds" (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
        ]
        pure [YulStmt.block (copyData ++ [letSuccess, revertBlock])]
    | _ =>
        throw "callWithValueBytes expects 2 arguments (target, value)"

/-- Convenience: create a `Stmt.ecm` for an ETH-aware generic call over a bytes
    parameter named `bytesParam`. -/
def callWithValueBytes (target value : Expr) (bytesParam : String) : Stmt :=
  .ecm (callWithValueBytesModule bytesParam) [target, value]

end Compiler.Modules.Calls
