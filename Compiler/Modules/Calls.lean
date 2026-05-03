/-
  Compiler.Modules.Calls: Generic External Call Modules

  Standard ECM for ABI-encoded external calls with a single uint256 return:
  - `withReturn`: call/staticcall with selector + args, revert-forward on failure,
    validate return data, bind result variable
  - `bubblingValueCall`: arbitrary low-level call with caller-provided ETH value,
    caller-provided input/output memory slices, and exact revert-data bubbling

  Trust assumption: the target contract's function matches the declared
  selector and ABI encoding. For arbitrary low-level calls, the target contract
  behavior and calldata ABI are deliberately outside Verity core and are surfaced
  as an explicit ECM assumption.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Calls

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

private def bubblingValueCallYul
    (targetExpr valueExpr inputOffsetExpr inputSizeExpr outputOffsetExpr outputSizeExpr : YulExpr) :
    List YulStmt :=
  let callExpr := YulExpr.call "call" [
    YulExpr.call "gas" [],
    targetExpr,
    valueExpr,
    inputOffsetExpr,
    inputSizeExpr,
    outputOffsetExpr,
    outputSizeExpr
  ]
  [YulStmt.block [
    YulStmt.let_ "__bvc_success" callExpr,
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__bvc_success"]) [
      YulStmt.let_ "__bvc_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__bvc_rds"
      ]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__bvc_rds"])
    ]
  ]]

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

/-- Generic Solidity-style low-level value call with revert-data bubbling.

    This models the common wrapper:

    ```
    let success := call(gas(), target, value, inputOffset, inputSize, outputOffset, outputSize)
    if iszero(success) {
      returndatacopy(0, 0, returndatasize())
      revert(0, returndatasize())
    }
    ```

    Arguments passed to compile:
    `[target, value, inputOffset, inputSize, outputOffset, outputSize]`.

    The module intentionally does not interpret the calldata or returndata
    payload. Protocol-specific meaning belongs in packages that use this generic
    Verity-core mechanism and document their own assumptions. -/
def bubblingValueCallModule : ExternalCallModule where
  name := "bubblingValueCall"
  numArgs := 6
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_low_level_value_call_interface"]
  compile := fun _ctx args => do
    let (targetExpr, valueExpr, inputOffsetExpr, inputSizeExpr, outputOffsetExpr, outputSizeExpr) ←
      match args with
      | [target, value, inputOffset, inputSize, outputOffset, outputSize] =>
          pure (target, value, inputOffset, inputSize, outputOffset, outputSize)
      | _ =>
          throw "bubblingValueCall expects 6 arguments (target, value, inputOffset, inputSize, outputOffset, outputSize)"
    pure <| bubblingValueCallYul
      targetExpr valueExpr inputOffsetExpr inputSizeExpr outputOffsetExpr outputSizeExpr

/-- Four-argument no-output variant of `bubblingValueCallModule`.

    This is useful for `verity_contract` `ecmDo` call sites and for adapter or
    router calls where successful returndata is intentionally ignored. Failure
    returndata is still bubbled exactly. -/
def bubblingValueCallNoOutputModule : ExternalCallModule where
  name := "bubblingValueCallNoOutput"
  numArgs := 4
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_low_level_value_call_interface"]
  compile := fun _ctx args => do
    let (targetExpr, valueExpr, inputOffsetExpr, inputSizeExpr) ←
      match args with
      | [target, value, inputOffset, inputSize] =>
          pure (target, value, inputOffset, inputSize)
      | _ =>
          throw "bubblingValueCallNoOutput expects 4 arguments (target, value, inputOffset, inputSize)"
    pure <| bubblingValueCallYul
      targetExpr valueExpr inputOffsetExpr inputSizeExpr (YulExpr.lit 0) (YulExpr.lit 0)

/-- Convenience constructor for `bubblingValueCallModule`. -/
def bubblingValueCall
    (target value inputOffset inputSize outputOffset outputSize : Expr) : Stmt :=
  .ecm bubblingValueCallModule [target, value, inputOffset, inputSize, outputOffset, outputSize]

/-- Convenience constructor for the common adapter/router shape that ignores
    successful returndata while still bubbling failure returndata exactly. -/
def bubblingValueCallNoOutput
    (target value inputOffset inputSize : Expr) : Stmt :=
  .ecm bubblingValueCallNoOutputModule [target, value, inputOffset, inputSize]

end Compiler.Modules.Calls
