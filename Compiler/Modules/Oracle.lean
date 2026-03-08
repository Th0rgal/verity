/- 
  Compiler.Modules.Oracle: Oracle Read Modules

  Standard ECMs for read-only oracle integrations:
  - `oracleReadUint256`: staticcall a target with ABI-encoded selector and static
    arguments, requiring exactly one 32-byte return word.

  Trust assumption: the target address implements the selected oracle read
  interface and returns one ABI-encoded `uint256` word.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Oracle

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

/-- Read-only oracle module that ABI-encodes `selector(staticArgs...)`, performs
    a `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds it to `resultVar`.

    Arguments passed to the module are `[target] ++ staticArgs`. -/
def oracleReadUint256Module (resultVar : String) (selector : Nat) (numStaticArgs : Nat) :
    ExternalCallModule where
  name := "oracleReadUint256"
  numArgs := 1 + numStaticArgs
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["oracle_read_uint256_interface"]
  compile := fun _ctx args => do
    if selector >= 2^32 then
      throw s!"oracleReadUint256: selector 0x{String.mk (Nat.toDigits 16 selector)} exceeds 4 bytes"
    let targetExpr ← match args.head? with
      | some target => pure target
      | none => throw "oracleReadUint256 expects at least 1 argument (target)"
    let staticArgExprs := args.drop 1
    let calldataSize := 4 + numStaticArgs * 32
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit 0,
      YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    ])
    let storeArgs := staticArgExprs.zipIdx.map fun (argExpr, idx) =>
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (4 + idx * 32), argExpr])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      targetExpr,
      YulExpr.lit 0, YulExpr.lit calldataSize,
      YulExpr.lit 0, YulExpr.lit 32
    ]
    let revertOnFailure := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__oracle_success"]) [
      YulStmt.let_ "__oracle_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__oracle_rds"
      ]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__oracle_rds"])
    ]
    let requireSingleWord := YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit 0])
    pure [YulStmt.block (
      [storeSelector] ++ storeArgs ++
      [YulStmt.let_ "__oracle_success" callExpr, revertOnFailure, requireSingleWord]
    ), bindResult]

/-- Convenience: create a `Stmt.ecm` for a read-only `uint256` oracle call. -/
def oracleReadUint256 (resultVar : String) (target : Expr) (selector : Nat) (staticArgs : List Expr) :
    Stmt :=
  .ecm (oracleReadUint256Module resultVar selector staticArgs.length) ([target] ++ staticArgs)

end Compiler.Modules.Oracle
