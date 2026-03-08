/- 
  Compiler.Modules.ERC4626: ERC-4626 Vault Interaction Modules

  Standard ECMs for read-only ERC-4626 integrations:
  - `previewDeposit`: staticcall `previewDeposit(uint256)` and require exactly
    one 32-byte return word.

  Trust assumption: the target address implements the selected ERC-4626 read
  interface and returns one ABI-encoded `uint256` word.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.ERC4626

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

/-- Read-only ERC-4626 `previewDeposit(uint256)` module.

    It ABI-encodes the canonical `previewDeposit(uint256)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, assets]`. -/
def previewDepositModule (resultVar : String) : ExternalCallModule where
  name := "previewDeposit"
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["erc4626_previewDeposit_interface"]
  compile := fun _ctx args => do
    let (vaultExpr, assetsExpr) ← match args with
      | [vault, assets] => pure (vault, assets)
      | _ => throw "previewDeposit expects 2 arguments (vault, assets)"
    let selector := 0xef8b30f7
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit 0,
      YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    ])
    let storeAssets := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, assetsExpr])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      vaultExpr,
      YulExpr.lit 0, YulExpr.lit 36,
      YulExpr.lit 0, YulExpr.lit 32
    ]
    let revertOnFailure := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__erc4626_success"]) [
      YulStmt.let_ "__erc4626_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__erc4626_rds"
      ]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__erc4626_rds"])
    ]
    let requireSingleWord := YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]
    ]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.call "mload" [YulExpr.lit 0])
    pure [YulStmt.block [
      storeSelector,
      storeAssets,
      YulStmt.let_ "__erc4626_success" callExpr,
      revertOnFailure,
      requireSingleWord
    ], bindResult]

/-- Convenience: create a `Stmt.ecm` for a read-only `previewDeposit(uint256)`
    call. -/
def previewDeposit (resultVar : String) (vault assets : Expr) : Stmt :=
  .ecm (previewDepositModule resultVar) [vault, assets]

end Compiler.Modules.ERC4626
