/- 
  Compiler.Modules.ERC4626: ERC-4626 Vault Interaction Modules

  Standard ECMs for read-only ERC-4626 integrations:
  - `previewDeposit`: staticcall `previewDeposit(uint256)` and require exactly
    one 32-byte return word.
  - `previewMint`: staticcall `previewMint(uint256)` and require exactly one
    32-byte return word.
  - `previewWithdraw`: staticcall `previewWithdraw(uint256)` and require
    exactly one 32-byte return word.
  - `previewRedeem`: staticcall `previewRedeem(uint256)` and require exactly
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

/-- Shared implementation for read-only ERC-4626 preview calls that take a
    single `uint256` argument and return one ABI-encoded `uint256` word. -/
private def previewUint256Module
    (moduleName : String)
    (axiomName : String)
    (resultVar : String)
    (selector : Nat)
    (argName : String) : ExternalCallModule where
  name := moduleName
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := [axiomName]
  compile := fun _ctx args => do
    let (vaultExpr, argExpr) ← match args with
      | [vault, value] => pure (vault, value)
      | _ => throw s!"{moduleName} expects 2 arguments (vault, {argName})"
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit 0,
      YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    ])
    let storeArg := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, argExpr])
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
      storeArg,
      YulStmt.let_ "__erc4626_success" callExpr,
      revertOnFailure,
      requireSingleWord
    ], bindResult]

/-- Read-only ERC-4626 `previewDeposit(uint256)` module.

    It ABI-encodes the canonical `previewDeposit(uint256)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, assets]`. -/
def previewDepositModule (resultVar : String) : ExternalCallModule :=
  previewUint256Module
    "previewDeposit"
    "erc4626_previewDeposit_interface"
    resultVar
    0xef8b30f7
    "assets"

/-- Convenience: create a `Stmt.ecm` for a read-only `previewDeposit(uint256)`
    call. -/
def previewDeposit (resultVar : String) (vault assets : Expr) : Stmt :=
  .ecm (previewDepositModule resultVar) [vault, assets]

/-- Read-only ERC-4626 `previewMint(uint256)` module.

    It ABI-encodes the canonical `previewMint(uint256)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, shares]`. -/
def previewMintModule (resultVar : String) : ExternalCallModule :=
  previewUint256Module
    "previewMint"
    "erc4626_previewMint_interface"
    resultVar
    0xb3d7f6b9
    "shares"

/-- Convenience: create a `Stmt.ecm` for a read-only `previewMint(uint256)`
    call. -/
def previewMint (resultVar : String) (vault shares : Expr) : Stmt :=
  .ecm (previewMintModule resultVar) [vault, shares]

/-- Read-only ERC-4626 `previewWithdraw(uint256)` module.

    It ABI-encodes the canonical `previewWithdraw(uint256)` selector, performs
    a `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, assets]`. -/
def previewWithdrawModule (resultVar : String) : ExternalCallModule :=
  previewUint256Module
    "previewWithdraw"
    "erc4626_previewWithdraw_interface"
    resultVar
    0x0a28a477
    "assets"

/-- Convenience: create a `Stmt.ecm` for a read-only `previewWithdraw(uint256)`
    call. -/
def previewWithdraw (resultVar : String) (vault assets : Expr) : Stmt :=
  .ecm (previewWithdrawModule resultVar) [vault, assets]

/-- Read-only ERC-4626 `previewRedeem(uint256)` module.

    It ABI-encodes the canonical `previewRedeem(uint256)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, shares]`. -/
def previewRedeemModule (resultVar : String) : ExternalCallModule :=
  previewUint256Module
    "previewRedeem"
    "erc4626_previewRedeem_interface"
    resultVar
    0x4cdad506
    "shares"

/-- Convenience: create a `Stmt.ecm` for a read-only `previewRedeem(uint256)`
    call. -/
def previewRedeem (resultVar : String) (vault shares : Expr) : Stmt :=
  .ecm (previewRedeemModule resultVar) [vault, shares]

end Compiler.Modules.ERC4626
