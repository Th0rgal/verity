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
  - `convertToAssets`: staticcall `convertToAssets(uint256)` and require
    exactly one 32-byte return word.
  - `convertToShares`: staticcall `convertToShares(uint256)` and require
    exactly one 32-byte return word.
  - `totalAssets`: staticcall `totalAssets()` and require exactly one 32-byte
    return word.
  - `maxDeposit`: staticcall `maxDeposit(address)` and require exactly one
    32-byte return word.
  - `maxMint`: staticcall `maxMint(address)` and require exactly one 32-byte
    return word.
  - `maxWithdraw`: staticcall `maxWithdraw(address)` and require exactly one
    32-byte return word.
  - `maxRedeem`: staticcall `maxRedeem(address)` and require exactly one
    32-byte return word.

  Trust assumption: the target address implements the selected ERC-4626 read
  interface and returns one ABI-encoded `uint256` word.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.ERC4626

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr)

/-- Shared implementation for read-only ERC-4626 calls that return one
    ABI-encoded `uint256` word. -/
private def readUint256Module
    (moduleName : String)
    (axiomName : String)
    (resultVar : String)
    (selector : Nat)
    (argNames : List String) : ExternalCallModule where
  name := moduleName
  numArgs := 1 + argNames.length
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := [axiomName]
  compile := fun _ctx args => do
    let vaultExpr ← match args.head? with
      | some vault => pure vault
      | none => throw s!"{moduleName} expects at least 1 argument (vault)"
    let argExprs := args.drop 1
    if argExprs.length != argNames.length then
      throw s!"{moduleName} expects {1 + argNames.length} arguments (vault{if argNames.isEmpty then "" else s!", {String.intercalate ", " argNames}"})"
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit 0,
      YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    ])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, idx) =>
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (4 + idx * 32), argExpr])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      vaultExpr,
      YulExpr.lit 0, YulExpr.lit (4 + argNames.length * 32),
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
    pure [YulStmt.block (
      [storeSelector] ++ storeArgs ++
      [YulStmt.let_ "__erc4626_success" callExpr, revertOnFailure, requireSingleWord]
    ), bindResult]

/-- Read-only ERC-4626 `previewDeposit(uint256)` module.

    It ABI-encodes the canonical `previewDeposit(uint256)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, assets]`. -/
def previewDepositModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "previewDeposit"
    "erc4626_previewDeposit_interface"
    resultVar
    0xef8b30f7
    ["assets"]

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
  readUint256Module
    "previewMint"
    "erc4626_previewMint_interface"
    resultVar
    0xb3d7f6b9
    ["shares"]

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
  readUint256Module
    "previewWithdraw"
    "erc4626_previewWithdraw_interface"
    resultVar
    0x0a28a477
    ["assets"]

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
  readUint256Module
    "previewRedeem"
    "erc4626_previewRedeem_interface"
    resultVar
    0x4cdad506
    ["shares"]

/-- Convenience: create a `Stmt.ecm` for a read-only `previewRedeem(uint256)`
    call. -/
def previewRedeem (resultVar : String) (vault shares : Expr) : Stmt :=
  .ecm (previewRedeemModule resultVar) [vault, shares]

/-- Read-only ERC-4626 `convertToAssets(uint256)` module.

    It ABI-encodes the canonical `convertToAssets(uint256)` selector, performs
    a `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, shares]`. -/
def convertToAssetsModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "convertToAssets"
    "erc4626_convertToAssets_interface"
    resultVar
    0x07a2d13a
    ["shares"]

/-- Convenience: create a `Stmt.ecm` for a read-only `convertToAssets(uint256)`
    call. -/
def convertToAssets (resultVar : String) (vault shares : Expr) : Stmt :=
  .ecm (convertToAssetsModule resultVar) [vault, shares]

/-- Read-only ERC-4626 `convertToShares(uint256)` module.

    It ABI-encodes the canonical `convertToShares(uint256)` selector, performs
    a `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, assets]`. -/
def convertToSharesModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "convertToShares"
    "erc4626_convertToShares_interface"
    resultVar
    0xc6e6f592
    ["assets"]

/-- Convenience: create a `Stmt.ecm` for a read-only `convertToShares(uint256)`
    call. -/
def convertToShares (resultVar : String) (vault assets : Expr) : Stmt :=
  .ecm (convertToSharesModule resultVar) [vault, assets]

/-- Read-only ERC-4626 `totalAssets()` module.

    It ABI-encodes the canonical `totalAssets()` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault]`. -/
def totalAssetsModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "totalAssets"
    "erc4626_totalAssets_interface"
    resultVar
    0x01e1d114
    []

/-- Convenience: create a `Stmt.ecm` for a read-only `totalAssets()` call. -/
def totalAssets (resultVar : String) (vault : Expr) : Stmt :=
  .ecm (totalAssetsModule resultVar) [vault]

/-- Read-only ERC-4626 `maxDeposit(address)` module.

    It ABI-encodes the canonical `maxDeposit(address)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, receiver]`. -/
def maxDepositModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "maxDeposit"
    "erc4626_maxDeposit_interface"
    resultVar
    0x402d267d
    ["receiver"]

/-- Convenience: create a `Stmt.ecm` for a read-only `maxDeposit(address)`
    call. -/
def maxDeposit (resultVar : String) (vault receiver : Expr) : Stmt :=
  .ecm (maxDepositModule resultVar) [vault, receiver]

/-- Read-only ERC-4626 `maxMint(address)` module.

    It ABI-encodes the canonical `maxMint(address)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, receiver]`. -/
def maxMintModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "maxMint"
    "erc4626_maxMint_interface"
    resultVar
    0xc63d75b6
    ["receiver"]

/-- Convenience: create a `Stmt.ecm` for a read-only `maxMint(address)` call.
    -/
def maxMint (resultVar : String) (vault receiver : Expr) : Stmt :=
  .ecm (maxMintModule resultVar) [vault, receiver]

/-- Read-only ERC-4626 `maxWithdraw(address)` module.

    It ABI-encodes the canonical `maxWithdraw(address)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, owner]`. -/
def maxWithdrawModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "maxWithdraw"
    "erc4626_maxWithdraw_interface"
    resultVar
    0xce96cb77
    ["owner"]

/-- Convenience: create a `Stmt.ecm` for a read-only `maxWithdraw(address)`
    call. -/
def maxWithdraw (resultVar : String) (vault owner : Expr) : Stmt :=
  .ecm (maxWithdrawModule resultVar) [vault, owner]

/-- Read-only ERC-4626 `maxRedeem(address)` module.

    It ABI-encodes the canonical `maxRedeem(address)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[vault, owner]`. -/
def maxRedeemModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "maxRedeem"
    "erc4626_maxRedeem_interface"
    resultVar
    0xd905777e
    ["owner"]

/-- Convenience: create a `Stmt.ecm` for a read-only `maxRedeem(address)`
    call. -/
def maxRedeem (resultVar : String) (vault owner : Expr) : Stmt :=
  .ecm (maxRedeemModule resultVar) [vault, owner]

end Compiler.Modules.ERC4626
