/-
  Compiler.Modules.ERC20: ERC-20 Token Interaction Modules

  Standard ECMs for safe ERC-20 token operations:
  - `safeTransfer`:     transfer(address,uint256)       selector 0xa9059cbb
  - `safeTransferFrom`: transferFrom(address,address,uint256) selector 0x23b872dd
  - `safeApprove`:      approve(address,uint256)        selector 0x095ea7b3
  - `balanceOf`:        balanceOf(address)              selector 0x70a08231
  - `allowance`:        allowance(address,address)      selector 0xdd62ed3e
  - `totalSupply`:      totalSupply()                   selector 0x18160ddd

  All modules handle the ERC-20 optional-bool-return pattern: if the call
  succeeds but returndatasize == 32 and the returned word is zero, the
  module reverts.  This correctly handles both standard (bool-returning)
  and non-standard (void-returning) ERC-20 tokens.

  Trust assumption: the target address implements the ERC-20 interface
  (or is a non-standard token that doesn't return a bool).
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.ERC20

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

/-- The OpenZeppelin v5 `SafeERC20FailedOperation(address)` selector,
    left-shifted into the ABI error selector word. -/
private def safeERC20FailedOperationSelectorWord : Nat :=
  0x5274afe700000000000000000000000000000000000000000000000000000000

/-- Revert with OpenZeppelin v5's `SafeERC20FailedOperation(address)` custom error. -/
private def revertSafeERC20FailedOperation (tokenExpr : YulExpr) : List YulStmt := [
  YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex safeERC20FailedOperationSelectorWord]),
  YulStmt.expr (YulExpr.call "mstore" [
    YulExpr.lit 4,
    YulExpr.call "and" [tokenExpr, YulExpr.lit Compiler.Constants.addressMask]
  ]),
  YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 36])
]

/-- Post-call guard for OpenZeppelin-style optional-bool ERC-20 operations.
    A successful call is accepted only if it returned exactly `true`, or returned
    no data and the token address has code. Failing calls are bubbled earlier. -/
private def requireOptionalBoolSuccess
    (tokenExpr returnPtr : YulExpr) : List YulStmt := [
  YulStmt.if_
    (YulExpr.call "iszero" [
      YulExpr.call "eq" [YulExpr.call "mload" [returnPtr], YulExpr.lit 1]
    ]) [
      YulStmt.if_
        (YulExpr.call "iszero" [
          YulExpr.call "and" [
            YulExpr.call "iszero" [YulExpr.call "returndatasize" []],
            YulExpr.call "gt" [YulExpr.call "extcodesize" [tokenExpr], YulExpr.lit 0]
          ]
        ])
        (revertSafeERC20FailedOperation tokenExpr)
    ]
]

/-- Shared implementation for read-only ERC-20 calls that return one
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
    let tokenExpr ← match args.head? with
      | some token => pure token
      | none => throw s!"{moduleName} expects at least 1 argument (token)"
    let argExprs := args.drop 1
    if argExprs.length = argNames.length then
      let calldataSize := 4 + argNames.length * 32
      let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
      let ptrName := s!"__{moduleName}_ptr"
      let ptrExpr := YulExpr.ident ptrName
      let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
      let storeSelector := YulStmt.expr (YulExpr.call "mstore" [
        ptrExpr,
        YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
      ])
      let storeArgs := argExprs.zipIdx.map fun (argExpr, idx) =>
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + idx * 32)],
          argExpr
        ])
      let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit freeMemoryPointer,
        YulExpr.call "add" [ptrExpr, YulExpr.lit frameSize]
      ])
      let callExpr := YulExpr.call "staticcall" [
        YulExpr.call "gas" [],
        tokenExpr,
        ptrExpr, YulExpr.lit calldataSize,
        ptrExpr, YulExpr.lit 32
      ]
      let revertOnFailure := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident s!"__{moduleName}_success"]) [
        YulStmt.let_ s!"__{moduleName}_rds" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [
          YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident s!"__{moduleName}_rds"
        ]),
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident s!"__{moduleName}_rds"])
      ]
      let requireSingleWord := YulStmt.if_ (YulExpr.call "iszero" [
        YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]
      ]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ]
      let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
      let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [ptrExpr])
      pure [bindResult, YulStmt.block (
        [loadPtr, storeSelector] ++ storeArgs ++ [advancePtr] ++
        [YulStmt.let_ s!"__{moduleName}_success" callExpr, revertOnFailure, requireSingleWord, assignResult]
      )]
    else
      throw s!"{moduleName} expects {1 + argNames.length} arguments (token, {String.intercalate ", " argNames})"

/-- ERC-20 safeTransfer module.
    Calls `transfer(address to, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, to, amount] -/
def safeTransferModule : ExternalCallModule where
  name := "safeTransfer"
  numArgs := 3
  writesState := true
  readsState := false
  axioms := ["erc20_transfer_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, toExpr, amountExpr) ← match args with
      | [t, to, a] => pure (t, to, a)
      | _ => throw "safeTransfer expects 3 arguments (token, to, amount)"
    let selectorWord := 0xa9059cbb00000000000000000000000000000000000000000000000000000000
    let optionalBoolGuard := requireOptionalBoolSuccess tokenExpr (YulExpr.ident "__st_ptr")
    pure [YulStmt.block ([
      YulStmt.let_ "__st_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident "__st_ptr", YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__st_ptr", YulExpr.lit 4], toExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__st_ptr", YulExpr.lit 36], amountExpr]),
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit freeMemoryPointer,
        YulExpr.call "and" [
          YulExpr.call "add" [
            YulExpr.call "add" [YulExpr.ident "__st_ptr", YulExpr.lit 68],
            YulExpr.lit 31
          ],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      ]),
      YulStmt.let_ "__st_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.ident "__st_ptr", YulExpr.lit 68, YulExpr.ident "__st_ptr", YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__st_success"]) [
        YulStmt.let_ "__st_rds" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__st_rds"]),
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__st_rds"])
      ]
    ] ++ optionalBoolGuard)]

/-- Convenience: create a `Stmt.ecm` for safeTransfer. -/
def safeTransfer (token to amount : Expr) : Stmt :=
  .ecm safeTransferModule [token, to, amount]

/-- ERC-20 safeTransferFrom module.
    Calls `transferFrom(address from, address to, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, from, to, amount] -/
def safeTransferFromModule : ExternalCallModule where
  name := "safeTransferFrom"
  numArgs := 4
  writesState := true
  readsState := false
  axioms := ["erc20_transferFrom_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, fromExpr, toExpr, amountExpr) ← match args with
      | [t, f, to, a] => pure (t, f, to, a)
      | _ => throw "safeTransferFrom expects 4 arguments (token, from, to, amount)"
    let selectorWord := 0x23b872dd00000000000000000000000000000000000000000000000000000000
    let optionalBoolGuard := requireOptionalBoolSuccess tokenExpr (YulExpr.ident "__stf_ptr")
    pure [YulStmt.block ([
      YulStmt.let_ "__stf_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident "__stf_ptr", YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__stf_ptr", YulExpr.lit 4], fromExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__stf_ptr", YulExpr.lit 36], toExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__stf_ptr", YulExpr.lit 68], amountExpr]),
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit freeMemoryPointer,
        YulExpr.call "and" [
          YulExpr.call "add" [
            YulExpr.call "add" [YulExpr.ident "__stf_ptr", YulExpr.lit 100],
            YulExpr.lit 31
          ],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      ]),
      YulStmt.let_ "__stf_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.ident "__stf_ptr", YulExpr.lit 100, YulExpr.ident "__stf_ptr", YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__stf_success"]) [
        YulStmt.let_ "__stf_rds" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__stf_rds"]),
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__stf_rds"])
      ]
    ] ++ optionalBoolGuard)]

/-- Convenience: create a `Stmt.ecm` for safeTransferFrom. -/
def safeTransferFrom (token fromAddr to amount : Expr) : Stmt :=
  .ecm safeTransferFromModule [token, fromAddr, to, amount]

/-- ERC-20 safeApprove module (new — demonstrates ECM extensibility).
    Calls `approve(address spender, uint256 amount)` with optional-bool-return handling.
    Arguments: [token, spender, amount] -/
def safeApproveModule : ExternalCallModule where
  name := "safeApprove"
  numArgs := 3
  writesState := true
  readsState := false
  axioms := ["erc20_approve_interface"]
  compile := fun _ctx args => do
    let (tokenExpr, spenderExpr, amountExpr) ← match args with
      | [t, s, a] => pure (t, s, a)
      | _ => throw "safeApprove expects 3 arguments (token, spender, amount)"
    let selectorWord := 0x095ea7b300000000000000000000000000000000000000000000000000000000
    let optionalBoolGuard := requireOptionalBoolSuccess tokenExpr (YulExpr.ident "__sa_ptr")
    pure [YulStmt.block ([
      YulStmt.let_ "__sa_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident "__sa_ptr", YulExpr.hex selectorWord]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__sa_ptr", YulExpr.lit 4], spenderExpr]),
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [YulExpr.ident "__sa_ptr", YulExpr.lit 36], amountExpr]),
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit freeMemoryPointer,
        YulExpr.call "and" [
          YulExpr.call "add" [
            YulExpr.call "add" [YulExpr.ident "__sa_ptr", YulExpr.lit 68],
            YulExpr.lit 31
          ],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      ]),
      YulStmt.let_ "__sa_success" (YulExpr.call "call" [
        YulExpr.call "gas" [], tokenExpr, YulExpr.lit 0,
        YulExpr.ident "__sa_ptr", YulExpr.lit 68, YulExpr.ident "__sa_ptr", YulExpr.lit 32
      ]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sa_success"]) [
        YulStmt.let_ "__sa_rds" (YulExpr.call "returndatasize" []),
        YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__sa_rds"]),
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__sa_rds"])
      ]
    ] ++ optionalBoolGuard)]

/-- Convenience: create a `Stmt.ecm` for safeApprove. -/
def safeApprove (token spender amount : Expr) : Stmt :=
  .ecm safeApproveModule [token, spender, amount]

/-- Read-only ERC-20 `balanceOf(address)` module.

    It ABI-encodes the canonical `balanceOf(address)` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[token, owner]`. -/
def balanceOfModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "balanceOf"
    "erc20_balanceOf_interface"
    resultVar
    0x70a08231
    ["owner"]

/-- Convenience: create a `Stmt.ecm` for a read-only `balanceOf(address)` call. -/
def balanceOf (resultVar : String) (token owner : Expr) : Stmt :=
  .ecm (balanceOfModule resultVar) [token, owner]

/-- Read-only ERC-20 `allowance(address,address)` module.

    It ABI-encodes the canonical `allowance(address,address)` selector,
    performs a `staticcall`, forwards revert returndata on failure, requires
    exactly one 32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[token, owner, spender]`. -/
def allowanceModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "allowance"
    "erc20_allowance_interface"
    resultVar
    0xdd62ed3e
    ["owner", "spender"]

/-- Convenience: create a `Stmt.ecm` for a read-only `allowance(address,address)` call. -/
def allowance (resultVar : String) (token owner spender : Expr) : Stmt :=
  .ecm (allowanceModule resultVar) [token, owner, spender]

/-- Read-only ERC-20 `totalSupply()` module.

    It ABI-encodes the canonical `totalSupply()` selector, performs a
    `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds that word to `resultVar`.

    Arguments passed to the module are `[token]`. -/
def totalSupplyModule (resultVar : String) : ExternalCallModule :=
  readUint256Module
    "totalSupply"
    "erc20_totalSupply_interface"
    resultVar
    0x18160ddd
    []

/-- Convenience: create a `Stmt.ecm` for a read-only `totalSupply()` call. -/
def totalSupply (resultVar : String) (token : Expr) : Stmt :=
  .ecm (totalSupplyModule resultVar) [token]

end Compiler.Modules.ERC20
