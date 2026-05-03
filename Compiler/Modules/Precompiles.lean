/-
  Compiler.Modules.Precompiles: EVM Precompile Modules

  Standard ECMs for EVM precompile calls:
  - `ecrecover`: ECDSA signature recovery via precompile at address 0x01
  - `sha256Memory`: SHA-256 over an existing memory slice via precompile 0x02

  Trust assumption: EVM precompiles behave according to the Ethereum
  Yellow Paper specification.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Precompiles

open Compiler.Yul
open Compiler.ECM
open Compiler.Constants (addressMask)
open Compiler.CompilationModel (Stmt Expr)

/-- Ecrecover precompile module.
    Performs ECDSA recovery via staticcall to precompile address 0x01.
    Arguments: [hash, v, r, s]
    Binds one result variable (the recovered address, masked to 160 bits).
    Guards against stale hash when the precompile returns 0 bytes. -/
def ecrecoverModule (resultVar : String) : ExternalCallModule where
  name := "ecrecover"
  numArgs := 4
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_ecrecover_precompile"]
  compile := fun _ctx args => do
    let (hashExpr, vExpr, rExpr, sExpr) ← match args with
      | [h, v, r, s] => pure (h, v, r, s)
      | _ => throw "ecrecover expects 4 arguments (hash, v, r, s)"
    let storeHash := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, hashExpr])
    let storeV := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, vExpr])
    let storeR := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 64, rExpr])
    let storeS := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 96, sExpr])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 1,
      YulExpr.lit 0, YulExpr.lit 128,
      YulExpr.lit 0, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecr_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let guardStale := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "returndatasize" []]) [
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar
      (YulExpr.call "and" [YulExpr.call "mload" [YulExpr.lit 0], YulExpr.hex addressMask])
    pure [YulStmt.block (
      [storeHash, storeV, storeR, storeS,
       YulStmt.let_ "__ecr_success" callExpr,
       revertBlock,
       guardStale]
    ), bindResult]

/-- Convenience: create a `Stmt.ecm` for ecrecover. -/
def ecrecover (resultVar : String) (hash v r s : Expr) : Stmt :=
  .ecm (ecrecoverModule resultVar) [hash, v, r, s]

/-- SHA-256 precompile over an existing memory slice.
    Arguments: [inputOffset, inputSize, outputOffset]
    Binds one result variable to `mload(outputOffset)`.
    Reverts if precompile 0x02 reports failure. -/
def sha256MemoryModule (resultVar : String) : ExternalCallModule where
  name := "sha256Memory"
  numArgs := 3
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_sha256_precompile"]
  compile := fun _ctx args => do
    let (inputOffset, inputSize, outputOffset) ← match args with
      | [inputOffset, inputSize, outputOffset] => pure (inputOffset, inputSize, outputOffset)
      | _ => throw "sha256Memory expects 3 arguments (inputOffset, inputSize, outputOffset)"
    let outputOffsetTemp := YulExpr.ident "__sha256_output_offset"
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 2,
      inputOffset, inputSize,
      outputOffsetTemp, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sha256_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.call "mload" [outputOffsetTemp])
    pure [
      YulStmt.let_ "__sha256_output_offset" outputOffset,
      YulStmt.let_ "__sha256_success" callExpr,
      revertBlock,
      bindResult
    ]

/-- Convenience: create a `Stmt.ecm` for SHA-256 over memory. -/
def sha256Memory (resultVar : String) (inputOffset inputSize outputOffset : Expr) : Stmt :=
  .ecm (sha256MemoryModule resultVar) [inputOffset, inputSize, outputOffset]

/-- Short alias for SHA-256 over an existing memory slice. -/
def sha256 (resultVar : String) (inputOffset inputSize outputOffset : Expr) : Stmt :=
  sha256Memory resultVar inputOffset inputSize outputOffset

end Compiler.Modules.Precompiles
