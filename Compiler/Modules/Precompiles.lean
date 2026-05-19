/-
  Compiler.Modules.Precompiles: EVM Precompile Modules

  Standard ECMs for EVM precompile calls:
  - `ecrecover`: ECDSA signature recovery via precompile at address 0x01
  - `sha256Memory`: SHA-256 over an existing memory slice via precompile 0x02
  - `bn256Add`: BN254 (alt_bn128) point addition via precompile 0x06
  - `bn256ScalarMul`: BN254 scalar multiplication via precompile 0x07
  - `bn256Pairing`: BN254 optimal-Ate pairing check via precompile 0x08

  Trust assumption: EVM precompiles behave according to the Ethereum
  Yellow Paper specification (EIP-196 and EIP-197 for the BN254 curve
  precompiles introduced in the Byzantium hard fork).
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Precompiles

open Compiler.Yul
open Compiler.ECM
open Compiler.Constants (addressMask)
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

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
    let ptrName := "__ecr_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let storeHash := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, hashExpr])
    let storeV := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 32], vExpr])
    let storeR := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 64], rExpr])
    let storeS := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 96], sExpr])
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit 128]
    ])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 1,
      ptrExpr, YulExpr.lit 128,
      ptrExpr, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecr_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let guardStale := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.call "returndatasize" []]) [
      YulStmt.expr (YulExpr.call "mstore" [ptrExpr, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar
      (YulExpr.call "and" [YulExpr.call "mload" [ptrExpr], YulExpr.hex addressMask])
    pure [bindResult, YulStmt.block (
      [loadPtr, storeHash, storeV, storeR, storeS, advancePtr,
       YulStmt.let_ "__ecr_success" callExpr,
       revertBlock,
       guardStale,
       assignResult]
    )]

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
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [outputOffsetTemp])
    pure [
      bindResult,
      YulStmt.block [
        YulStmt.let_ "__sha256_output_offset" outputOffset,
        YulStmt.let_ "__sha256_success" callExpr,
        revertBlock,
        assignResult
      ]
    ]

/-- Convenience: create a `Stmt.ecm` for SHA-256 over memory. -/
def sha256Memory (resultVar : String) (inputOffset inputSize outputOffset : Expr) : Stmt :=
  .ecm (sha256MemoryModule resultVar) [inputOffset, inputSize, outputOffset]

/-- Short alias for SHA-256 over an existing memory slice. -/
def sha256 (resultVar : String) (inputOffset inputSize outputOffset : Expr) : Stmt :=
  sha256Memory resultVar inputOffset inputSize outputOffset

/-! ### BN254 (alt_bn128) curve precompiles (EIP-196 / EIP-197).

These precompiles operate on the BN254 elliptic curve used by zkSNARK
verifiers.  Inputs and outputs are encoded as 256-bit big-endian words
in the standard EVM precompile layout.  All three precompiles revert on
invalid inputs (point not on curve, non-canonical field element, etc.);
we surface that as a regular revert from the convenience module.

Trust assumption (single axiom per precompile): the EVM implementation
of the precompile matches the Yellow Paper / EIP semantics. -/

/-- BN254 point addition via precompile 0x06 (EIP-196).
    Arguments: [x1, y1, x2, y2] — the affine coordinates of the two
    input points.  Binds two result variables `(resultXVar, resultYVar)`
    to the affine coordinates of the sum.  The infinity point is encoded
    as `(0, 0)` in both inputs and outputs, matching the EIP-196 spec.
    Reverts if the precompile call fails (e.g. malformed point). -/
def bn256AddModule (resultXVar resultYVar : String) : ExternalCallModule where
  name := "bn256Add"
  numArgs := 4
  resultVars := [resultXVar, resultYVar]
  writesState := false
  readsState := true
  axioms := ["evm_bn256_add_precompile"]
  compile := fun _ctx args => do
    let (x1, y1, x2, y2) ← match args with
      | [x1, y1, x2, y2] => pure (x1, y1, x2, y2)
      | _ => throw "bn256Add expects 4 arguments (x1, y1, x2, y2)"
    let ptrName := "__bn256_add_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let storeX1 := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, x1])
    let storeY1 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 32], y1])
    let storeX2 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 64], x2])
    let storeY2 := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 96], y2])
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit 128]
    ])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 6,
      ptrExpr, YulExpr.lit 128,
      ptrExpr, YulExpr.lit 64
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__bn256_add_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindX := YulStmt.let_ resultXVar (YulExpr.lit 0)
    let bindY := YulStmt.let_ resultYVar (YulExpr.lit 0)
    let assignX := YulStmt.assign resultXVar (YulExpr.call "mload" [ptrExpr])
    let assignY := YulStmt.assign resultYVar (YulExpr.call "mload" [YulExpr.call "add" [ptrExpr, YulExpr.lit 32]])
    pure [
      bindX,
      bindY,
      YulStmt.block [
        loadPtr, storeX1, storeY1, storeX2, storeY2, advancePtr,
        YulStmt.let_ "__bn256_add_success" callExpr,
        revertBlock,
        assignX, assignY
      ]
    ]

/-- Convenience: create a `Stmt.ecm` for BN254 point addition. -/
def bn256Add (resultXVar resultYVar : String) (x1 y1 x2 y2 : Expr) : Stmt :=
  .ecm (bn256AddModule resultXVar resultYVar) [x1, y1, x2, y2]

/-- BN254 scalar multiplication via precompile 0x07 (EIP-196).
    Arguments: [x, y, scalar] — the affine coordinates of the input point
    and a 256-bit scalar.  Binds two result variables to the affine
    coordinates of `scalar * (x, y)`.  Reverts on precompile failure. -/
def bn256ScalarMulModule (resultXVar resultYVar : String) : ExternalCallModule where
  name := "bn256ScalarMul"
  numArgs := 3
  resultVars := [resultXVar, resultYVar]
  writesState := false
  readsState := true
  axioms := ["evm_bn256_scalar_mul_precompile"]
  compile := fun _ctx args => do
    let (x, y, scalar) ← match args with
      | [x, y, s] => pure (x, y, s)
      | _ => throw "bn256ScalarMul expects 3 arguments (x, y, scalar)"
    let ptrName := "__bn256_mul_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let storeX := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, x])
    let storeY := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 32], y])
    let storeS := YulStmt.expr (YulExpr.call "mstore" [YulExpr.call "add" [ptrExpr, YulExpr.lit 64], scalar])
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit 96]
    ])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 7,
      ptrExpr, YulExpr.lit 96,
      ptrExpr, YulExpr.lit 64
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__bn256_mul_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindX := YulStmt.let_ resultXVar (YulExpr.lit 0)
    let bindY := YulStmt.let_ resultYVar (YulExpr.lit 0)
    let assignX := YulStmt.assign resultXVar (YulExpr.call "mload" [ptrExpr])
    let assignY := YulStmt.assign resultYVar (YulExpr.call "mload" [YulExpr.call "add" [ptrExpr, YulExpr.lit 32]])
    pure [
      bindX,
      bindY,
      YulStmt.block [
        loadPtr, storeX, storeY, storeS, advancePtr,
        YulStmt.let_ "__bn256_mul_success" callExpr,
        revertBlock,
        assignX, assignY
      ]
    ]

/-- Convenience: create a `Stmt.ecm` for BN254 scalar multiplication. -/
def bn256ScalarMul (resultXVar resultYVar : String) (x y scalar : Expr) : Stmt :=
  .ecm (bn256ScalarMulModule resultXVar resultYVar) [x, y, scalar]

/-- BN254 optimal-Ate pairing check via precompile 0x08 (EIP-197).
    Arguments: [inputOffset, inputSize, outputOffset].  The input region
    must contain `k` pairs of (G1, G2) points encoded as 192 bytes each
    (so `inputSize = 192 * k`).  The output is a single 32-byte word:
    `1` if the product of the pairings equals the identity, `0` otherwise.
    Binds the boolean-typed word from the output to the result variable.
    Reverts if the precompile call fails (invalid input size, off-curve point,
    etc.). -/
def bn256PairingModule (resultVar : String) : ExternalCallModule where
  name := "bn256Pairing"
  numArgs := 3
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_bn256_pairing_precompile"]
  compile := fun _ctx args => do
    let (inputOffset, inputSize, outputOffset) ← match args with
      | [a, b, c] => pure (a, b, c)
      | _ => throw "bn256Pairing expects 3 arguments (inputOffset, inputSize, outputOffset)"
    let outputOffsetTemp := YulExpr.ident "__bn256_pairing_output_offset"
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 8,
      inputOffset, inputSize,
      outputOffsetTemp, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__bn256_pairing_success"]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [outputOffsetTemp])
    pure [
      bindResult,
      YulStmt.block [
        YulStmt.let_ "__bn256_pairing_output_offset" outputOffset,
        YulStmt.let_ "__bn256_pairing_success" callExpr,
        revertBlock,
        assignResult
      ]
    ]

/-- Convenience: create a `Stmt.ecm` for the BN254 pairing precompile. -/
def bn256Pairing (resultVar : String) (inputOffset inputSize outputOffset : Expr) : Stmt :=
  .ecm (bn256PairingModule resultVar) [inputOffset, inputSize, outputOffset]

end Compiler.Modules.Precompiles
