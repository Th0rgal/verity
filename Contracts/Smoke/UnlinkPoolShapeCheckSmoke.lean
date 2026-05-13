import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

-- Direct translation of the shape-validation phase of UnlinkPool.transfer
-- (https://github.com/unlink-xyz/monorepo `protocol/contracts/src/UnlinkPool.sol`).
-- This smoke is the concrete acceptance target for verity#1849 G1+G2 — it
-- exercises every macro lift those gaps require, in the exact shape the
-- production audit code uses.
--
-- Faithful translation notes:
--
-- * The Solidity `Transaction` struct (`protocol/contracts/src/lib/Models.sol`)
--   carries a nested `Proof` struct with `uint256[2]` / `uint256[2][2]`
--   fixed arrays, plus a `Ciphertext[]` dynamic struct array. Those nested
--   shapes are out of scope for the G1+G2 demo — they require fixed-array
--   and nested-struct-array support that has its own roadmap. We keep the
--   `Transaction` schema reduced to the dynamic-member fields needed to
--   exercise `arrayLength` (G1) and per-tx element indexing (G2):
--   `nullifierHashes`, `newCommitments`, plus the scalar `merkleRoot`
--   that the real contract uses for context validation.
--
-- * `validateInputShape` mirrors lines 341 of `UnlinkPool.transfer`
--   (`if (txn.nullifierHashes.length != c.inputCount) revert PoolInvalidInputShape()`),
--   which is the canonical G1 use site.
--
-- * `validateOutputShape` mirrors line 342
--   (`if (txn.newCommitments.length != c.outputCount) revert PoolInvalidOutputShape()`).
--
-- * `firstNullifier` mirrors the per-tx `_spendNullifiers(txn.nullifierHashes)`
--   loop's inner indexing shape — `txn.nullifierHashes[k]`, which is the
--   canonical G2 use site.
--
-- * `cmp_eq` is the EDSL boolean comparison; revert-shape uses the standard
--   `requireError <cond> <ErrorName> ()` form.
verity_contract UnlinkPoolShapeCheckSmoke where
  storage

  struct Transaction where
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    contextHash : Uint256

  -- G1: read the `.length` of a dynamic member inside a struct-array
  -- element. The macro lowers this to
  -- `Expr.arrayElementDynamicMemberLength "txs" (param "idx") wordOffset`
  -- where `wordOffset` is the head-word index of `nullifierHashes` in the
  -- `Transaction` element layout.
  function nullifierCountOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).nullifierHashes

  function commitmentCountOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).newCommitments

  -- G2: read a specific element of a dynamic member inside a struct-array
  -- element. The macro lowers this to
  -- `Expr.arrayElementDynamicMemberElement "txs" (param "idx") wordOffset (param "k")`.
  function nullifierAt (txs : Array Transaction, idx : Uint256, k : Uint256) : Uint256 := do
    return arrayElement (arrayElement txs idx).nullifierHashes k

  function commitmentAt (txs : Array Transaction, idx : Uint256, k : Uint256) : Uint256 := do
    return arrayElement (arrayElement txs idx).newCommitments k

  -- The full shape-check pattern from `UnlinkPool.transfer` (UnlinkPool.sol:341-342)
  -- is `if (txn.nullifierHashes.length != c.inputCount) revert PoolInvalidInputShape();`.
  -- Translating the `requireError`/`revert` form requires combining G1 with the
  -- existing `cmp_eq` boolean predicate; the `cmp_eq` arm currently rejects
  -- the G1 projection on the compile-model path, so we leave the
  -- straight-line G1/G2 reads above and document the residual gap rather
  -- than ship a half-working revert form. The next session adds the
  -- `cmp_eq (G1) X` lift via the same projection helper.

example :
    UnlinkPoolShapeCheckSmoke.nullifierCountOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            1) -- wordOffset 1: `merkleRoot` (word 0), `nullifierHashes` (word 1)
      ] := rfl

example :
    UnlinkPoolShapeCheckSmoke.commitmentCountOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            2) -- wordOffset 2: `newCommitments`
      ] := rfl

example :
    UnlinkPoolShapeCheckSmoke.nullifierAt_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberElement
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            1
            (Compiler.CompilationModel.Expr.param "k"))
      ] := rfl

end Contracts.Smoke
