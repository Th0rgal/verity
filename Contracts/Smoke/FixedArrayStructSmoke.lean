import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

-- Production-shaped Unlink fixed-array smoke. This keeps the real `Proof`
-- and `Ciphertext` nested fixed-array members from unlink-xyz `Models.sol`,
-- then reads leaves after those members through the struct-array projection
-- walker. The expected offsets prove the macro ABI layout counts
-- `uint256[2]`, `uint256[2][2]`, and `uint256[3]` fields correctly.
verity_contract FixedArrayStructSmoke where
  storage

  struct Proof where
    pA : FixedArray Uint256 2,
    pB : FixedArray (FixedArray Uint256 2) 2,
    pC : FixedArray Uint256 2

  struct Ciphertext where
    ephemeralKey : Uint256,
    data : FixedArray Uint256 3

  struct Transaction where
    proof : Proof,
    circuitId : Uint256,
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    contextHash : Uint256,
    ciphertexts : Array Ciphertext

  function rootOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return (arrayElement txs idx).merkleRoot

  function nullifierCountOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).nullifierHashes

  function commitmentCountOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).newCommitments

  function ciphertextCountOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).ciphertexts

example :
    FixedArrayStructSmoke.rootOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicWord
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            9)
      ] := rfl

example :
    FixedArrayStructSmoke.nullifierCountOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            10)
      ] := rfl

example :
    FixedArrayStructSmoke.commitmentCountOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            11)
      ] := rfl

example :
    FixedArrayStructSmoke.ciphertextCountOf_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            13)
      ] := rfl

end Contracts.Smoke
