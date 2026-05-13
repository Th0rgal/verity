import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

-- Smoke test for verity#1849 G1 (`Expr.arrayElementDynamicMemberLength`):
-- read the `length` of a dynamic-array member nested inside a struct-array
-- element. The macro accepts `arrayLength (arrayElement txs i).proof`
-- where `proof : Array Uint256` is a dynamic member of `Transaction`, and
-- lowers through `Expr.arrayElementDynamicMemberLength` with the correct
-- head word offset (here `0` since `proof` is the first dynamic field of
-- the struct's element head).
verity_contract ArrayElementDynamicMemberLengthSmoke where
  storage

  struct Transaction where
    proof : Array Uint256,
    token : Address,
    fee : Uint256

  function proofLength (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return arrayLength (arrayElement txs idx).proof

example :
    ArrayElementDynamicMemberLengthSmoke.proofLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            0)
      ] := rfl

end Contracts.Smoke
