import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind

verity_contract ArrayElementDynamicMemberElementSmoke where
  storage

  struct Transaction where
    proof : Array Uint256,
    token : Address,
    fee : Uint256

  function proofAt (txs : Array Transaction, idx : Uint256, k : Uint256) : Uint256 := do
    return arrayElement (arrayElement txs idx).proof k

example :
    ArrayElementDynamicMemberElementSmoke.proofAt_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicMemberElement
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            0
            (Compiler.CompilationModel.Expr.param "k"))
      ] := rfl

end Contracts.Smoke
