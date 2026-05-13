import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

-- Regression test for verity#1847: Mathlib-reserved short identifiers
-- (`to`, `from`, `at`, ...) can be used as `verity_contract` parameter
-- binders and references via Lean's `«…»` raw-identifier escape, even
-- after Mathlib pulls them in as syntax tokens. The compiled
-- CompilationModel preserves the underlying name without guillemets, so
-- ABI and audit reports stay consistent with the Solidity-faithful name.
verity_contract MathlibReservedBinderEscape where
  storage
    balances : Address → Uint256 := slot 0

  function transferLike («to» : Address, amount : Uint256) : Uint256 := do
    let current ← getMapping balances «to»
    setMapping balances «to» (add current amount)
    return amount

  function transferLikeFrom («from» : Address, «to» : Address, amount : Uint256) : Uint256 := do
    let srcBal ← getMapping balances «from»
    setMapping balances «from» (sub srcBal amount)
    let dstBal ← getMapping balances «to»
    setMapping balances «to» (add dstBal amount)
    return amount

example :
    MathlibReservedBinderEscape.transferLike_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "current"
          (Compiler.CompilationModel.Expr.mapping "balances" (Compiler.CompilationModel.Expr.param "to"))
      , Compiler.CompilationModel.Stmt.setMapping "balances"
          (Compiler.CompilationModel.Expr.param "to")
          (Compiler.CompilationModel.Expr.add
            (Compiler.CompilationModel.Expr.localVar "current")
            (Compiler.CompilationModel.Expr.param "amount"))
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.param "amount")
      ] := rfl

example :
    MathlibReservedBinderEscape.transferLikeFrom_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "srcBal"
          (Compiler.CompilationModel.Expr.mapping "balances" (Compiler.CompilationModel.Expr.param "from"))
      , Compiler.CompilationModel.Stmt.setMapping "balances"
          (Compiler.CompilationModel.Expr.param "from")
          (Compiler.CompilationModel.Expr.sub
            (Compiler.CompilationModel.Expr.localVar "srcBal")
            (Compiler.CompilationModel.Expr.param "amount"))
      , Compiler.CompilationModel.Stmt.letVar "dstBal"
          (Compiler.CompilationModel.Expr.mapping "balances" (Compiler.CompilationModel.Expr.param "to"))
      , Compiler.CompilationModel.Stmt.setMapping "balances"
          (Compiler.CompilationModel.Expr.param "to")
          (Compiler.CompilationModel.Expr.add
            (Compiler.CompilationModel.Expr.localVar "dstBal")
            (Compiler.CompilationModel.Expr.param "amount"))
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.param "amount")
      ] := rfl

end Contracts.Smoke
