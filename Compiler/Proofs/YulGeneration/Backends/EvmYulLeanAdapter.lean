import Compiler.Yul.Ast
import EvmYul.Yul.Ast

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul

abbrev AdapterError := String

def lowerExpr : YulExpr → EvmYul.Yul.Ast.Expr
  | .lit n => .Lit (EvmYul.UInt256.ofNat n)
  | .hex n => .Lit (EvmYul.UInt256.ofNat n)
  | .str s => .Var s
  | .ident name => .Var name
  | .call func args => .Call (.inr func) (args.map lowerExpr)

partial def lowerStmts : List YulStmt → Except AdapterError (List EvmYul.Yul.Ast.Stmt)
  | [] => pure []
  | stmt :: rest => do
      let stmt' ← lowerStmt stmt
      let rest' ← lowerStmts rest
      pure (stmt' :: rest')

partial def lowerStmt : YulStmt → Except AdapterError EvmYul.Yul.Ast.Stmt
  | .comment _ => pure (.Block [])
  | .let_ name value => pure (.Let [name] (some (lowerExpr value)))
  | .assign _ _ =>
      .error "adapter gap: assignment lowering not implemented"
  | .expr e => pure (.ExprStmtCall (lowerExpr e))
  | .if_ cond body => do
      let body' ← lowerStmts body
      pure (.If (lowerExpr cond) body')
  | .for_ init cond post body => do
      if init != [] then
        .error "adapter gap: for-loop init lowering not implemented"
      else
        let post' ← lowerStmts post
        let body' ← lowerStmts body
        pure (.For (lowerExpr cond) post' body')
  | .switch expr cases default => do
      let lowerCase := fun (tag, block : Nat × List YulStmt) => do
        let block' ← lowerStmts block
        pure (EvmYul.UInt256.ofNat tag, block')
      let cases' ← cases.mapM lowerCase
      let default' ← lowerStmts (default.getD [])
      pure (.Switch (lowerExpr expr) cases' default')
  | .block stmts => do
      let stmts' ← lowerStmts stmts
      pure (.Block stmts')
  | .funcDef _ _ _ _ =>
      .error "adapter gap: function definition lowering not implemented"

def lowerProgram (stmts : List YulStmt) : Except AdapterError EvmYul.Yul.Ast.Stmt := do
  let stmts' ← lowerStmts stmts
  pure (.Block stmts')

/--
Compile-only seam for the EVMYulLean backend in issue #294.
Behavior remains unchanged because runtime interpreters still default to the
existing Verity builtin semantics path.
-/
def evalBuiltinCallViaEvmYulLean
    (_storage : Nat → Nat)
    (_mappings : Nat → Nat → Nat)
    (_sender : Nat)
    (_selector : Nat)
    (_calldata : List Nat)
    (_func : String)
    (_argVals : List Nat) : Option Nat :=
  none

end Compiler.Proofs.YulGeneration.Backends
