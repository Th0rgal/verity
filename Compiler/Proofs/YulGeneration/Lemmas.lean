import Compiler.Codegen
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul

/-! ## Yul Runtime Lemmas

These lemmas connect the runtime codegen structure with the Yul semantics.
-/

@[simp]
theorem evalYulExpr_selectorExpr_semantics :
    ∀ state : YulState, evalYulExpr state selectorExpr = some (state.selector % selectorModulus) := by
  intro state
  -- Unfold the selector expression and reduce calldataload/shr.
  unfold selectorExpr
  simp [evalYulExpr, evalYulExprs, evalYulCall, selectorWord, selectorModulus,
    selectorShift, Nat.mul_div_right, Nat.pow_pos]

@[simp]
theorem execYulStmt_switch_match_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = some (v, body)) :
    execYulStmt state (YulStmt.switch expr cases' default) = execYulStmts state body := by
  simp [execYulStmt, execYulStmtFuel, execYulStmts, execYulStmtsFuel, hEval, hFind]

@[simp]
theorem execYulStmt_switch_miss_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = none) :
    execYulStmt state (YulStmt.switch expr cases' default) =
      (match default with
        | some body => execYulStmts state body
        | none => YulExecResult.continue state) := by
  simp [execYulStmt, execYulStmtFuel, execYulStmts, execYulStmtsFuel, hEval, hFind]

@[simp]
theorem execYulStmts_funcDef
    (state : YulState) (name : String) (args rets : List String) (body : List YulStmt)
    (rest : List YulStmt) :
    execYulStmts state (YulStmt.funcDef name args rets body :: rest) = execYulStmts state rest := by
  simp [execYulStmts, execYulStmtsFuel, execYulStmt, execYulStmtFuel]

end Compiler.Proofs.YulGeneration
