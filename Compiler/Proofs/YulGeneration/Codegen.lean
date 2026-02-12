import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Proofs.YulGeneration.Lemmas

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Codegen Proof Obligations (Layer 3)

These lemmas capture the core obligations for Yul codegen correctness:
1. Selector extraction matches the function selector.
2. Runtime switch dispatch executes the selected function body.
-/-

/-- Selector expression used by the runtime switch. -/
def selectorExpr : YulExpr :=
  YulExpr.call "shr" [
    YulExpr.lit selectorShift,
    YulExpr.call "calldataload" [YulExpr.lit 0]
  ]

@[simp]
theorem emitYul_runtimeCode_eq (contract : IRContract) :
    (Compiler.emitYul contract).runtimeCode = Compiler.runtimeCode contract := by
  rfl

/-- Selector extraction via `selectorExpr` yields the 4-byte selector. -/
@[simp]
theorem evalYulExpr_selectorExpr (state : YulState) :
    evalYulExpr state selectorExpr = some (state.selector % selectorModulus) := by
  simp [selectorExpr]

/-- Executing runtime code is equivalent to executing the switch body (mapping helper is a no-op). -/
theorem execYulStmts_runtimeCode_eq (contract : IRContract) (state : YulState) :
    execYulStmts state (Compiler.runtimeCode contract) =
      execYulStmts state [Compiler.buildSwitch contract.functions] := by
  by_cases h : contract.usesMapping
  · simp [Compiler.runtimeCode, h, execYulStmts, execYulStmt]
  · simp [Compiler.runtimeCode, h]

/-- If the selector matches a case, the switch executes that case body. -/
theorem execYulStmt_switch_match
    (state : YulState) (expr : YulExpr) (cases : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : cases.find? (fun (c, _) => c = v) = some (v, body)) :
    execYulStmt state (YulStmt.switch expr cases default) =
      execYulStmts state body := by
  simp [execYulStmt, hEval, hFind]

/-- If no selector case matches, the switch executes the default (or continues). -/
theorem execYulStmt_switch_miss
    (state : YulState) (expr : YulExpr) (cases : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : cases.find? (fun (c, _) => c = v) = none) :
    execYulStmt state (YulStmt.switch expr cases default) =
      match default with
      | some body => execYulStmts state body
      | none => YulExecResult.continue state := by
  simp [execYulStmt, hEval, hFind]

/-- Bridge lemma: mapping a found function into switch cases yields the corresponding case. -/
lemma find_switch_case_of_find_function
    (fns : List IRFunction) (sel : Nat) (fn : IRFunction)
    (hFind : fns.find? (fun f => f.selector == sel) = some fn) :
    (fns.map (fun f =>
      let body := [YulStmt.comment s!"{f.name}()"] ++ f.body
      (f.selector, body)
    )).find? (fun (c, _) => c = sel) =
      some (fn.selector, [YulStmt.comment s!"{fn.name}()"] ++ fn.body) := by
  induction fns with
  | nil =>
      simp at hFind
  | cons f rest ih =>
      simp [List.find?] at hFind
      by_cases hsel : f.selector == sel
      · simp [List.find?, hsel] at hFind
        cases hFind
        simp [List.find?, hsel]
      · simp [List.find?, hsel] at hFind
        have := ih hFind
        simp [List.find?, hsel, this]

end Compiler.Proofs.YulGeneration
