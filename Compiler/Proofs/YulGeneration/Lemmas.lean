import Compiler.Codegen
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul

/-! ## Yul Runtime Lemmas

These lemmas connect the runtime codegen structure with the Yul semantics.
-/

set_option maxHeartbeats 1000000 in
@[simp] theorem evalYulExpr_selectorExpr_semantics :
    ∀ state : YulState, evalYulExpr state selectorExpr = some (state.selector % selectorModulus) := by
  intro state
  -- Unfold the selector expression and reduce calldataload/shr.
  unfold selectorExpr
  have hpow : 0 < (2 ^ selectorShift) := by
    simpa using (Nat.pow_pos (a := 2) (n := selectorShift) (by decide : 0 < (2 : Nat)))
  simp [evalYulExpr, evalYulExprs]
  unfold evalYulCall
  simp [evalYulExprs, evalYulExpr, selectorWord, selectorModulus,
    selectorShift, Nat.mul_div_right, hpow]

@[simp]
theorem execYulStmtFuel_switch_match_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (fuel v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = some (v, body)) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      execYulStmtsFuel fuel state body := by
  have hFind' : List.find? (fun (c, _) => decide (c = v)) cases' = some (v, body) := by
    simpa using hFind
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, hEval]
      simp [execYulStmtsFuel, hFind']
  | succ fuel =>
      simp [execYulStmtFuel, hEval]
      simp [execYulStmtsFuel, hFind']

@[simp]
theorem execYulStmtFuel_switch_miss_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (fuel v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = none) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      (match default with
        | some body => execYulStmtsFuel fuel state body
        | none => YulExecResult.continue state) := by
  have hFind' : List.find? (fun (c, _) => decide (c = v)) cases' = none := by
    simpa using hFind
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, hEval]
      simp [execYulStmtsFuel, hFind']
  | succ fuel =>
      simp [execYulStmtFuel, hEval]
      simp [execYulStmtsFuel, hFind']

end Compiler.Proofs.YulGeneration
