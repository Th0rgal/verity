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
  -- Evaluate the call arguments explicitly to avoid simp issues with match equations.
  have hCalldata :
      evalYulExpr state (YulExpr.call "calldataload" [YulExpr.lit 0]) =
        some (selectorWord state.selector) := by
    simp [evalYulExpr, evalYulCall, evalYulExprs, selectorWord]
  have hArgs :
      evalYulExprs state
          [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]] =
        some [selectorShift, selectorWord state.selector] := by
    simp [evalYulExprs, evalYulExpr, hCalldata]
  -- Now discharge the "shr" call with the computed arguments.
  have hShr :
      (evalYulExprs state
          [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]]).bind
        (fun argVals =>
          match argVals with
          | [shift, value] => some (value / 2 ^ shift)
          | _ => none) =
        some ((selectorWord state.selector) / (2 ^ selectorShift)) := by
    simp [hArgs]
  -- Normalize selectorWord to the 4-byte selector.
  simpa [selectorExpr, evalYulExpr, evalYulCall, selectorWord,
    selectorModulus, selectorShift, Nat.mul_div_right, hpow] using hShr

@[simp]
theorem execYulStmtFuel_switch_match_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (fuel v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun x : Nat × List YulStmt => decide (x.1 = v)) cases' = some (v, body)) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      execYulStmtsFuel fuel state body := by
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]
  | succ fuel =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]

@[simp]
theorem execYulStmtFuel_switch_miss_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (default : Option (List YulStmt)) (fuel v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun x : Nat × List YulStmt => decide (x.1 = v)) cases' = none) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      (match default with
        | some body => execYulStmtsFuel fuel state body
        | none => YulExecResult.continue state) := by
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]
      rfl
  | succ fuel =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]
      rfl

end Compiler.Proofs.YulGeneration
