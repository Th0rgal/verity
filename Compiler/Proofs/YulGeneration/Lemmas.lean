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
  have hShiftModEq : selectorShift % evmModulus = selectorShift := by
    have hShiftLtModulus : selectorShift < evmModulus := by
      norm_num [selectorShift, evmModulus]
    exact Nat.mod_eq_of_lt hShiftLtModulus
  have hSelectorShiftLt256 : selectorShift < 256 := by
    norm_num [selectorShift]
  have hSelectorShiftNotGe256 : ¬ 256 ≤ selectorShift := Nat.not_le_of_lt hSelectorShiftLt256
  have hSelectorWordLt :
      (state.selector % selectorModulus) * 2 ^ selectorShift < evmModulus := by
    have hModLt : state.selector % selectorModulus < selectorModulus := by
      exact Nat.mod_lt _ (by decide)
    have hPowPos : 0 < 2 ^ selectorShift := by
      exact Nat.pow_pos (a := 2) (n := selectorShift) (by decide)
    have hMulLt :
        (state.selector % selectorModulus) * 2 ^ selectorShift <
          selectorModulus * 2 ^ selectorShift := by
      exact Nat.mul_lt_mul_of_pos_right hModLt hPowPos
    have hModulusSplit : selectorModulus * 2 ^ selectorShift = evmModulus := by
      norm_num [selectorModulus, selectorShift, evmModulus, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc]
    simpa [hModulusSplit] using hMulLt
  have hSelectorWordMod :
      ((state.selector % selectorModulus) * 2 ^ selectorShift) % evmModulus =
        (state.selector % selectorModulus) * 2 ^ selectorShift := by
    exact Nat.mod_eq_of_lt hSelectorWordLt
  simp [selectorExpr, evalYulExpr, evalYulCall, evalYulExprs,
    evalBuiltinCallWithBackend, evalBuiltinCall, calldataloadWord, selectorWord,
    hShiftModEq, hSelectorWordMod, hSelectorShiftNotGe256]

@[simp]
theorem execYulStmtFuel_switch_match_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (defaultCase : Option (List YulStmt)) (fuel v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun x : Nat × List YulStmt => decide (x.1 = v)) cases' = some (v, body)) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' defaultCase) =
      execYulStmtsFuel fuel state body := by
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]
  | succ fuel =>
      simp [execYulStmtFuel, execYulStmtsFuel, execYulFuel, hEval, hFind]

@[simp]
theorem execYulStmtFuel_switch_miss_semantics
    (state : YulState) (expr : YulExpr) (cases' : List (Nat × List YulStmt))
    (defaultCase : Option (List YulStmt)) (fuel v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun x : Nat × List YulStmt => decide (x.1 = v)) cases' = none) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' defaultCase) =
      (match defaultCase with
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
