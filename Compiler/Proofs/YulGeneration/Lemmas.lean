import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul

/-! ## Lemmas for Yul Runtime Semantics

Small, reusable facts about `calldataload` and selector extraction. These are
useful when proving that `emitYul`'s runtime dispatch matches IR semantics.
-/-

@[simp]
theorem evalYulExpr_calldataload_selector_word (state : YulState) :
    evalYulExpr state
      (YulExpr.call "calldataload" [YulExpr.lit 0]) =
      some (selectorWord state.selector) := by
  simp [evalYulExpr, evalYulCall, evalYulExprs]

@[simp]
theorem evalYulExpr_calldataload_arg (state : YulState) (i : Nat) :
    evalYulExpr state
      (YulExpr.call "calldataload" [YulExpr.lit (4 + 32 * i)]) =
      some (state.calldata.getD i 0) := by
  have hmod : (32 * i) % 32 = 0 := by
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 32 i)
  have hdiv : (32 * i) / 32 = i := by
    exact Nat.mul_div_right i (by decide : 0 < 32)
  -- Unfold and simplify calldataload for a word-aligned offset after the selector.
  simp [evalYulExpr, evalYulCall, evalYulExprs, hmod, hdiv, Nat.add_sub_cancel]

/-- Selector extraction via `shr(224, calldataload(0))` yields the 4-byte selector. -/
@[simp]
theorem evalYulExpr_selector_extract (state : YulState) :
    evalYulExpr state
      (YulExpr.call "shr" [
        YulExpr.lit selectorShift,
        YulExpr.call "calldataload" [YulExpr.lit 0]
      ]) = some ((state.selector % selectorModulus)) := by
  -- `shr` is modeled as division by 2^shift.
  -- selectorWord = (selector % 2^32) * 2^224
  have hpos : 0 < 2 ^ selectorShift := by
    -- 2^n is positive for all n
    exact Nat.pow_pos (by decide : 0 < 2) _
  simp [evalYulExpr, evalYulCall, evalYulExprs, selectorWord, selectorModulus, selectorShift,
    Nat.mul_div_right, hpos]

end Compiler.Proofs.YulGeneration
