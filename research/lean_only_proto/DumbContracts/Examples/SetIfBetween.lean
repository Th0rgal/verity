import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot only if it is strictly between min and max. -/

def setIfBetweenFun : Fun :=
  { name := "setIfBetween"
    args := ["slot", "value", "min", "max"]
    body :=
      requireBetween
        (v "value")
        (v "min")
        (v "max")
        (sstoreVar "slot" (v "value"))
    ret := none }

def setIfBetweenSpecR (slot value min max : Nat) : SpecR Store :=
  { requires := fun _ => value > min ∧ value < max
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value <= min ∨ value >= max }

theorem setIfBetween_meets_specR_ok (s : Store) (slot value min max : Nat) :
    (setIfBetweenSpecR slot value min max).requires s ->
    (match execFun setIfBetweenFun [slot, value, min, max] s [] with
      | ExecResult.ok _ s' => (setIfBetweenSpecR slot value min max).ensures s s'
      | _ => False) := by
  intro hreq
  rcases hreq with ⟨hgt, hlt⟩
  simp [setIfBetweenSpecR, setIfBetweenFun, requireBetween, requireAnd, require, sstoreVar, v, execFun,
    execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hgt, hlt]

theorem setIfBetween_meets_specR_reverts (s : Store) (slot value min max : Nat) :
    (setIfBetweenSpecR slot value min max).reverts s ->
    execFun setIfBetweenFun [slot, value, min, max] s [] = ExecResult.reverted := by
  intro hrev
  rcases hrev with hle | hge
  · have hnot : ¬ value > min := by
      exact Nat.not_lt.mpr hle
    simp [setIfBetweenSpecR, setIfBetweenFun, requireBetween, requireAnd, require, sstoreVar, v, execFun,
      execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]
  · by_cases hgt : value > min
    · have hnotlt : ¬ value < max := by
        exact Nat.not_lt.mpr hge
      simp [setIfBetweenSpecR, setIfBetweenFun, requireBetween, requireAnd, require, sstoreVar, v,
        execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hgt, hnotlt]
    · have hnot : ¬ value > min := by
        exact hgt
      simp [setIfBetweenSpecR, setIfBetweenFun, requireBetween, requireAnd, require, sstoreVar, v,
        execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

end DumbContracts.Examples
