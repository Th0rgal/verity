import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Add a delta to a slot only if it is strictly between min and max. -/

def addIfBetweenFun : Fun :=
  { name := "addIfBetween"
    args := ["slot", "delta", "min", "max"]
    body :=
      requireBetween
        (v "delta")
        (v "min")
        (v "max")
        (sstoreAdd (v "slot") (v "delta"))
    ret := none }

def addIfBetweenSpecR (slot delta min max : Nat) : SpecR Store :=
  { requires := fun _ => delta > min ∧ delta < max
    ensures := fun s s' => s' = updateStore s slot (s slot + delta)
    reverts := fun _ => delta <= min ∨ delta >= max }

theorem addIfBetween_meets_specR_ok (s : Store) (slot delta min max : Nat) :
    (addIfBetweenSpecR slot delta min max).requires s ->
    (match execFun addIfBetweenFun [slot, delta, min, max] s [] with
      | ExecResult.ok _ s' => (addIfBetweenSpecR slot delta min max).ensures s s'
      | _ => False) := by
  intro hreq
  rcases hreq with ⟨hgt, hlt⟩
  simp [addIfBetweenSpecR, addIfBetweenFun, requireBetween, requireAnd, require, sstoreAdd, v, execFun,
    execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hgt, hlt]

theorem addIfBetween_meets_specR_reverts (s : Store) (slot delta min max : Nat) :
    (addIfBetweenSpecR slot delta min max).reverts s ->
    execFun addIfBetweenFun [slot, delta, min, max] s [] = ExecResult.reverted := by
  intro hrev
  rcases hrev with hle | hge
  · have hnot : ¬ delta > min := by
      exact Nat.not_lt.mpr hle
    simp [addIfBetweenSpecR, addIfBetweenFun, requireBetween, requireAnd, require, sstoreAdd, v, execFun,
      execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]
  · by_cases hgt : delta > min
    · have hnotlt : ¬ delta < max := by
        exact Nat.not_lt.mpr hge
      simp [addIfBetweenSpecR, addIfBetweenFun, requireBetween, requireAnd, require, sstoreAdd, v,
        execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hgt, hnotlt]
    · have hnot : ¬ delta > min := by
        exact hgt
      simp [addIfBetweenSpecR, addIfBetweenFun, requireBetween, requireAnd, require, sstoreAdd, v,
        execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

end DumbContracts.Examples
