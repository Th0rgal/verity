import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot only if it is non-zero and below a max. -/

def setIfNonZeroAndLessFun : Fun :=
  { name := "setIfNonZeroAndLess"
    args := ["slot", "value", "max"]
    body :=
      requireAnd
        (neq (v "value") (n 0))
        (Expr.lt (v "value") (v "max"))
        (sstoreVar "slot" (v "value"))
    ret := none }

def setIfNonZeroAndLessSpecR (slot value max : Nat) : SpecR Store :=
  { requires := fun _ => value != 0 ∧ value < max
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value = 0 ∨ value >= max }

theorem setIfNonZeroAndLess_meets_specR_ok (s : Store) (slot value max : Nat) :
    (setIfNonZeroAndLessSpecR slot value max).requires s ->
    (match execFun setIfNonZeroAndLessFun [slot, value, max] s [] with
      | ExecResult.ok _ s' => (setIfNonZeroAndLessSpecR slot value max).ensures s s'
      | _ => False) := by
  intro hreq
  rcases hreq with ⟨hnonzero, hlt⟩
  simp [setIfNonZeroAndLessSpecR, setIfNonZeroAndLessFun, requireAnd, require, neq, eq, sstoreVar,
    v, n, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnonzero, hlt]

theorem setIfNonZeroAndLess_meets_specR_reverts (s : Store) (slot value max : Nat) :
    (setIfNonZeroAndLessSpecR slot value max).reverts s ->
    execFun setIfNonZeroAndLessFun [slot, value, max] s [] = ExecResult.reverted := by
  intro hrev
  rcases hrev with hzero | hge
  · simp [setIfNonZeroAndLessSpecR, setIfNonZeroAndLessFun, requireAnd, require, neq, eq, sstoreVar,
      v, n, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hzero]
  · by_cases hnonzero : value != 0
    · have hnotlt : ¬ value < max := by
        exact Nat.not_lt.mpr hge
      simp [setIfNonZeroAndLessSpecR, setIfNonZeroAndLessFun, requireAnd, require, neq, eq, sstoreVar,
        v, n, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnonzero, hnotlt]
    · have hnot : ¬ value != 0 := by
        exact hnonzero
      simp [setIfNonZeroAndLessSpecR, setIfNonZeroAndLessFun, requireAnd, require, neq, eq, sstoreVar,
        v, n, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

end DumbContracts.Examples
