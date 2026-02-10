import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot only if it is below a maximum. -/

def setIfLessFun : Fun :=
  { name := "setIfLess"
    args := ["slot", "value", "max"]
    body := requireLt (v "value") (v "max") (sstoreVar "slot" (v "value"))
    ret := none }

def setIfLessSpecR (slot value max : Nat) : SpecR Store :=
  { requires := fun _ => value < max
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value >= max }

theorem setIfLess_meets_specR_ok (s : Store) (slot value max : Nat) :
    (setIfLessSpecR slot value max).requires s ->
    (match execFun setIfLessFun [slot, value, max] s [] with
      | ExecResult.ok _ s' => (setIfLessSpecR slot value max).ensures s s'
      | _ => False) := by
  intro hreq
  have hlt : value < max := by exact hreq
  simp [setIfLessSpecR, setIfLessFun, requireLt, require, sstoreVar, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hlt]

theorem setIfLess_meets_specR_reverts (s : Store) (slot value max : Nat) :
    (setIfLessSpecR slot value max).reverts s ->
    execFun setIfLessFun [slot, value, max] s [] = ExecResult.reverted := by
  intro hrev
  have hnot : ¬ value < max := by
    exact Nat.not_lt.mpr hrev
  simp [setIfLessSpecR, setIfLessFun, requireLt, require, sstoreVar, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

end DumbContracts.Examples
