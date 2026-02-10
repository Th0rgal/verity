import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot only if it exceeds a minimum. -/

def setIfGreaterFun : Fun :=
  { name := "setIfGreater"
    args := ["slot", "value", "min"]
    body := requireGt (v "value") (v "min") (sstoreVar "slot" (v "value"))
    ret := none }

def setIfGreaterSpecR (slot value min : Nat) : SpecR Store :=
  { requires := fun _ => value > min
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value <= min }

theorem setIfGreater_meets_specR_ok (s : Store) (slot value min : Nat) :
    (setIfGreaterSpecR slot value min).requires s ->
    (match execFun setIfGreaterFun [slot, value, min] s [] with
      | ExecResult.ok _ s' => (setIfGreaterSpecR slot value min).ensures s s'
      | _ => False) := by
  intro hreq
  have hgt : value > min := by exact hreq
  simp [setIfGreaterSpecR, setIfGreaterFun, requireGt, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hgt]

theorem setIfGreater_meets_specR_reverts (s : Store) (slot value min : Nat) :
    (setIfGreaterSpecR slot value min).reverts s ->
    execFun setIfGreaterFun [slot, value, min] s [] = ExecResult.reverted := by
  intro hrev
  have hnot : ¬ value > min := by
    exact Nat.not_lt.mpr hrev
  simp [setIfGreaterSpecR, setIfGreaterFun, requireGt, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hnot]

end DumbContracts.Examples
