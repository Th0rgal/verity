import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a value into a slot only if it meets a minimum (>=). -/

def setIfAtLeastFun : Fun :=
  { name := "setIfAtLeast"
    args := ["slot", "value", "min"]
    body := requireGte (v "value") (v "min") (sstoreVar "slot" (v "value"))
    ret := none }

def setIfAtLeastSpecR (slot value min : Nat) : SpecR Store :=
  { requires := fun _ => value >= min
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun _ => value < min }

theorem setIfAtLeast_meets_specR_ok (s : Store) (slot value min : Nat) :
    (setIfAtLeastSpecR slot value min).requires s ->
    (match execFun setIfAtLeastFun [slot, value, min] s [] with
      | ExecResult.ok _ s' => (setIfAtLeastSpecR slot value min).ensures s s'
      | _ => False) := by
  intro hreq
  have hge : value >= min := by exact hreq
  have hnot : ¬ value < min := by
    exact not_lt_of_ge hge
  simp [setIfAtLeastSpecR, setIfAtLeastFun, requireGte, require, sstoreVar, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

theorem setIfAtLeast_meets_specR_reverts (s : Store) (slot value min : Nat) :
    (setIfAtLeastSpecR slot value min).reverts s ->
    execFun setIfAtLeastFun [slot, value, min] s [] = ExecResult.reverted := by
  intro hrev
  have hlt : value < min := by exact hrev
  simp [setIfAtLeastSpecR, setIfAtLeastFun, requireGte, require, sstoreVar, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hlt]

end DumbContracts.Examples
