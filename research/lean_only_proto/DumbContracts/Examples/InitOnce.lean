import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Initialize a slot once, reverting if it was already set. -/

def initOnceFun : Fun :=
  { name := "initOnce"
    args := ["slot", "value"]
    body :=
      letSload "current" (v "slot")
        (requireZero (v "current") (sstoreVar "slot" (v "value")))
    ret := none }

def initOnceSpecR (slot value : Nat) : SpecR Store :=
  { requires := fun s => s slot = 0
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun s => s slot != 0 }

theorem initOnce_meets_specR_ok (s : Store) (slot value : Nat) :
    (initOnceSpecR slot value).requires s ->
    (match execFun initOnceFun [slot, value] s [] with
      | ExecResult.ok _ s' => (initOnceSpecR slot value).ensures s s'
      | _ => False) := by
  intro hreq
  have hzero : s slot = 0 := by exact hreq
  simp [initOnceSpecR, initOnceFun, letSload, requireZero, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hzero]

theorem initOnce_meets_specR_reverts (s : Store) (slot value : Nat) :
    (initOnceSpecR slot value).reverts s ->
    execFun initOnceFun [slot, value] s [] = ExecResult.reverted := by
  intro hrev
  simp [initOnceSpecR, initOnceFun, letSload, requireZero, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
