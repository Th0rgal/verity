import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Initialize a slot to 1 if it is currently zero. -/

def initToOneFun : Fun :=
  { name := "initToOne"
    args := ["slot"]
    body :=
      letSload "current" (v "slot")
        (requireZero (v "current") (sstoreVar "slot" (n 1)))
    ret := none }

def initToOneSpecR (slot : Nat) : SpecR Store :=
  { requires := fun s => s slot = 0
    ensures := fun s s' => s' = updateStore s slot 1
    reverts := fun s => s slot != 0 }

theorem initToOne_meets_specR_ok (s : Store) (slot : Nat) :
    (initToOneSpecR slot).requires s ->
    (match execFun initToOneFun [slot] s [] with
      | ExecResult.ok _ s' => (initToOneSpecR slot).ensures s s'
      | _ => False) := by
  intro hreq
  have hzero : s slot = 0 := by exact hreq
  simp [initToOneSpecR, initToOneFun, letSload, requireZero, requireEq, eq, require, execFun,
    execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hzero]

theorem initToOne_meets_specR_reverts (s : Store) (slot : Nat) :
    (initToOneSpecR slot).reverts s ->
    execFun initToOneFun [slot] s [] = ExecResult.reverted := by
  intro hrev
  simp [initToOneSpecR, initToOneFun, letSload, requireZero, requireEq, eq, require, execFun,
    execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
