import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store a new value only if the slot matches the expected value. -/

def compareAndSwapFun : Fun :=
  { name := "compareAndSwap"
    args := ["slot", "expected", "value"]
    body :=
      Stmt.let_ "current" (sloadVar "slot")
        (requireEq (v "current") (v "expected") (sstoreVar "slot" (v "value")))
    ret := none }

def compareAndSwapSpecR (slot expected value : Nat) : SpecR Store :=
  { requires := fun s => s slot = expected
    ensures := fun s s' => s' = updateStore s slot value
    reverts := fun s => s slot != expected }

theorem compareAndSwap_meets_specR_ok (s : Store) (slot expected value : Nat) :
    (compareAndSwapSpecR slot expected value).requires s ->
    (match execFun compareAndSwapFun [slot, expected, value] s [] with
      | ExecResult.ok _ s' => (compareAndSwapSpecR slot expected value).ensures s s'
      | _ => False) := by
  intro hreq
  have hmatch : s slot = expected := by exact hreq
  simp [compareAndSwapSpecR, compareAndSwapFun, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hmatch]

theorem compareAndSwap_meets_specR_reverts (s : Store) (slot expected value : Nat) :
    (compareAndSwapSpecR slot expected value).reverts s ->
    execFun compareAndSwapFun [slot, expected, value] s [] = ExecResult.reverted := by
  intro hrev
  simp [compareAndSwapSpecR, compareAndSwapFun, requireEq, eq, require, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
