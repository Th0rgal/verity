import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Decrement a slot by delta when the current value is large enough. -/

def subIfEnoughFun : Fun :=
  { name := "subIfEnough"
    args := ["slot", "delta"]
    body := letSload "current" (v "slot")
      (requireGte
        (v "current")
        (v "delta")
        (Stmt.sstore (v "slot") (Expr.sub (v "current") (v "delta"))))
    ret := none }

def subIfEnoughSpecR (slot delta : Nat) : SpecR Store :=
  { requires := fun s => s slot >= delta
    ensures := fun s s' => s' = updateStore s slot (s slot - delta)
    reverts := fun s => s slot < delta }

theorem subIfEnough_meets_specR_ok (s : Store) (slot delta : Nat) :
    (subIfEnoughSpecR slot delta).requires s ->
    (match execFun subIfEnoughFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (subIfEnoughSpecR slot delta).ensures s s'
      | _ => False) := by
  intro hreq
  have hge : s slot >= delta := by exact hreq
  have hnot : ¬ s slot < delta := by
    exact not_lt_of_ge hge
  simp [subIfEnoughSpecR, subIfEnoughFun, letSload, requireGte, require, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hnot]

theorem subIfEnough_meets_specR_reverts (s : Store) (slot delta : Nat) :
    (subIfEnoughSpecR slot delta).reverts s ->
    execFun subIfEnoughFun [slot, delta] s [] = ExecResult.reverted := by
  intro hrev
  have hlt : s slot < delta := by exact hrev
  simp [subIfEnoughSpecR, subIfEnoughFun, letSload, requireGte, require, v, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, hlt]

end DumbContracts.Examples
