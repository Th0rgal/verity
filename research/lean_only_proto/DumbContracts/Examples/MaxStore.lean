import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Store the max of two inputs into a chosen slot. -/

def maxStoreFun : Fun :=
  { name := "maxStore"
    args := ["slot", "a", "b"]
    body :=
      Stmt.if_
        (Expr.gt (v "a") (v "b"))
        (sstoreVar "slot" (v "a"))
        (sstoreVar "slot" (v "b"))
    ret := none }

def maxStoreSpec (slot a b : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (if a > b then a else b) }

theorem maxStore_meets_spec (s : Store) (slot a b : Nat) :
    (maxStoreSpec slot a b).requires s ->
    (match execFun maxStoreFun [slot, a, b] s [] with
      | ExecResult.ok _ s' => (maxStoreSpec slot a b).ensures s s'
      | _ => False) := by
  intro _hreq
  by_cases h : a > b
  · simp [maxStoreFun, maxStoreSpec, sstoreVar, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv,
      updateEnv, updateStore, h]
  · simp [maxStoreFun, maxStoreSpec, sstoreVar, v, execFun, execStmt, evalExpr, bindArgs, emptyEnv,
      updateEnv, updateStore, h]

end DumbContracts.Examples
