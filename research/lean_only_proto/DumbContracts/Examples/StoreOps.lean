import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Simple storage helpers. -/

def getSlotFun : Fun :=
  { name := "getSlot"
    args := ["slot"]
    body := Stmt.return_ (Expr.sload (Expr.var "slot"))
    ret := none }

def setSlotFun : Fun :=
  { name := "setSlot"
    args := ["slot", "value"]
    body := Stmt.sstore (Expr.var "slot") (Expr.var "value")
    ret := none }

def addSlotFun : Fun :=
  { name := "addSlot"
    args := ["slot", "delta"]
    body := Stmt.sstore (Expr.var "slot") (Expr.add (Expr.sload (Expr.var "slot")) (Expr.var "delta"))
    ret := none }

def guardedAddSlotFun : Fun :=
  { name := "guardedAddSlot"
    args := ["slot", "delta"]
    body := require
      (Expr.gt (Expr.var "delta") (Expr.lit 0))
      (Stmt.sstore (Expr.var "slot")
        (Expr.add (Expr.sload (Expr.var "slot")) (Expr.var "delta")))
    ret := none }

/-- A minimal store for point examples. -/

def storeOf (k v : Nat) : Store :=
  fun x => if x = k then v else 0

-- Tests and execution facts.

theorem getSlot_returns (slot value : Nat) :
    execFun getSlotFun [slot] (storeOf slot value) [] =
      ExecResult.returned [value] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot value) := by
  simp [getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv]

theorem setSlot_updates (slot value : Nat) :
    execFun setSlotFun [slot, value] (storeOf slot 0) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "value"] [slot, value]) (storeOf slot value) := by
  simp [setSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem addSlot_updates (slot base delta : Nat) :
    execFun addSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "delta"] [slot, delta]) (storeOf slot (base + delta)) := by
  simp [addSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem set_then_get (slot value : Nat) :
    (match execFun setSlotFun [slot, value] (storeOf slot 0) [] with
      | ExecResult.ok _ store1 =>
          execFun getSlotFun [slot] store1 [] =
            ExecResult.returned [value] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot value)
      | _ => False) := by
  simp [setSlotFun, getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem add_then_get (slot base delta : Nat) :
    (match execFun addSlotFun [slot, delta] (storeOf slot base) [] with
      | ExecResult.ok _ store1 =>
          execFun getSlotFun [slot] store1 [] =
            ExecResult.returned [base + delta] (bindArgs emptyEnv ["slot"] [slot]) (storeOf slot (base + delta))
      | _ => False) := by
  simp [addSlotFun, getSlotFun, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv, updateEnv, updateStore]

theorem guarded_add_updates (slot base delta : Nat) (h : delta > 0) :
    execFun guardedAddSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.ok (bindArgs emptyEnv ["slot", "delta"] [slot, delta]) (storeOf slot (base + delta)) := by
  simp [guardedAddSlotFun, require, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv,
    updateEnv, updateStore, h]

theorem guarded_add_reverts (slot base delta : Nat) (h : delta = 0) :
    execFun guardedAddSlotFun [slot, delta] (storeOf slot base) [] =
      ExecResult.reverted := by
  simp [guardedAddSlotFun, require, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv,
    updateEnv, updateStore, h]

-- Storage specs (Store-level).

def addSlotSpec (slot delta : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' => s' = updateStore s slot (s slot + delta) }

def guardedAddSlotSpec (slot delta : Nat) : Spec Store :=
  { requires := fun _ => delta > 0
    ensures := fun s s' => s' = updateStore s slot (s slot + delta) }

def guardedAddSlotSpecR (slot delta : Nat) : SpecR Store :=
  { requires := fun _ => delta > 0
    ensures := fun s s' => s' = updateStore s slot (s slot + delta)
    reverts := fun _ => delta = 0 }

theorem addSlot_meets_spec (s : Store) (slot delta : Nat) :
    (addSlotSpec slot delta).requires s ->
    (match execFun addSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (addSlotSpec slot delta).ensures s s'
      | _ => False) := by
  intro _hreq
  simp [addSlotSpec, addSlotFun, execFun, execStmt, evalExpr, bindArgs, emptyEnv, updateEnv, updateStore]

theorem guardedAddSlot_meets_spec (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpec slot delta).requires s ->
    (match execFun guardedAddSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (guardedAddSlotSpec slot delta).ensures s s'
      | _ => False) := by
  intro hreq
  have hpos : delta > 0 := by exact hreq
  simp [guardedAddSlotSpec, guardedAddSlotFun, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hpos]

theorem guardedAddSlot_meets_specR_ok (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpecR slot delta).requires s ->
    (match execFun guardedAddSlotFun [slot, delta] s [] with
      | ExecResult.ok _ s' => (guardedAddSlotSpecR slot delta).ensures s s'
      | _ => False) := by
  intro hreq
  have hpos : delta > 0 := by exact hreq
  simp [guardedAddSlotSpecR, guardedAddSlotFun, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hpos]

theorem guardedAddSlot_meets_specR_reverts (s : Store) (slot delta : Nat) :
    (guardedAddSlotSpecR slot delta).reverts s ->
    execFun guardedAddSlotFun [slot, delta] s [] = ExecResult.reverted := by
  intro hrev
  simp [guardedAddSlotSpecR, guardedAddSlotFun, require, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hrev]

theorem guardedAddSlot_reverts_when_not_requires (slot delta : Nat) (h : delta = 0) :
    (guardedAddSlotSpec slot delta).requires (storeOf slot 0) = False ∧
    execFun guardedAddSlotFun [slot, delta] (storeOf slot 0) [] = ExecResult.reverted := by
  constructor
  · simp [guardedAddSlotSpec, h]
  · simp [guardedAddSlotFun, require, execFun, execStmt, evalExpr, storeOf, bindArgs, emptyEnv,
      updateEnv, updateStore, h]

end DumbContracts.Examples
