import DumbContracts.Lang
import DumbContracts.Semantics
import DumbContracts.Stdlib

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts
open DumbContracts.Std

/-- Storage layout for the simple risk model. -/

def riskStore (collateral debt minHF : Nat) : Store :=
  fun x =>
    if x = 0 then collateral
    else if x = 1 then debt
    else if x = 2 then minHF
    else 0

/-- Set collateral, debt, and minHF in slots 0/1/2. -/

def setRiskFun : Fun :=
  { name := "setRisk"
    args := ["collateral", "debt", "minHF"]
    body :=
      sstoreSlot 0 (v "collateral") ;;
      sstoreSlot 1 (v "debt") ;;
      sstoreSlot 2 (v "minHF")
    ret := none }

/-- Revert when collateral < debt * minHF. -/

def checkHealthFun : Fun :=
  { name := "checkHealth"
    args := []
    body := unless
      (Expr.lt (sloadSlot 0) (Expr.mul (sloadSlot 1) (sloadSlot 2)))
      Stmt.skip
    ret := none }

-- Execution facts.

theorem setRisk_updates (collateral debt minHF : Nat) :
    execFun setRiskFun [collateral, debt, minHF] (riskStore 0 0 0) [] =
      ExecResult.ok
        (bindArgs emptyEnv ["collateral", "debt", "minHF"] [collateral, debt, minHF])
        (riskStore collateral debt minHF) := by
  simp [setRiskFun, sstoreSlot, v, execFun, execStmt, evalExpr, riskStore, bindArgs,
    emptyEnv, updateEnv, updateStore]

theorem checkHealth_ok (collateral debt minHF : Nat) (h : debt * minHF <= collateral) :
    execFun checkHealthFun [] (riskStore collateral debt minHF) [] =
      ExecResult.ok (bindArgs emptyEnv [] []) (riskStore collateral debt minHF) := by
  simp [checkHealthFun, unless, sloadSlot, execFun, execStmt, evalExpr, riskStore,
    bindArgs, emptyEnv, updateEnv, updateStore, not_lt_of_ge h]

theorem checkHealth_reverts (collateral debt minHF : Nat) (h : collateral < debt * minHF) :
    execFun checkHealthFun [] (riskStore collateral debt minHF) [] =
      ExecResult.reverted := by
  simp [checkHealthFun, unless, sloadSlot, execFun, execStmt, evalExpr, riskStore,
    bindArgs, emptyEnv, updateEnv, updateStore, h]

-- Risk specs (Store-level).

def setRiskSpec (collateral debt minHF : Nat) : Spec Store :=
  { requires := fun _ => True
    ensures := fun s s' =>
      s' = updateStore (updateStore (updateStore s 0 collateral) 1 debt) 2 minHF }

def riskOk (store : Store) : Prop :=
  store 1 * store 2 <= store 0

def checkHealthSpec : Spec Store :=
  { requires := riskOk
    ensures := fun s s' => s' = s }

def checkHealthSpecR : SpecR Store :=
  { requires := riskOk
    ensures := fun s s' => s' = s
    reverts := fun s => s 0 < s 1 * s 2 }

theorem setRisk_meets_spec (s : Store) (collateral debt minHF : Nat) :
    (setRiskSpec collateral debt minHF).requires s ->
    (match execFun setRiskFun [collateral, debt, minHF] s [] with
      | ExecResult.ok _ s' => (setRiskSpec collateral debt minHF).ensures s s'
      | _ => False) := by
  intro _hreq
  simp [setRiskSpec, setRiskFun, sstoreSlot, v, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore]

theorem checkHealth_meets_spec (s : Store) :
    checkHealthSpec.requires s ->
    (match execFun checkHealthFun [] s [] with
      | ExecResult.ok _ s' => checkHealthSpec.ensures s s'
      | _ => False) := by
  intro hreq
  simp [checkHealthSpec, riskOk, checkHealthFun, unless, sloadSlot, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, not_lt_of_ge hreq]

theorem checkHealth_meets_specR_ok (s : Store) :
    checkHealthSpecR.requires s ->
    (match execFun checkHealthFun [] s [] with
      | ExecResult.ok _ s' => checkHealthSpecR.ensures s s'
      | _ => False) := by
  intro hreq
  simp [checkHealthSpecR, riskOk, checkHealthFun, unless, sloadSlot, execFun, execStmt,
    evalExpr, bindArgs, emptyEnv, updateEnv, updateStore, not_lt_of_ge hreq]

theorem checkHealth_meets_specR_reverts (s : Store) :
    checkHealthSpecR.reverts s ->
    execFun checkHealthFun [] s [] = ExecResult.reverted := by
  intro hrev
  simp [checkHealthSpecR, checkHealthFun, unless, sloadSlot, execFun, execStmt, evalExpr,
    bindArgs, emptyEnv, updateEnv, updateStore, hrev]

end DumbContracts.Examples
