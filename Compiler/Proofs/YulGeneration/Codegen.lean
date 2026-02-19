import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Proofs.YulGeneration.Lemmas

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Codegen Proof Obligations (Layer 3)

These lemmas capture the core obligations for Yul codegen correctness:
1. Selector extraction matches the function selector.
2. Runtime switch dispatch executes the selected function body.
-/

@[simp]
theorem emitYul_runtimeCode_eq (contract : IRContract) :
    (Compiler.emitYul contract).runtimeCode = Compiler.runtimeCode contract := by
  rfl

/-- Selector extraction via `selectorExpr` yields the 4-byte selector. -/
@[simp]
theorem evalYulExpr_selectorExpr (state : YulState) :
    evalYulExpr state selectorExpr = some (state.selector % selectorModulus) :=
by
  simpa using (Compiler.Proofs.YulGeneration.evalYulExpr_selectorExpr_semantics state)

/-- Selector extraction yields the raw selector when it fits in 4 bytes. -/
@[simp]
theorem evalYulExpr_selectorExpr_eq (state : YulState)
    (hselector : state.selector < selectorModulus) :
    evalYulExpr state selectorExpr = some state.selector :=
by
  simp [evalYulExpr_selectorExpr, Nat.mod_eq_of_lt hselector]

theorem execYulFuel_mappingSlotFunc (fuel : Nat) (state : YulState) :
    execYulFuel fuel state (YulExecTarget.stmt mappingSlotFunc) =
      YulExecResult.continue state :=
by
  cases fuel <;> simp [mappingSlotFunc, execYulFuel]

theorem execYulFuel_drop_mappingSlotFunc_buildSwitch
    (fuel : Nat) (state : YulState) (fns : List IRFunction) :
    execYulFuel (fuel + 1) state (YulExecTarget.stmts [mappingSlotFunc, buildSwitch fns]) =
      execYulFuel fuel state (YulExecTarget.stmts [buildSwitch fns]) :=
by
  cases fuel with
  | zero =>
      simp [execYulFuel, execYulFuel_mappingSlotFunc]
  | succ fuel =>
      simp [execYulFuel, execYulFuel_mappingSlotFunc]

theorem execYulStmts_runtimeCode_eq :
    ∀ (contract : IRContract) (state : YulState) (fuel : Nat),
      execYulStmtsFuel fuel state (Compiler.runtimeCode contract) =
        execYulStmtsFuel fuel state [Compiler.buildSwitch contract.functions] :=
by
  intro contract state fuel
  by_cases h : contract.usesMapping
  · cases fuel with
    | zero =>
        simp [Compiler.runtimeCode, h, execYulStmtsFuel, execYulFuel]
    | succ fuel =>
        simp [Compiler.runtimeCode, h, execYulStmtsFuel]
        simpa using
          (execYulFuel_drop_mappingSlotFunc_buildSwitch fuel state contract.functions)
  · simp [Compiler.runtimeCode, h, execYulStmtsFuel]

/-- Switch cases generated from IR functions. -/
def switchCases (fns : List IRFunction) : List (Prod Nat (List YulStmt)) :=
  fns.map (fun f =>
    let body := [YulStmt.comment s!"{f.name}()"] ++
      [Compiler.callvalueGuard] ++ [Compiler.calldatasizeGuard f.params.length] ++ f.body
    (f.selector, body)
  )

@[simp] theorem buildSwitch_eq (fns : List IRFunction) :
    Compiler.buildSwitch fns =
      YulStmt.switch selectorExpr (switchCases fns) (some [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ]) := by
  simp [Compiler.buildSwitch, selectorExpr, switchCases, selectorShift]

/-- If the selector matches a case, the switch executes that case body (fueled). -/
theorem execYulStmtFuel_switch_match
    (state : YulState) (expr : YulExpr) (cases' : List (Prod Nat (List YulStmt)))
    (default : Option (List YulStmt)) (fuel v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = some (v, body)) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      execYulStmtsFuel fuel state body := by
  have hFind' :
      List.find? (fun x : Prod Nat (List YulStmt) => decide (x.1 = v)) cases' = some (v, body) := by
    simpa using hFind
  simpa using (Compiler.Proofs.YulGeneration.execYulStmtFuel_switch_match_semantics
    state expr cases' default fuel v body hEval hFind')

/-- If no selector case matches, the switch executes the default (or continues). -/
def execYulStmtFuel_switch_miss_result (state : YulState) (fuel : Nat)
    (default : Option (List YulStmt)) : YulExecResult :=
  match default with
  | some body => execYulStmtsFuel fuel state body
  | none => YulExecResult.continue state

theorem execYulStmtFuel_switch_miss
    (state : YulState) (expr : YulExpr) (cases' : List (Prod Nat (List YulStmt)))
    (default : Option (List YulStmt)) (fuel v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = none) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' default) =
      execYulStmtFuel_switch_miss_result state fuel default := by
  have hFind' :
      List.find? (fun x : Prod Nat (List YulStmt) => decide (x.1 = v)) cases' = none := by
    simpa using hFind
  have h :=
    Compiler.Proofs.YulGeneration.execYulStmtFuel_switch_miss_semantics
      state expr cases' default fuel v hEval hFind'
  simpa [execYulStmtFuel_switch_miss_result] using h

/- Bridge lemmas for switch-case lookup. -/
theorem find_switch_case_of_find_function
    (fns : List IRFunction) (sel : Nat) (fn : IRFunction)
    (hFind : fns.find? (fun f => f.selector == sel) = some fn) :
    (switchCases fns).find? (fun (c, _) => c = sel) =
      some (fn.selector, [YulStmt.comment s!"{fn.name}()"] ++
        [Compiler.callvalueGuard] ++ [Compiler.calldatasizeGuard fn.params.length] ++ fn.body) := by
  induction fns with
  | nil =>
      simp at hFind
  | cons f rest ih =>
      by_cases hsel : f.selector = sel
      · have hselb : (f.selector == sel) = true := by
          simp [beq_iff_eq, hsel]
        have hFind' : some f = some fn := by
          simpa [List.find?, hselb] using hFind
        cases hFind'
        simp [switchCases, List.find?, hsel]
      · have hselb : (f.selector == sel) = false := by
          simp [beq_iff_eq, hsel]
        have hFind' : rest.find? (fun f => f.selector == sel) = some fn := by
          simpa [List.find?, hselb] using hFind
        have ih' := ih hFind'
        simpa [switchCases, List.find?, hsel] using ih'

theorem find_switch_case_of_find_function_none
    (fns : List IRFunction) (sel : Nat)
    (hFind : fns.find? (fun f => f.selector == sel) = none) :
    (switchCases fns).find? (fun (c, _) => c = sel) = none := by
  induction fns with
  | nil =>
      simp at hFind
      simp [switchCases]
  | cons f rest ih =>
      by_cases hsel : f.selector = sel
      · have hselb : (f.selector == sel) = true := by
          simp [beq_iff_eq, hsel]
        have hFind' : (some f : Option IRFunction) = none := by
          simpa [List.find?, hselb] using hFind
        cases hFind'
      · have hselb : (f.selector == sel) = false := by
          simp [beq_iff_eq, hsel]
        have hFind' : rest.find? (fun f => f.selector == sel) = none := by
          simpa [List.find?, hselb] using hFind
        have ih' := ih hFind'
        simpa [switchCases, List.find?, hsel] using ih'


end Compiler.Proofs.YulGeneration
