import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Layer 3: Statement-Level Equivalence (Complete)

Proves that each IR statement type executes equivalently in Yul when states
are aligned. Uses `mutual` recursion between `conditional_equiv` and
`all_stmts_equiv` to handle the circular dependency.

Individual statement proofs compose via `execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv`
(Equivalence.lean) to complete the `hbody` hypothesis in `Preservation.lean`.
-/

/-! ### Expression Equivalence (Now Proven — Previously Axioms)

With the IR expression evaluators refactored to be total and structurally
identical to the Yul evaluators, these are now **proven theorems**.

Previously these were axioms:
  axiom evalIRExpr_eq_evalYulExpr : ...
  axiom evalIRExprs_eq_evalYulExprs : ...

Eliminated by making `evalIRExpr`/`evalIRExprs`/`evalIRCall` total (using
`termination_by` with `exprSize`/`exprsSize`) and restructuring `evalIRCall`
to evaluate all arguments first (matching `evalYulCall`). See Issue #148.
-/

open Compiler.Proofs.YulGeneration in
mutual

/-- IR and Yul expression evaluation are identical when states are aligned.

PROVEN (previously axiom #1). Both evaluators are now total with identical
structure — the proof proceeds by mutual structural induction on expression size. -/
theorem evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr := by
  match expr with
  | .lit n => rfl
  | .hex n => rfl
  | .str _ => rfl
  | .ident name =>
      simp [evalIRExpr, evalYulExpr, IRState.getVar, YulState.getVar, yulStateOfIR]
  | .call func args =>
      simp only [evalIRExpr, evalYulExpr]
      exact evalIRCall_eq_evalYulCall selector irState func args
termination_by exprSize expr
decreasing_by
  simp [exprSize, exprsSize]

/-- List version: IR and Yul list evaluation are identical when states are aligned.

PROVEN (previously axiom #2). Follows from `evalIRExpr_eq_evalYulExpr` by
structural induction on the expression list. -/
theorem evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs := by
  match exprs with
  | [] => rfl
  | e :: es =>
      simp only [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr selector irState e]
      rw [evalIRExprs_eq_evalYulExprs selector irState es]
termination_by exprsSize exprs
decreasing_by
  all_goals
    simp [exprsSize, exprSize]
    omega

/-- Call version: IR and Yul call evaluation are identical when states are aligned. -/
theorem evalIRCall_eq_evalYulCall (selector : Nat) (irState : IRState) (func : String) (args : List YulExpr) :
    evalIRCall irState func args = evalYulCall (yulStateOfIR selector irState) func args := by
  simp only [evalIRCall, evalYulCall]
  rw [evalIRExprs_eq_evalYulExprs selector irState args]
  simp [yulStateOfIR, selectorWord]
termination_by exprsSize args + 1
decreasing_by
  simp [exprsSize, exprSize]

end

/-! ## Proven Theorems -/

theorem assign_equiv (selector : Nat) (fuel : Nat) (varName : String) (valueExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.assign varName valueExpr))
      (execYulStmtFuel fuel yulState (YulStmt.assign varName valueExpr)) := by
  -- Unfold state alignment
  unfold statesAligned at halign
  subst halign
  -- Destruct fuel
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
      -- Use lemma: evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr
      rw [evalIRExpr_eq_evalYulExpr]
      -- Now both sides are identical
      cases evalYulExpr (yulStateOfIR selector irState) valueExpr with
      | none =>
          -- Both revert
          unfold execResultsAligned
          rfl
      | some v =>
          -- Both continue with updated variable
          unfold execResultsAligned statesAligned yulStateOfIR
          simp [IRState.setVar, YulState.setVar]

/-! ### Storage Store Equivalence -/

theorem storageStore_equiv (selector : Nat) (fuel : Nat)
    (slotExpr valExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "sstore" [slotExpr, valExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "sstore" [slotExpr, valExpr]))) := by
  -- Storage store follows same pattern
  unfold statesAligned at halign
  subst halign
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
      -- Both eval the same expressions using our theorem
      simp only [evalIRExpr_eq_evalYulExpr, evalIRExprs_eq_evalYulExprs]
      -- Now both sides are syntactically identical
      unfold execResultsAligned statesAligned yulStateOfIR
      simp

/-! ### Conditional (if) and Universal Statement Equivalence

Proven mutually: `conditional_equiv` needs `all_stmts_equiv` for the body,
and `all_stmts_equiv` needs `conditional_equiv` for `if_` statements.
-/

mutual

theorem conditional_equiv (selector : Nat) (fuel : Nat)
    (condExpr : YulExpr) (body : List YulStmt)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.if_ condExpr body))
      (execYulStmtFuel fuel yulState (YulStmt.if_ condExpr body)) := by
  -- Conditional evaluates condition, then executes body if non-zero
  unfold statesAligned at halign
  subst halign
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
      rw [evalIRExpr_eq_evalYulExpr]
      cases h : evalYulExpr (yulStateOfIR selector irState) condExpr with
      | none =>
          -- Evaluation fails, both revert
          unfold execResultsAligned
          rfl
      | some c =>
          -- Evaluation succeeds with value c
          simp [h]
          by_cases hc : c = 0
          · -- Condition is false (0), both continue without executing body
            simp [hc]
            unfold execResultsAligned statesAligned yulStateOfIR
            rfl
          · -- Condition is true (non-zero), both execute body
            simp [hc]
            -- Both call execIRStmtsFuel/execYulStmtsFuel on the body
            -- Apply the composition theorem with all_stmts_equiv
            exact execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
              (fun sel f st irSt yulSt => all_stmts_equiv sel f st irSt yulSt)
              selector fuel' body irState (yulStateOfIR selector irState) rfl

/-! Universal dispatcher: dispatches to specific theorems based on statement type. -/

theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState := by
  intros selector fuel stmt irState yulState halign
  -- Need fuel > 0 for the theorems to apply
  cases fuel with
  | zero =>
      -- When fuel is 0, goal is trivial (both timeout/fail)
      unfold execIRStmt_equiv_execYulStmt_goal
      intro _
      unfold execResultsAligned
      cases stmt <;> simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel]
  | succ fuel' =>
      -- Dispatch to specific theorem based on statement type
      cases stmt with
      | comment _ =>
          -- Trivial: both no-op
          unfold execIRStmt_equiv_execYulStmt_goal execResultsAligned
          intro hAlign
          unfold statesAligned at hAlign
          subst hAlign
          simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel, yulStateOfIR]
      | let_ name value =>
          exact assign_equiv selector (fuel' + 1) name value irState yulState halign (by omega)
      | assign name value =>
          exact assign_equiv selector (fuel' + 1) name value irState yulState halign (by omega)
      | expr e =>
          -- Expression statements - dispatch based on expression type
          cases e with
          | call fname args =>
              -- Handle specific builtin calls
              match fname, args with
              | "sstore", [slotExpr, valExpr] =>
                  exact storageStore_equiv selector (fuel' + 1) slotExpr valExpr irState yulState halign (by omega)
              | "return", [offsetExpr, sizeExpr] =>
                  exact return_equiv selector (fuel' + 1) offsetExpr sizeExpr irState yulState halign (by omega)
              | "revert", [offsetExpr, sizeExpr] =>
                  exact revert_equiv selector (fuel' + 1) offsetExpr sizeExpr irState yulState halign (by omega)
              | _, _ =>
                  -- Generic handling: stop, mstore, and all other expression statements
                  unfold execIRStmt_equiv_execYulStmt_goal execResultsAligned
                  intro hAlign
                  unfold statesAligned at hAlign
                  subst hAlign
                  simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel, yulStateOfIR, evalIRExpr_eq_evalYulExpr, evalIRExprs_eq_evalYulExprs]
          | _ =>
              -- Non-call expressions - generic handling
              unfold execIRStmt_equiv_execYulStmt_goal execResultsAligned
              intro hAlign
              unfold statesAligned at hAlign
              subst hAlign
              simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel, yulStateOfIR, evalIRExpr_eq_evalYulExpr]
      | if_ cond body =>
          exact conditional_equiv selector (fuel' + 1) cond body irState yulState halign (by omega)
      | switch expr cases default =>
          -- Switch evaluates expr and matches against cases, with optional default
          unfold execIRStmt_equiv_execYulStmt_goal execResultsAligned
          intro hAlign
          unfold statesAligned at hAlign
          subst hAlign
          unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
          rw [evalIRExpr_eq_evalYulExpr]
          cases h : evalYulExpr (yulStateOfIR selector irState) expr with
          | none =>
              -- Evaluation fails, both revert
              rfl
          | some v =>
              -- Evaluation succeeds with value v
              simp [h]
              -- Both use List.find? with the same predicate (x.fst = v)
              -- The find? results will be identical, so we case split on the result
              cases hfind : cases.find? (fun x => decide (x.fst = v)) with
              | none =>
                  -- No matching case found, use default
                  simp [hfind]
                  cases default with
                  | none =>
                      -- No default, both continue
                      rfl
                  | some body =>
                      -- Execute default body - apply composition theorem
                      exact execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
                        (fun sel f st irSt yulSt => all_stmts_equiv sel f st irSt yulSt)
                        selector fuel' body irState (yulStateOfIR selector irState) rfl
              | some (val, body) =>
                  -- Found matching case, execute its body - apply composition theorem
                  simp [hfind]
                  exact execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
                    (fun sel f st irSt yulSt => all_stmts_equiv sel f st irSt yulSt)
                    selector fuel' body irState (yulStateOfIR selector irState) rfl
      | block stmts =>
          -- Recursive: apply composition theorem
          unfold execIRStmt_equiv_execYulStmt_goal
          intro hAlign
          unfold statesAligned at hAlign
          subst hAlign
          simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel]
          exact execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
            (fun sel f st irSt yulSt => all_stmts_equiv sel f st irSt yulSt)
            selector fuel' stmts irState (yulStateOfIR selector irState) rfl
      | funcDef _ _ _ _ =>
          -- No-op
          unfold execIRStmt_equiv_execYulStmt_goal execResultsAligned
          intro hAlign
          unfold statesAligned at hAlign
          subst hAlign
          simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel, yulStateOfIR]

end

/-! ### Return Statement Equivalence -/

theorem return_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr]))) := by
  -- Return evaluates offset and size, then transitions to .return state
  unfold statesAligned at halign
  subst halign
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
      simp only [evalIRExpr_eq_evalYulExpr, evalIRExprs_eq_evalYulExprs]
      unfold execResultsAligned statesAligned yulStateOfIR
      simp

/-! ### Revert Statement Equivalence -/

theorem revert_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr]))) := by
  -- Revert transitions to .revert state - both do the same
  unfold statesAligned at halign
  subst halign
  cases fuel with
  | zero => contradiction
  | succ fuel' =>
      unfold execIRStmtFuel execIRStmt execYulStmtFuel execYulFuel
      -- Both return .revert regardless of evaluation
      unfold execResultsAligned statesAligned yulStateOfIR
      rfl


end Compiler.Proofs.YulGeneration
