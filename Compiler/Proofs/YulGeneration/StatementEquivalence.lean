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

/-! ### Expression Equivalence

IR and Yul expression evaluators are total and structurally identical,
so equivalence follows by mutual structural induction on expression size.
-/

open Compiler.Proofs.YulGeneration in
mutual

/-- IR and Yul expression evaluation are identical when states are aligned.
Proved by mutual structural induction on expression size. -/
theorem evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr := by
  match expr with
  | .lit n => simp [evalIRExpr, evalYulExpr]
  | .hex n => simp [evalIRExpr, evalYulExpr]
  | .str _ => simp [evalIRExpr, evalYulExpr]
  | .ident name =>
      simp [evalIRExpr, evalYulExpr, IRState.getVar, YulState.getVar, yulStateOfIR]
  | .call func args =>
      simp only [evalIRExpr, evalYulExpr]
      exact evalIRCall_eq_evalYulCall selector irState func args
termination_by exprSize expr
decreasing_by
  simp [exprSize]

/-- List version: IR and Yul list evaluation are identical when states are aligned.
Follows from `evalIRExpr_eq_evalYulExpr` by structural induction on the list. -/
theorem evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs := by
  match exprs with
  | [] => simp [evalIRExprs, evalYulExprs]
  | e :: es =>
      simp only [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr selector irState e]
      rw [evalIRExprs_eq_evalYulExprs selector irState es]
termination_by exprsSize exprs
decreasing_by
  all_goals
    simp [exprsSize]
    omega

/-- Call version: IR and Yul call evaluation are identical when states are aligned. -/
theorem evalIRCall_eq_evalYulCall (selector : Nat) (irState : IRState) (func : String) (args : List YulExpr) :
    evalIRCall irState func args = evalYulCall (yulStateOfIR selector irState) func args := by
  simp only [evalIRCall, evalYulCall]
  rw [evalIRExprs_eq_evalYulExprs selector irState args]
  rfl
termination_by exprsSize args + 1
decreasing_by
  simp

end

attribute [simp] evalIRExpr_eq_evalYulExpr evalIRExprs_eq_evalYulExprs evalIRCall_eq_evalYulCall

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
      simp [execIRStmtFuel, execIRStmt, execYulStmtFuel, execYulFuel]
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

private theorem stmts_align_contra
    {selector fuel : Nat} {stmts : List YulStmt} {irState : IRState} {yulState : YulState}
    {irExec : IRExecResult} {yulExec : YulExecResult}
    (hStmts : execResultsAligned selector
      (execIRStmtsFuel fuel irState stmts)
      (execYulStmtsFuel fuel yulState stmts))
    (hIR : execIRStmtsFuel fuel irState stmts = irExec)
    (hYul : execYulStmtsFuel fuel yulState stmts = yulExec)
    (hImpossible : ¬ execResultsAligned selector irExec yulExec) : False := by
  apply hImpossible
  simpa [hIR, hYul] using hStmts

private theorem stmt_align_contra
    {selector fuel : Nat} {stmt : YulStmt} {irState : IRState} {yulState : YulState}
    {irExec : IRExecResult} {yulExec : YulExecResult}
    (hStmt : execResultsAligned selector
      (execIRStmtFuel fuel irState stmt)
      (execYulStmtFuel fuel yulState stmt))
    (hIR : execIRStmtFuel fuel irState stmt = irExec)
    (hYul : execYulStmtFuel fuel yulState stmt = yulExec)
    (hImpossible : ¬ execResultsAligned selector irExec yulExec) : False := by
  apply hImpossible
  simpa [hIR, hYul] using hStmt

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
private theorem stmt_and_stmts_equiv :
    ∀ fuel,
      (∀ selector stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) ∧
      (∀ selector stmts irState yulState,
        execIRStmts_equiv_execYulStmts_goal selector fuel stmts irState yulState) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro selector stmt irState yulState halign
        cases stmt <;>
          simp [execIRStmtFuel, execIRStmt,
            execYulStmtFuel, execYulFuel, execResultsAligned, halign]
      · intro selector stmts irState yulState halign
        cases stmts <;>
          simp [execIRStmtsFuel, execIRStmts,
            execYulStmtsFuel, execYulFuel, execResultsAligned, halign]
  | succ fuel ih =>
      rcases ih with ⟨ihStmt, ihStmts⟩
      constructor
      · intro selector stmt irState yulState halign
        unfold statesAligned at halign
        subst halign
        cases stmt with
        | comment _ =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | let_ name value =>
            exact assign_equiv selector (fuel + 1) name value irState
              (yulStateOfIR selector irState) rfl (by omega)
        | letMany _ _ =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | assign name value =>
            exact assign_equiv selector (fuel + 1) name value irState
              (yulStateOfIR selector irState) rfl (by omega)
        | «leave» =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | expr e =>
            cases e with
            | call func args =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, execYulFuel]
                -- Both sides match on (.call func args) against string literals.
                -- With `func` free, neither match tree reduces. Generalize so both
                -- sides share the same discriminant, then split.
                generalize YulExpr.call func args = disc
                split
                · -- sstore: inner match on slotExpr
                  split
                  · -- mappingSlot: match on 3 evals
                    simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                    split <;> simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                  · -- non-mappingSlot: match on 2 evals
                    simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                    split <;> simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                · -- mstore: match on 2 evals
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                · -- tstore: match on 2 evals
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                · -- stop
                  simp [execResultsAligned, statesAligned, yulStateOfIR]
                · -- revert
                  simp [execResultsAligned, statesAligned, yulStateOfIR]
                · -- return: match on 2 evals, then if on size = 32
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  repeat' split
                  all_goals simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                · -- catch-all: match on eval of full expr
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all [execResultsAligned, statesAligned, yulStateOfIR]
            | lit val =>
                simp [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, execYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | hex val =>
                simp [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, execYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | str val =>
                simp [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, execYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | ident val =>
                simp [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, execYulFuel, evalIRExpr, evalYulExpr,
                  IRState.getVar, YulState.getVar,
                  execResultsAligned, statesAligned, yulStateOfIR]
                cases hfind : List.find? (fun x => x.1 == val) irState.vars <;>
                  simp
        | if_ cond body =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel]
            rw [evalIRExpr_eq_evalYulExpr]
            cases hcond : evalYulExpr (yulStateOfIR selector irState) cond with
            | none =>
                simp [execResultsAligned, statesAligned, yulStateOfIR]
            | some c =>
                simp
                by_cases hc : c = 0
                · simp [hc, execResultsAligned, statesAligned, yulStateOfIR]
                · simp [hc]
                  exact ihStmts selector body irState (yulStateOfIR selector irState) rfl
        | «switch» expr cases defaultCase =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel, beq_eq_decide, yulStateOfIR]
            rw [evalIRExpr_eq_evalYulExpr]
            cases hEval : evalYulExpr (yulStateOfIR selector irState) expr with
            | none =>
                have hEval' :
                    evalYulExpr
                  { vars := irState.vars, storage := irState.storage,
                        transientStorage := irState.transientStorage, memory := irState.memory,
                        calldata := irState.calldata, selector := irState.selector,
                        returnValue := irState.returnValue, sender := irState.sender,
                        msgValue := irState.msgValue, thisAddress := irState.thisAddress,
                        blockTimestamp := irState.blockTimestamp, blockNumber := irState.blockNumber,
                        chainId := irState.chainId,
                        blobBaseFee := irState.blobBaseFee,
                        events := irState.events } expr = none := by
                  simpa [yulStateOfIR] using hEval
                simp [hEval', execResultsAligned, statesAligned, yulStateOfIR]
            | some v =>
                have hEval' :
                    evalYulExpr
                  { vars := irState.vars, storage := irState.storage,
                        transientStorage := irState.transientStorage, memory := irState.memory,
                        calldata := irState.calldata, selector := irState.selector,
                        returnValue := irState.returnValue, sender := irState.sender,
                        msgValue := irState.msgValue, thisAddress := irState.thisAddress,
                        blockTimestamp := irState.blockTimestamp, blockNumber := irState.blockNumber,
                        chainId := irState.chainId,
                        blobBaseFee := irState.blobBaseFee,
                        events := irState.events } expr = some v := by
                  simpa [yulStateOfIR] using hEval
                simp [hEval']
                cases hFind : cases.find? (fun x => decide (x.fst = v)) with
                | none =>
                    have hFind' :
                        List.find? (fun x => decide (x.fst = v)) cases = none := hFind
                    simp
                    cases defaultCase with
                    | none =>
                        simp [execResultsAligned, statesAligned, yulStateOfIR]
                    | some body =>
                        simpa [hEval', hFind', execYulStmtsFuel, execYulFuel] using
                          ihStmts selector body irState (yulStateOfIR selector irState) rfl
                | some pair =>
                    cases pair with
                    | mk _ body =>
                        simpa [hEval', hFind, execYulStmtsFuel, execIRStmtsFuel, execYulFuel] using
                          ihStmts selector body irState (yulStateOfIR selector irState) rfl
        | for_ init cond post body =>
            simp only [execIRStmtFuel,
              execIRStmt, execYulStmtFuel_for]
            have hInit := ihStmts selector init irState (yulStateOfIR selector irState) rfl
            cases hIRInit : execIRStmtsFuel fuel irState init with
            | «continue» irAfterInit =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» yulAfterInit =>
                    have hAlignedInit : statesAligned selector irAfterInit yulAfterInit := by
                      simpa [execResultsAligned, hIRInit, hYulInit] using hInit
                    unfold statesAligned at hAlignedInit
                    subst hAlignedInit
                    -- Normalize yulStateOfIR after subst to match expanded kernel forms
                    simp only [yulStateOfIR] at *
                    have hCondEq : evalIRExpr irAfterInit cond =
                        evalYulExpr (yulStateOfIR selector irAfterInit) cond :=
                      evalIRExpr_eq_evalYulExpr selector irAfterInit cond
                    cases hCondIR : evalIRExpr irAfterInit cond with
                    | none =>
                        have hCondYul : evalYulExpr (yulStateOfIR selector irAfterInit) cond = none := by
                          symm
                          simpa [hCondIR] using hCondEq
                        simp only [yulStateOfIR] at hCondYul
                        simp [hIRInit, hCondIR, hCondYul,
                          execResultsAligned, statesAligned, yulStateOfIR]
                    | some v =>
                        have hCondYul : evalYulExpr (yulStateOfIR selector irAfterInit) cond = some v := by
                          symm
                          simpa [hCondIR] using hCondEq
                        by_cases hv : v = 0
                        · simp only [yulStateOfIR] at hCondYul
                          simp [hIRInit, hCondIR, hCondYul, hv,
                            execResultsAligned, statesAligned, yulStateOfIR]
                        · have hBody :=
                            ihStmts selector body irAfterInit (yulStateOfIR selector irAfterInit) rfl
                          cases hIRBody : execIRStmtsFuel fuel irAfterInit body with
                          | «continue» irAfterBody =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «continue» yulAfterBody =>
                                  have hAlignedBody : statesAligned selector irAfterBody yulAfterBody := by
                                    simpa [execResultsAligned, hIRBody, hYulBody] using hBody
                                  unfold statesAligned at hAlignedBody
                                  subst hAlignedBody
                                  simp only [yulStateOfIR] at *
                                  have hPost :=
                                    ihStmts selector post irAfterBody (yulStateOfIR selector irAfterBody) rfl
                                  cases hIRPost : execIRStmtsFuel fuel irAfterBody post with
                                  | «continue» irAfterPost =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «continue» yulAfterPost =>
                                          have hAlignedPost : statesAligned selector irAfterPost yulAfterPost := by
                                            simpa [execResultsAligned, hIRPost, hYulPost] using hPost
                                          unfold statesAligned at hAlignedPost
                                          subst hAlignedPost
                                          simp only [yulStateOfIR] at *
                                          have hRec := ihStmt selector (.for_ [] cond post body)
                                              irAfterPost (yulStateOfIR selector irAfterPost) rfl
                                          simp_all [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                                            execYulStmtFuel, execYulStmtsFuel, yulStateOfIR]
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                  | «return» _ _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «return» _ _ =>
                                          simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                  | «stop» _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «stop» _ =>
                                          simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                  | «revert» _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «revert» _ =>
                                          simp_all [execResultsAligned, statesAligned, yulStateOfIR]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp [execResultsAligned]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                          | «return» _ _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «return» _ _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp [hIRInit, hCondIR, hCondYul, hv,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                          | «stop» _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «stop» _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp [hIRInit, hCondIR, hCondYul, hv,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                          | «revert» _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «revert» _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp [hIRInit, hCondIR, hCondYul, hv,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
            | «return» retVal retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.return retVal retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa [hIRInit] using hInit
                    simp_all [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR]
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
            | «stop» retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «stop» _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.stop retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa [hIRInit] using hInit
                    simp_all [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR]
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
            | «revert» retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp [execResultsAligned]))
                | «revert» _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.revert retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa [hIRInit] using hInit
                    simp_all [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | block stmts =>
            simpa [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel] using
              ihStmts selector stmts irState (yulStateOfIR selector irState) rfl
        | funcDef _ _ _ _ =>
            simp [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, execYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
      · intro selector stmts irState yulState halign
        unfold statesAligned at halign
        subst halign
        cases stmts with
        | nil =>
            simp [execIRStmtsFuel, execIRStmts,
              execYulStmtsFuel, execYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | cons stmt rest =>
            have hStmt := ihStmt selector stmt irState (yulStateOfIR selector irState) rfl
            cases hIR : execIRStmtFuel fuel irState stmt with
            | «continue» ir' =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «continue» y' =>
                    have hAligned' : statesAligned selector ir' y' := by
                      simpa [execResultsAligned, hIR, hYul] using hStmt
                    have hRest := ihStmts selector rest ir' y' hAligned'
                    simpa [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, hIR, hYul] using hRest
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
            | «return» _ _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «return» _ _ =>
                    simpa [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
            | «stop» _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «stop» _ =>
                    simpa [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
            | «revert» _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «revert» _ =>
                    simpa [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))

theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState := by
  intro selector fuel stmt irState yulState
  exact (stmt_and_stmts_equiv fuel).1 selector stmt irState yulState

theorem conditional_equiv (selector : Nat) (fuel : Nat)
    (condExpr : YulExpr) (body : List YulStmt)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.if_ condExpr body))
      (execYulStmtFuel fuel yulState (YulStmt.if_ condExpr body)) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.if_ condExpr body) irState yulState halign)

theorem return_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])) irState yulState halign)

theorem revert_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])) irState yulState halign)

theorem storageStore_equiv (selector : Nat) (fuel : Nat)
    (slotExpr valExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "sstore" [slotExpr, valExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "sstore" [slotExpr, valExpr]))) := by
  simpa [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "sstore" [slotExpr, valExpr])) irState yulState halign)


end Compiler.Proofs.YulGeneration
