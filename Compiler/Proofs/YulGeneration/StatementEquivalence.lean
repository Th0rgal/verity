import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.IRFuel
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

private def yulStateOfIR (_selector : Nat) (state : IRState) : YulState :=
  { vars := state.vars
    storage := state.storage
    transientStorage := state.transientStorage
    memory := state.memory
    calldata := state.calldata
    selector := state.selector
    returnValue := state.returnValue
    sender := state.sender
    msgValue := state.msgValue
    thisAddress := state.thisAddress
    blockTimestamp := state.blockTimestamp
    blockNumber := state.blockNumber
    chainId := state.chainId
    blobBaseFee := state.blobBaseFee
    events := state.events }

private def statesAligned (selector : Nat) (ir : IRState) (yul : YulState) : Prop :=
  yul = yulStateOfIR selector ir

private def execResultsAligned (selector : Nat) : IRExecResult → YulExecResult → Prop
  | .continue ir, .continue yul => statesAligned selector ir yul
  | .return v ir, .return v' yul => v = v' ∧ statesAligned selector ir yul
  | .stop ir, .stop yul => statesAligned selector ir yul
  | .revert ir, .revert yul => statesAligned selector ir yul
  | _, _ => False

private def execIRStmt_equiv_execYulStmt_goal
    (selector : Nat) (fuel : Nat) (stmt : YulStmt)
    (irState : IRState) (yulState : YulState) : Prop :=
  statesAligned selector irState yulState →
  execResultsAligned selector
    (execIRStmtFuel fuel irState stmt) (execYulStmtFuel fuel yulState stmt)

private def execIRStmts_equiv_execYulStmts_goal
    (selector : Nat) (fuel : Nat) (stmts : List YulStmt)
    (irState : IRState) (yulState : YulState) : Prop :=
  statesAligned selector irState yulState →
  execResultsAligned selector
    (execIRStmtsFuel fuel irState stmts) (execYulStmtsFuel fuel yulState stmts)

/-! ## Layer 3: Statement-Level Equivalence (Complete)

Proves that each IR statement type executes equivalently in Yul when states
are aligned. Uses `mutual` recursion between `conditional_equiv` and
`all_stmts_equiv` to handle the circular dependency.

Individual statement proofs feed the file-local sequence/function lifting
helpers in `Equivalence.lean`; the statement-level legacy equivalence theorem
`all_stmts_equiv` remains file-local transition evidence.
-/

private theorem execYulStmtsFuel_cons
    (fuel : Nat) (state : YulState) (stmt : YulStmt) (rest : List YulStmt) :
    execYulStmtsFuel (Nat.succ fuel) state (stmt :: rest) =
      match execYulStmtFuel fuel state stmt with
      | .continue s' => execYulStmtsFuel fuel s' rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := by
  rfl

private theorem execYulStmtFuel_for
    (fuel : Nat) (state : YulState) (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.for_ init cond post body) =
      match execYulStmtsFuel fuel state init with
      | .continue s' =>
          match evalYulExpr s' cond with
          | some v =>
              if v = 0 then .continue s'
              else
                match execYulStmtsFuel fuel s' body with
                | .continue s'' =>
                    match execYulStmtsFuel fuel s'' post with
                    | .continue s''' => execYulStmtFuel fuel s''' (.for_ [] cond post body)
                    | other => other
                | other => other
          | none => .revert s'
      | other => other := by
  rfl

/-! ### Expression Equivalence

IR and Yul expression evaluators are total and structurally identical,
so equivalence follows by mutual structural induction on expression size.
-/

open Compiler.Proofs.YulGeneration in
mutual

/-- IR and Yul expression evaluation are identical when states are aligned.
Proved by mutual structural induction on expression size. -/
private theorem evalIRExpr_eq_evalYulExpr (selector : Nat) (irState : IRState) (expr : YulExpr) :
    evalIRExpr irState expr = evalYulExpr (yulStateOfIR selector irState) expr := by
  match expr with
  | .lit n => simp only [evalIRExpr, evalYulExpr]
  | .hex n => simp only [evalIRExpr, evalYulExpr]
  | .str _ => simp only [evalIRExpr, evalYulExpr]
  | .ident name =>
      simp only [evalIRExpr, evalYulExpr, IRState.getVar, YulState.getVar, yulStateOfIR]
  | .call func args =>
      simp only [evalIRExpr, evalYulExpr]
      exact evalIRCall_eq_evalYulCall selector irState func args
termination_by exprSize expr
decreasing_by
  simp only [exprSize]; omega

/-- List version: IR and Yul list evaluation are identical when states are aligned.
Follows from `evalIRExpr_eq_evalYulExpr` by structural induction on the list. -/
private theorem evalIRExprs_eq_evalYulExprs (selector : Nat) (irState : IRState) (exprs : List YulExpr) :
    evalIRExprs irState exprs = evalYulExprs (yulStateOfIR selector irState) exprs := by
  match exprs with
  | [] => simp only [evalIRExprs, evalYulExprs]
  | e :: es =>
      simp only [evalIRExprs, evalYulExprs]
      rw [evalIRExpr_eq_evalYulExpr selector irState e]
      rw [evalIRExprs_eq_evalYulExprs selector irState es]
termination_by exprsSize exprs
decreasing_by
  all_goals
    simp only [exprsSize]
    omega

/-- Call version: IR and Yul call evaluation are identical when states are aligned. -/
private theorem evalIRCall_eq_evalYulCall (selector : Nat) (irState : IRState) (func : String) (args : List YulExpr) :
    evalIRCall irState func args = evalYulCall (yulStateOfIR selector irState) func args := by
  simp only [evalIRCall, evalYulCall]
  rw [evalIRExprs_eq_evalYulExprs selector irState args]
  rfl
termination_by exprsSize args + 1
decreasing_by
  omega

end

attribute [simp] evalIRExpr_eq_evalYulExpr evalIRExprs_eq_evalYulExprs evalIRCall_eq_evalYulCall

/-! ## Proven Theorems -/

private theorem applyYulLogCall?_aligned
    (selector : Nat) (irState : IRState) (func : String) (argVals : List Nat) :
    applyYulLogCall? (yulStateOfIR selector irState) func argVals =
      (IRGeneration.applyYulLogCall? irState func argVals).map
        (fun next => yulStateOfIR selector next) := by
  cases argVals with
  | nil => simp [applyYulLogCall?, IRGeneration.applyYulLogCall?]
  | cons a rest =>
      cases rest with
      | nil => simp [applyYulLogCall?, IRGeneration.applyYulLogCall?]
      | cons b rest =>
          cases rest with
          | nil =>
              by_cases h0 : func = "log0" <;>
                simp [applyYulLogCall?, IRGeneration.applyYulLogCall?,
                  YulState.appendYulLog, IRState.appendYulLog, yulStateOfIR, h0]
          | cons c rest =>
              cases rest with
              | nil =>
                  by_cases h1 : func = "log1" <;>
                    simp [applyYulLogCall?, IRGeneration.applyYulLogCall?,
                      YulState.appendYulLog, IRState.appendYulLog, yulStateOfIR, h1]
              | cons d rest =>
                  cases rest with
                  | nil =>
                      by_cases h2 : func = "log2" <;>
                        simp [applyYulLogCall?, IRGeneration.applyYulLogCall?,
                          YulState.appendYulLog, IRState.appendYulLog, yulStateOfIR, h2]
                  | cons e rest =>
                      cases rest with
                      | nil =>
                          by_cases h3 : func = "log3" <;>
                            simp [applyYulLogCall?, IRGeneration.applyYulLogCall?,
                              YulState.appendYulLog, IRState.appendYulLog, yulStateOfIR, h3]
                      | cons f rest =>
                          cases rest with
                          | nil =>
                              by_cases h4 : func = "log4" <;>
                                simp [applyYulLogCall?, IRGeneration.applyYulLogCall?,
                                  YulState.appendYulLog, IRState.appendYulLog, yulStateOfIR, h4]
                          | cons _ _ =>
                              simp [applyYulLogCall?, IRGeneration.applyYulLogCall?]

private theorem execResultsAligned_log_call
    (selector : Nat) (irState : IRState) (func : String) (argVals : List Nat) :
    execResultsAligned selector
      (match IRGeneration.applyYulLogCall? irState func argVals with
      | some next => IRExecResult.continue next
      | none => IRExecResult.revert irState)
      (match applyYulLogCall? (yulStateOfIR selector irState) func argVals with
      | some next => YulExecResult.continue next
      | none => YulExecResult.revert (yulStateOfIR selector irState)) := by
  rw [applyYulLogCall?_aligned]
  cases IRGeneration.applyYulLogCall? irState func argVals <;>
    simp [execResultsAligned, statesAligned]

private theorem assign_equiv (selector : Nat) (fuel : Nat) (varName : String) (valueExpr : YulExpr)
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
      simp only [execIRStmtFuel, execIRStmt, execYulStmtFuel, legacyExecYulFuel]
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
          simp only [IRState.setVar, YulState.setVar]

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
  simpa only [hIR, hYul] using hStmts

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
  simpa only [hIR, hYul] using hStmt

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
          simp only [execIRStmtFuel, execIRStmt,
            execYulStmtFuel, legacyExecYulFuel, execResultsAligned, halign]
      · intro selector stmts irState yulState halign
        cases stmts <;>
          simp only [execIRStmtsFuel, execIRStmts,
            execYulStmtsFuel, legacyExecYulFuel, execResultsAligned, halign]
  | succ fuel ih =>
      rcases ih with ⟨ihStmt, ihStmts⟩
      constructor
      · intro selector stmt irState yulState halign
        unfold statesAligned at halign
        subst halign
        cases stmt with
        | comment _ =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | let_ name value =>
            exact assign_equiv selector (fuel + 1) name value irState
              (yulStateOfIR selector irState) rfl (by omega)
        | letMany _ _ =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | assign name value =>
            exact assign_equiv selector (fuel + 1) name value irState
              (yulStateOfIR selector irState) rfl (by omega)
        | «leave» =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | expr e =>
            cases e with
            | call func args =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, legacyExecYulFuel]
                -- Both sides match on (.call func args) against string literals.
                -- With `func` free, neither match tree reduces. Generalize so both
                -- sides share the same discriminant, then split.
                generalize YulExpr.call func args = disc
                split
                · -- sstore: inner match on slotExpr
                  split
                  · -- mappingSlot: match on 3 evals
                    simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                    split <;> simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq]
                  · -- non-mappingSlot: match on 2 evals
                    simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                    split <;> simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq]
                · -- mstore: match on 2 evals
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq]
                · -- tstore: match on 2 evals
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq]
                · -- stop
                  simp only [execResultsAligned, statesAligned, yulStateOfIR]
                · -- revert
                  simp only [execResultsAligned, statesAligned, yulStateOfIR]
                · -- return: match on 2 evals, then if on size = 32
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  repeat' split
                  all_goals simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq, not_true_eq_false, Bool.false_eq_true]
                · -- log call or generic call: match on log dispatch, then eval/log result
                  rename_i funcLog argsLog _ _ _ _ _ _
                  simp only [evalIRExpr_eq_evalYulExpr selector,
                    evalIRExprs_eq_evalYulExprs selector, yulStateOfIR] at *
                  split
                  · split
                    · rename_i values hargs
                      simpa [hargs] using
                        execResultsAligned_log_call selector irState _ values
                    · rename_i hargs
                      simp [hargs, execResultsAligned, statesAligned, yulStateOfIR]
                  · split <;>
                      simp_all only [execResultsAligned, statesAligned, yulStateOfIR,
                        and_self, and_true, true_and, Option.some.injEq]
                · -- non-call catch-all: match on eval of full expr
                  simp only [evalIRExpr_eq_evalYulExpr selector, yulStateOfIR] at *
                  split <;> simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, Option.some.injEq]
            | lit val =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, legacyExecYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | hex val =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, legacyExecYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | str val =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, legacyExecYulFuel, evalIRExpr, evalYulExpr,
                  execResultsAligned, statesAligned, yulStateOfIR]
            | ident val =>
                simp only [execIRStmtFuel, execIRStmt,
                  execYulStmtFuel, legacyExecYulFuel, evalIRExpr, evalYulExpr,
                  IRState.getVar, YulState.getVar,
                  execResultsAligned, statesAligned, yulStateOfIR]
                cases hfind : List.find? (fun x => x.1 == val) irState.vars <;>
                  simp only [Option.map]
        | if_ cond body =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel]
            rw [evalIRExpr_eq_evalYulExpr]
            cases hcond : evalYulExpr (yulStateOfIR selector irState) cond with
            | none =>
                simp only [execResultsAligned, statesAligned, yulStateOfIR]
            | some c =>
                simp only []
                by_cases hc : c = 0
                · subst hc
                  simp only [ne_eq, not_true_eq_false, ite_false, ite_true, execResultsAligned, statesAligned, yulStateOfIR]
                · simp only [hc, ne_eq, ite_false, decide_false, not_false_eq_true, ite_true]
                  exact ihStmts selector body irState (yulStateOfIR selector irState) rfl
        | «switch» expr cases defaultCase =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel, beq_eq_decide, yulStateOfIR]
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
                  simpa only [yulStateOfIR] using hEval
                simp only [hEval', execResultsAligned, statesAligned, yulStateOfIR]
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
                  simpa only [yulStateOfIR] using hEval
                simp only [hEval']
                cases hFind : cases.find? (fun x => decide (x.fst = v)) with
                | none =>
                    have hFind' :
                        List.find? (fun x => decide (x.fst = v)) cases = none := hFind
                    simp only []
                    cases defaultCase with
                    | none =>
                        simp only [execResultsAligned, statesAligned, yulStateOfIR]
                    | some body =>
                        simpa only [hEval', hFind', execYulStmtsFuel, legacyExecYulFuel] using
                          ihStmts selector body irState (yulStateOfIR selector irState) rfl
                | some pair =>
                    cases pair with
                    | mk _ body =>
                        simpa only [hEval', hFind, execYulStmtsFuel, execIRStmtsFuel, legacyExecYulFuel] using
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
                      simpa only [execResultsAligned, hIRInit, hYulInit] using hInit
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
                          simpa only [hCondIR] using hCondEq
                        simp only [yulStateOfIR] at hCondYul
                        simp only [hIRInit, hCondIR, hCondYul,
                          execResultsAligned, statesAligned, yulStateOfIR]
                    | some v =>
                        have hCondYul : evalYulExpr (yulStateOfIR selector irAfterInit) cond = some v := by
                          symm
                          simpa only [hCondIR] using hCondEq
                        by_cases hv : v = 0
                        · subst hv
                          simp only [yulStateOfIR] at hCondYul
                          simp only [hIRInit, hCondIR, hCondYul, ne_eq, not_true_eq_false, ite_false, ite_true,
                            execResultsAligned, statesAligned, yulStateOfIR]
                        · have hBody :=
                            ihStmts selector body irAfterInit (yulStateOfIR selector irAfterInit) rfl
                          cases hIRBody : execIRStmtsFuel fuel irAfterInit body with
                          | «continue» irAfterBody =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «continue» yulAfterBody =>
                                  have hAlignedBody : statesAligned selector irAfterBody yulAfterBody := by
                                    simpa only [execResultsAligned, hIRBody, hYulBody] using hBody
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
                                            simpa only [execResultsAligned, hIRPost, hYulPost] using hPost
                                          unfold statesAligned at hAlignedPost
                                          subst hAlignedPost
                                          simp only [yulStateOfIR] at *
                                          have hRec := ihStmt selector (.for_ [] cond post body)
                                              irAfterPost (yulStateOfIR selector irAfterPost) rfl
                                          simp_all only [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                                            execYulStmtFuel, execYulStmtsFuel, yulStateOfIR, and_self, and_true, true_and,
                                            ne_eq, ite_true, ite_false, not_false_eq_true, not_true_eq_false]
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                  | «return» _ _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «return» _ _ =>
                                          simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, ne_eq, ite_true, ite_false, not_false_eq_true, not_true_eq_false]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                  | «stop» _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «stop» _ =>
                                          simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, ne_eq, ite_true, ite_false, not_false_eq_true, not_true_eq_false]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «revert» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                  | «revert» _ =>
                                      cases hYulPost : execYulStmtsFuel fuel (yulStateOfIR selector irAfterBody) post with
                                      | «revert» _ =>
                                          simp_all only [execResultsAligned, statesAligned, yulStateOfIR, and_self, and_true, true_and, ne_eq, ite_true, ite_false, not_false_eq_true, not_true_eq_false]
                                      | «continue» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «return» _ _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                                      | «stop» _ =>
                                          exact False.elim (stmts_align_contra (hStmts := hPost) (hIR := hIRPost) (hYul := hYulPost) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                          | «return» _ _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «return» _ _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp only [hIRInit, hCondIR, hCondYul, hv, ite_true, ite_false, decide_true, decide_false, ne_eq, not_false_eq_true,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody, and_self]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                          | «stop» _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «stop» _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp only [hIRInit, hCondIR, hCondYul, hv, ite_true, ite_false, decide_true, decide_false, ne_eq, not_false_eq_true,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody, and_self]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «revert» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                          | «revert» _ =>
                              cases hYulBody : execYulStmtsFuel fuel (yulStateOfIR selector irAfterInit) body with
                              | «revert» _ =>
                                  simp only [yulStateOfIR] at hCondYul hYulBody hBody
                                  simp only [execResultsAligned, hIRBody, hYulBody,
                                    statesAligned, yulStateOfIR] at hBody
                                  simp only [hIRInit, hCondIR, hCondYul, hv, ite_true, ite_false, decide_true, decide_false, ne_eq, not_false_eq_true,
                                    hIRBody, hYulBody, execResultsAligned,
                                    statesAligned, yulStateOfIR, hBody, and_self]
                              | «continue» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «return» _ _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                              | «stop» _ =>
                                  exact False.elim (stmts_align_contra (hStmts := hBody) (hIR := hIRBody) (hYul := hYulBody) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
            | «return» retVal retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.return retVal retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa only [hIRInit] using hInit
                    simp_all only [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR,
                      and_self, and_true, true_and]
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
            | «stop» retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.stop retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa only [hIRInit] using hInit
                    simp_all only [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR,
                      and_self, and_true, true_and]
                | «revert» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
            | «revert» retState =>
                cases hYulInit : execYulStmtsFuel fuel (yulStateOfIR selector irState) init with
                | «continue» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    exact False.elim (stmts_align_contra (hStmts := hInit) (hIR := hIRInit) (hYul := hYulInit) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    have hInit' :
                        execResultsAligned selector (IRExecResult.revert retState)
                          (execYulStmtsFuel fuel (yulStateOfIR selector irState) init) := by
                      simpa only [hIRInit] using hInit
                    simp_all only [execIRStmt_equiv_execYulStmt_goal, execIRStmtFuel,
                      execYulStmtFuel, execYulStmtsFuel, execResultsAligned, statesAligned, yulStateOfIR,
                      and_self, and_true, true_and]
        | block stmts =>
            simpa only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel] using
              ihStmts selector stmts irState (yulStateOfIR selector irState) rfl
        | funcDef _ _ _ _ =>
            simp only [execIRStmtFuel, execIRStmt,
              execYulStmtFuel, legacyExecYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
      · intro selector stmts irState yulState halign
        unfold statesAligned at halign
        subst halign
        cases stmts with
        | nil =>
            simp only [execIRStmtsFuel, execIRStmts,
              execYulStmtsFuel, legacyExecYulFuel, execResultsAligned, statesAligned, yulStateOfIR]
        | cons stmt rest =>
            have hStmt := ihStmt selector stmt irState (yulStateOfIR selector irState) rfl
            cases hIR : execIRStmtFuel fuel irState stmt with
            | «continue» ir' =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «continue» y' =>
                    have hAligned' : statesAligned selector ir' y' := by
                      simpa only [execResultsAligned, hIR, hYul] using hStmt
                    have hRest := ihStmts selector rest ir' y' hAligned'
                    simpa only [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, hIR, hYul] using hRest
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
            | «return» _ _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «return» _ _ =>
                    simpa only [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
            | «stop» _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «stop» _ =>
                    simpa only [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «revert» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
            | «revert» _ =>
                cases hYul : execYulStmtFuel fuel (yulStateOfIR selector irState) stmt with
                | «revert» _ =>
                    simpa only [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execIRStmts,
                      execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
                | «continue» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «return» _ _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))
                | «stop» _ =>
                    exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp only [execResultsAligned, not_false_eq_true]))

private theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState := by
  intro selector fuel stmt irState yulState
  exact (stmt_and_stmts_equiv fuel).1 selector stmt irState yulState

private theorem conditional_equiv (selector : Nat) (fuel : Nat)
    (condExpr : YulExpr) (body : List YulStmt)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.if_ condExpr body))
      (execYulStmtFuel fuel yulState (YulStmt.if_ condExpr body)) := by
  simpa only [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.if_ condExpr body) irState yulState halign)

private theorem return_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "return" [offsetExpr, sizeExpr]))) := by
  simpa only [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "return" [offsetExpr, sizeExpr])) irState yulState halign)

private theorem revert_equiv (selector : Nat) (fuel : Nat)
    (offsetExpr sizeExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr]))) := by
  simpa only [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "revert" [offsetExpr, sizeExpr])) irState yulState halign)

private theorem storageStore_equiv (selector : Nat) (fuel : Nat)
    (slotExpr valExpr : YulExpr)
    (irState : IRState) (yulState : YulState)
    (halign : statesAligned selector irState yulState)
    (_hfuel : fuel > 0) :
    execResultsAligned selector
      (execIRStmtFuel fuel irState (YulStmt.expr (.call "sstore" [slotExpr, valExpr])))
      (execYulStmtFuel fuel yulState (YulStmt.expr (.call "sstore" [slotExpr, valExpr]))) := by
  simpa only [execIRStmt_equiv_execYulStmt_goal] using
    (all_stmts_equiv selector fuel (YulStmt.expr (.call "sstore" [slotExpr, valExpr])) irState yulState halign)


end Compiler.Proofs.YulGeneration
