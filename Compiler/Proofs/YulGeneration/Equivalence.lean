import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.IRFuel
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Yul

/-! ## IR ↔ Yul State Alignment -/

def yulStateOfIR (_selector : Nat) (state : IRState) : YulState :=
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

def statesAligned (selector : Nat) (ir : IRState) (yul : YulState) : Prop :=
  yul = yulStateOfIR selector ir

/- ## Layer 3 Equivalence Scaffolding

These statements capture the generic proof shape for IR → Yul equivalence.
They are intentionally parameterized so contract-level results become
mechanical instantiations once the instruction-level lemmas are proven.
-/

def execResultsAligned (selector : Nat) : IRExecResult → YulExecResult → Prop
  | .continue ir, .continue yul => statesAligned selector ir yul
  | .return v ir, .return v' yul => v = v' ∧ statesAligned selector ir yul
  | .stop ir, .stop yul => statesAligned selector ir yul
  | .revert ir, .revert yul => statesAligned selector ir yul
  | _, _ => False

/-- Results match when success, return value, and storage/mapping functions agree. -/
def resultsMatch (ir : IRResult) (yul : YulResult) : Prop :=
  ir.success = yul.success ∧
  ir.returnValue = yul.returnValue ∧
  (∀ slot, ir.finalStorage slot = yul.finalStorage slot) ∧
  (∀ base key, ir.finalMappings base key = yul.finalMappings base key) ∧
  ir.events = yul.events

private def irResultOfExecWithRollback (rollback : IRState) : IRExecResult → IRResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

/-- Interpret a function body starting from an aligned IR-derived state. -/
private noncomputable def interpretYulBodyFromState
    (fn : IRFunction) (selector : Nat) (state rollback : IRState) : YulResult :=
  let yulState := yulStateOfIR selector state
  let yulRollback := yulStateOfIR selector rollback
  yulResultOfExecWithRollback yulRollback (execYulStmts yulState fn.body)

private theorem resultsMatch_of_execResultsAligned
    (selector : Nat) (rollbackIR : IRState) (rollbackYul : YulState)
    (hAligned : statesAligned selector rollbackIR rollbackYul) :
    ∀ irExec yulExec,
      execResultsAligned selector irExec yulExec →
      resultsMatch (irResultOfExecWithRollback rollbackIR irExec)
        (yulResultOfExecWithRollback rollbackYul yulExec) := by
  intro irExec yulExec hExec
  cases irExec <;> cases yulExec
  · -- continue / continue
    cases hExec
    simp [irResultOfExecWithRollback, yulResultOfExecWithRollback, resultsMatch,
      yulStateOfIR]
  · -- continue / return
    cases hExec
  · -- continue / stop
    cases hExec
  · -- continue / revert
    cases hExec
  · -- return / continue
    cases hExec
  · -- return / return
    rcases hExec with ⟨hVal, hAligned'⟩
    cases hAligned'
    simp [irResultOfExecWithRollback, yulResultOfExecWithRollback, resultsMatch,
      yulStateOfIR, hVal]
  · -- return / stop
    cases hExec
  · -- return / revert
    cases hExec
  · -- stop / continue
    cases hExec
  · -- stop / return
    cases hExec
  · -- stop / stop
    cases hExec
    simp [irResultOfExecWithRollback, yulResultOfExecWithRollback, resultsMatch,
      yulStateOfIR]
  · -- stop / revert
    cases hExec
  · -- revert / continue
    cases hExec
  · -- revert / return
    cases hExec
  · -- revert / stop
    cases hExec
  · -- revert / revert
    cases hExec
    cases hAligned
    simp [irResultOfExecWithRollback, yulResultOfExecWithRollback, resultsMatch,
      yulStateOfIR]

/-! ## Generic Layer 3 Lemmas (Fuel-Agnostic)

These lemmas lift instruction-level equivalence to sequences and function
bodies. They do not assume any specific instruction equivalence proof;
instead, they require it as a parameter and then compose it.
-/

private theorem statesAligned_refl (selector : Nat) (state : IRState) :
    statesAligned selector state (yulStateOfIR selector state) := by
  rfl

/-! ## Fuel-Parametric Sequencing Lemmas

These unfolding lemmas expose how `execYulStmtsFuel` consumes one unit of
fuel before executing the first statement. They are intended as building
blocks for the generic sequence equivalence proof.
-/

private theorem execYulStmtsFuel_nil (fuel : Nat) (state : YulState) :
    execYulStmtsFuel fuel state [] = .continue state := by
  cases fuel <;> rfl

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

/-- Instruction-level equivalence goal: single IR statement matches Yul statement (fuel-parametric). -/
def execIRStmt_equiv_execYulStmt_goal
    (selector : Nat) (fuel : Nat) (stmt : YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmtFuel fuel irState stmt) (execYulStmtFuel fuel yulState stmt)

/-- Sequence/program equivalence goal: statement lists compose under alignment (fuel-parametric). -/
def execIRStmts_equiv_execYulStmts_goal
    (selector : Nat) (fuel : Nat) (stmts : List YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmtsFuel fuel irState stmts) (execYulStmtsFuel fuel yulState stmts)

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

private def ir_yul_function_equiv_fuel_goal
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState) : Prop :=
  resultsMatch
    (execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState)
    (interpretYulBodyFromState fn selector
      (fn.params.zip args |>.foldl
        (fun s (p, v) => s.setVar p.name v)
        initialState)
      initialState)


/-! ## Generic Sequence Equivalence

This lemma lifts statement-level equivalence to statement lists, parameterized
by the fuel used for Yul execution. It is intentionally fuel-parametric so
later proofs can specialize to the compiler-chosen fuel without re-proving the
composition logic.
-/

private theorem execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector fuel stmts irState yulState,
      execIRStmts_equiv_execYulStmts_goal selector fuel stmts irState yulState := by
  intro selector fuel stmts irState yulState hAligned
  revert fuel irState yulState hAligned
  induction stmts with
  | nil =>
      intro fuel irState yulState hAligned
      simp [execIRStmtsFuel, execIRStmts,
        execYulStmtsFuel_nil, execResultsAligned, hAligned]
  | cons stmt rest ih =>
      intro fuel irState yulState hAligned
      cases fuel with
      | zero =>
          simp [execIRStmtsFuel, execIRStmts,
            execYulStmtsFuel, legacyExecYulFuel, execResultsAligned, hAligned]
      | succ fuel =>
          have hStmt := stmt_equiv selector fuel stmt irState yulState hAligned
          cases hIR : execIRStmtFuel fuel irState stmt with
          | «continue» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «continue» y' =>
                  have hAligned' : statesAligned selector ir' y' := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  have hRest := ih (irState := ir') (yulState := y') (fuel := fuel) hAligned'
                  simpa [execIRStmtsFuel, execIRStmts, execYulStmtsFuel_cons, hIR, hYul] using hRest
              | «return» v y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «stop» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «revert» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
          | «return» v ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «return» v' y' =>
                  simpa [execIRStmtsFuel, execIRStmts, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «stop» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «revert» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
          | «stop» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «stop» y' =>
                  simpa [execIRStmtsFuel, execIRStmts, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «return» v y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «revert» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
          | «revert» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «revert» y' =>
                  simpa [execIRStmtsFuel, execIRStmts, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «return» v y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))
              | «stop» y' =>
                  exact False.elim (stmt_align_contra (hStmt := hStmt) (hIR := hIR) (hYul := hYul) (by simp [execResultsAligned]))

private theorem execIRStmtsFuel_equiv_execYulStmts_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector stmts irState yulState,
      statesAligned selector irState yulState →
      execResultsAligned selector
        (execIRStmtsFuel (sizeOf stmts + 1) irState stmts)
        (execYulStmts yulState stmts) := by
  intro selector stmts irState yulState hAligned
  have hFuel :=
    execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv stmt_equiv
      selector (sizeOf stmts + 1) stmts irState yulState hAligned
  simpa [execYulStmts] using hFuel

private theorem execIRFunctionFuel_equiv_interpretYulBodyFromState_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector fn args initialState,
      resultsMatch
        (execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState)
        (interpretYulBodyFromState fn selector
          (fn.params.zip args |>.foldl
            (fun s (p, v) => s.setVar p.name v)
            initialState)
          initialState) := by
  intro selector fn args initialState
  let stateWithParams :=
    fn.params.zip args |>.foldl
      (fun s (p, v) => s.setVar p.name v)
      initialState
  have hAligned : statesAligned selector stateWithParams (yulStateOfIR selector stateWithParams) := by
    rfl
  have hExec :=
    execIRStmtsFuel_equiv_execYulStmts_of_stmt_equiv stmt_equiv
      selector fn.body stateWithParams (yulStateOfIR selector stateWithParams) hAligned
  have hRollback : statesAligned selector initialState (yulStateOfIR selector initialState) := by
    rfl
  simpa [execIRFunctionFuel, interpretYulBodyFromState, stateWithParams] using
    (resultsMatch_of_execResultsAligned selector initialState
      (yulStateOfIR selector initialState) hRollback _ _ hExec)

private theorem ir_yul_function_equiv_fuel_goal_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector fn args initialState,
      ir_yul_function_equiv_fuel_goal fn selector args initialState := by
  intro selector fn args initialState
  simpa [ir_yul_function_equiv_fuel_goal] using
    (execIRFunctionFuel_equiv_interpretYulBodyFromState_of_stmt_equiv stmt_equiv
      selector fn args initialState)

private theorem ir_yul_function_equiv_from_state_of_fuel_goal
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState)
    (hFuel :
      execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState =
        execIRFunction fn args initialState)
    (hFuelGoal : ir_yul_function_equiv_fuel_goal fn selector args initialState) :
    resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        initialState) := by
  simpa [ir_yul_function_equiv_fuel_goal, hFuel] using hFuelGoal

private theorem ir_yul_function_equiv_from_state_of_fuel_goal_and_adequacy
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState)
    (hAdequacy : execIRFunctionFuel_adequate_goal fn args initialState)
    (hFuelGoal : ir_yul_function_equiv_fuel_goal fn selector args initialState) :
    resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        initialState) := by
  apply ir_yul_function_equiv_from_state_of_fuel_goal
  · simpa [execIRFunctionFuel_adequate_goal] using hAdequacy
  · exact hFuelGoal

private theorem ir_yul_function_equiv_from_state_of_stmt_equiv_and_adequacy
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState)
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState)
    (hAdequacy : execIRFunctionFuel_adequate_goal fn args initialState) :
    resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        initialState) := by
  have hFuelGoal :=
    ir_yul_function_equiv_fuel_goal_of_stmt_equiv stmt_equiv
      selector fn args initialState
  exact
    ir_yul_function_equiv_from_state_of_fuel_goal_and_adequacy
      fn selector args initialState hAdequacy hFuelGoal

/-- Direct function-level equivalence without an explicit adequacy hypothesis.

Since `execIRFunctionFuel` and `execIRFunction` are definitionally equal
(fuel adequacy is `rfl`), the adequacy hypothesis is always trivially
dischargeable. This theorem composes `stmt_equiv` with the internal
adequacy proof, eliminating the need for callers to supply it. -/
private theorem ir_yul_function_equiv_from_state_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState)
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState) :
    resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        initialState) :=
  ir_yul_function_equiv_from_state_of_stmt_equiv_and_adequacy
    stmt_equiv fn selector args initialState
    (execIRFunctionFuel_adequate fn args initialState)

end Compiler.Proofs.YulGeneration
