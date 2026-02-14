import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Yul

set_option allowUnsafeReducibility true in
attribute [local reducible] execIRStmt execIRStmts

/-! ## IR ↔ Yul State Alignment -/

def yulStateOfIR (selector : Nat) (state : IRState) : YulState :=
  { vars := state.vars
    storage := state.storage
    mappings := state.mappings
    memory := state.memory
    calldata := state.calldata
    selector := selector
    returnValue := state.returnValue
    sender := state.sender }

def statesAligned (selector : Nat) (ir : IRState) (yul : YulState) : Prop :=
  yul = yulStateOfIR selector ir

/-! ## Bridging IR and Yul Semantics

These helpers wire IR-level execution to Yul runtime execution so we can
compare results directly in smoke tests.
-/

noncomputable def interpretYulFromIR (contract : IRContract) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime (Compiler.emitYul contract).runtimeCode yulTx state.storage state.mappings

/-- Interpret just a function body as Yul runtime code. -/
noncomputable def interpretYulBody (fn : IRFunction) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime fn.body yulTx state.storage state.mappings

/-- Interpret a function body starting from an aligned IR-derived state. -/
def resultsMatchOn (slots : List Nat) (mappingKeys : List (Nat × Nat))
    (ir : IRResult) (yul : YulResult) : Bool :=
  ir.success == yul.success &&
  ir.returnValue == yul.returnValue &&
  slots.all (fun slot => ir.finalStorage slot == yul.finalStorage slot) &&
  mappingKeys.all (fun (base, key) => ir.finalMappings base key == yul.finalMappings base key)

/-! ## Layer 3 Equivalence Scaffolding

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
  (∀ base key, ir.finalMappings base key = yul.finalMappings base key)

def irResultOfExecWithRollback (rollback : IRState) : IRExecResult → IRResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := rollback.mappings }

def yulResultOfExecWithRollback (rollback : YulState) : YulExecResult → YulResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := rollback.mappings }

/-- Interpret a function body starting from an aligned IR-derived state. -/
noncomputable def interpretYulBodyFromState
    (fn : IRFunction) (selector : Nat) (state rollback : IRState) : YulResult :=
  let yulState := yulStateOfIR selector state
  let yulRollback := yulStateOfIR selector rollback
  yulResultOfExecWithRollback yulRollback (execYulStmts yulState fn.body)

theorem resultsMatch_of_execResultsAligned
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
      statesAligned, yulStateOfIR]
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
      statesAligned, yulStateOfIR]
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

/-- Instruction-level equivalence goal: single IR statement matches Yul statement (fuel-parametric). -/
def execIRStmt_equiv_execYulStmt_goal
    (selector : Nat) (fuel : Nat) (stmt : YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmt irState stmt) (execYulStmtFuel fuel yulState stmt)

/-- Generic function equivalence goal: holds for any IR function and its compiled Yul body. -/
def ir_yul_function_equiv_goal
    (fn : IRFunction) (tx : IRTransaction) (state : IRState) : Prop :=
    tx.functionSelector < selectorModulus →
    resultsMatch
      (execIRFunction fn tx.args { state with sender := tx.sender, calldata := tx.args })
      (interpretYulBody fn tx { state with sender := tx.sender, calldata := tx.args })

theorem ir_yul_function_equiv_goal_of_resultsMatch
    (fn : IRFunction) (tx : IRTransaction) (state : IRState)
    (hMatch :
      resultsMatch
        (execIRFunction fn tx.args { state with sender := tx.sender, calldata := tx.args })
        (interpretYulBody fn tx { state with sender := tx.sender, calldata := tx.args })) :
    ir_yul_function_equiv_goal fn tx state := by
  intro _
  simpa [ir_yul_function_equiv_goal] using hMatch

/-! ## Generic Layer 3 Lemmas (Fuel-Agnostic)

These lemmas lift instruction-level equivalence to sequences and function
bodies. They do not assume any specific instruction equivalence proof;
instead, they require it as a parameter and then compose it.
-/

theorem statesAligned_refl (selector : Nat) (state : IRState) :
    statesAligned selector state (yulStateOfIR selector state) := by
  rfl

/-! ## Fuel-Parametric Sequencing Lemmas

These unfolding lemmas expose how `execYulStmtsFuel` consumes one unit of
fuel before executing the first statement. They are intended as building
blocks for the generic sequence equivalence proof.
-/

theorem execYulStmtsFuel_nil (fuel : Nat) (state : YulState) :
    execYulStmtsFuel fuel state [] = .continue state := by
  cases fuel <;> rfl

theorem execYulStmtsFuel_cons
    (fuel : Nat) (state : YulState) (stmt : YulStmt) (rest : List YulStmt) :
    execYulStmtsFuel (Nat.succ fuel) state (stmt :: rest) =
      match execYulStmtFuel fuel state stmt with
      | .continue s' => execYulStmtsFuel fuel s' rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := by
  rfl

/-! ## Fuel-Parametric IR Statement Execution

This is the key missing piece! We need a fuel-parametric version of `execIRStmt`
to make it provable. The `partial` version in IRInterpreter.lean cannot be
reasoned about in proofs.

These must be defined as mutual functions since they call each other.
-/

mutual
  def execIRStmtFuel : Nat → IRState → YulStmt → IRExecResult
    | 0, state, _ => .revert state  -- Out of fuel
    | Nat.succ fuel, state, stmt =>
        match stmt with
        | .comment _ => .continue state
        | .let_ name value =>
            match evalIRExpr state value with
            | some v => .continue (state.setVar name v)
            | none => .revert state
        | .assign name value =>
            match evalIRExpr state value with
            | some v => .continue (state.setVar name v)
            | none => .revert state
        | .expr e =>
            match e with
            | .call "sstore" [slotExpr, valExpr] =>
                match slotExpr with
                | .call "mappingSlot" [baseExpr, keyExpr] =>
                    match evalIRExpr state baseExpr, evalIRExpr state keyExpr, evalIRExpr state valExpr with
                    | some baseSlot, some key, some val =>
                        .continue {
                          state with
                          mappings := fun b k =>
                            if b = baseSlot ∧ k = key then val else state.mappings b k
                        }
                    | _, _, _ => .revert state
                | _ =>
                    match evalIRExpr state slotExpr, evalIRExpr state valExpr with
                    | some slot, some val =>
                      match decodeMappingSlot slot with
                      | some (baseSlot, key) =>
                          .continue {
                            state with
                            mappings := fun b k =>
                              if b = baseSlot ∧ k = key then val else state.mappings b k
                          }
                      | none =>
                          .continue { state with storage := fun s => if s = slot then val else state.storage s }
                    | _, _ => .revert state
            | .call "mstore" [offsetExpr, valExpr] =>
                match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
                | some offset, some val =>
                  .continue { state with memory := fun o => if o = offset then val else state.memory o }
                | _, _ => .revert state
            | .call "stop" [] => .stop state
            | .call "revert" _ => .revert state
            | .call "return" [offsetExpr, sizeExpr] =>
                match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
                | some offset, some size =>
                  if size = 32 then
                    .return (state.memory offset) state
                  else
                    .return 0 state
                | _, _ => .revert state
            | _ => .continue state  -- Other expressions are no-ops
        | .if_ cond body =>
            match evalIRExpr state cond with
            | some c => if c ≠ 0 then execIRStmtsFuel fuel state body else .continue state
            | none => .revert state
        | .switch expr cases default =>
            match evalIRExpr state expr with
            | some v =>
              match cases.find? (·.1 == v) with
              | some (_, body) => execIRStmtsFuel fuel state body
              | none =>
                match default with
                | some body => execIRStmtsFuel fuel state body
                | none => .continue state
            | none => .revert state
        | .block stmts => execIRStmtsFuel fuel state stmts
        | .funcDef _ _ _ _ => .continue state

  def execIRStmtsFuel (fuel : Nat) (state : IRState) (stmts : List YulStmt) : IRExecResult :=
    match stmts with
    | [] => .continue state
    | stmt :: rest =>
        match fuel with
        | 0 => .revert state
        | Nat.succ fuel =>
            match execIRStmtFuel fuel state stmt with
            | .continue s' => execIRStmtsFuel fuel s' rest
            | .return v s => .return v s
            | .stop s => .stop s
            | .revert s => .revert s
end

/-- Sequence/program equivalence goal: statement lists compose under alignment (fuel-parametric). -/
def execIRStmts_equiv_execYulStmts_goal
    (selector : Nat) (fuel : Nat) (stmts : List YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmtsFuel fuel irState stmts) (execYulStmtsFuel fuel yulState stmts)

theorem execIRStmtsFuel_nil (fuel : Nat) (state : IRState) :
    execIRStmtsFuel fuel state [] = .continue state := by
  simp [execIRStmtsFuel]

theorem execIRStmtsFuel_cons
    (fuel : Nat) (state : IRState) (stmt : YulStmt) (rest : List YulStmt) :
    execIRStmtsFuel (Nat.succ fuel) state (stmt :: rest) =
      match execIRStmtFuel fuel state stmt with
      | .continue s' => execIRStmtsFuel fuel s' rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := by
  -- The mutual definition unfolds directly
  rfl

def execIRFunctionFuel (fuel : Nat) (fn : IRFunction) (args : List Nat) (initialState : IRState) :
    IRResult :=
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState
  match execIRStmtsFuel fuel stateWithParams fn.body with
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := s.mappings }
  | .revert s =>
      { success := false
        returnValue := none
        finalStorage := initialState.storage
        finalMappings := initialState.mappings }

def ir_yul_function_equiv_fuel_goal
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

theorem execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
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
      simp [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execYulStmtsFuel_nil,
        execResultsAligned, hAligned]
  | cons stmt rest ih =>
      intro fuel irState yulState hAligned
      cases fuel with
      | zero =>
          simp [execIRStmts_equiv_execYulStmts_goal, execIRStmtsFuel, execYulStmtsFuel,
            execYulFuel, execResultsAligned, hAligned]
      | succ fuel =>
          have hStmt := stmt_equiv selector fuel stmt irState yulState hAligned
          cases hIR : execIRStmt irState stmt with
          | «continue» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «continue» y' =>
                  have hAligned' : statesAligned selector ir' y' := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  have hRest := ih (irState := ir') (yulState := y') (fuel := fuel) hAligned'
                  simpa [execIRStmtsFuel, execYulStmtsFuel_cons, hIR, hYul] using hRest
              | «return» v y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «stop» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «revert» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
          | «return» v ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «return» v' y' =>
                  simpa [execIRStmtsFuel, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «stop» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «revert» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
          | «stop» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «stop» y' =>
                  simpa [execIRStmtsFuel, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «return» v y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «revert» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
          | «revert» ir' =>
              cases hYul : execYulStmtFuel fuel yulState stmt with
              | «revert» y' =>
                  simpa [execIRStmtsFuel, execYulStmtsFuel_cons, execResultsAligned, hIR, hYul] using hStmt
              | «continue» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «return» v y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this
              | «stop» y' =>
                  have : False := by
                    simpa [execResultsAligned, hIR, hYul] using hStmt
                  cases this

theorem execIRStmtsFuel_equiv_execYulStmts_of_stmt_equiv
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

theorem execIRFunctionFuel_equiv_interpretYulBodyFromState_of_stmt_equiv
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

theorem ir_yul_function_equiv_fuel_goal_of_stmt_equiv
    (stmt_equiv :
      ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector fn args initialState,
      ir_yul_function_equiv_fuel_goal fn selector args initialState := by
  intro selector fn args initialState
  simpa [ir_yul_function_equiv_fuel_goal] using
    (execIRFunctionFuel_equiv_interpretYulBodyFromState_of_stmt_equiv stmt_equiv
      selector fn args initialState)

theorem execIRFunctionFuel_eq_execIRFunction
    (fn : IRFunction) (args : List Nat) (initialState : IRState)
    (hFuel :
      execIRStmtsFuel (sizeOf fn.body + 1)
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        fn.body =
      execIRStmts
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        fn.body) :
    execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState =
      execIRFunction fn args initialState := by
  dsimp [execIRFunctionFuel, execIRFunction]
  simp [hFuel]
  rfl

def execIRStmtsFuel_adequate_goal (state : IRState) (stmts : List YulStmt) : Prop :=
  execIRStmtsFuel (sizeOf stmts + 1) state stmts = execIRStmts state stmts

def execIRFunctionFuel_adequate_goal
    (fn : IRFunction) (args : List Nat) (initialState : IRState) : Prop :=
  execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState =
    execIRFunction fn args initialState

theorem execIRFunctionFuel_adequate_goal_of_stmts_adequate
    (fn : IRFunction) (args : List Nat) (initialState : IRState)
    (hAdequacy :
      execIRStmtsFuel_adequate_goal
        (fn.params.zip args |>.foldl
          (fun s (p, v) => s.setVar p.name v)
          initialState)
        fn.body) :
    execIRFunctionFuel_adequate_goal fn args initialState := by
  let stateWithParams :=
    fn.params.zip args |>.foldl
      (fun s (p, v) => s.setVar p.name v)
      initialState
  have hAdequacy' :
      execIRStmtsFuel (sizeOf fn.body + 1) stateWithParams fn.body =
        execIRStmts stateWithParams fn.body := by
    simpa [execIRStmtsFuel_adequate_goal, stateWithParams] using hAdequacy
  have h :
      execIRFunctionFuel (sizeOf fn.body + 1) fn args initialState =
        execIRFunction fn args initialState := by
    dsimp [execIRFunctionFuel, execIRFunction, stateWithParams]
    rw [hAdequacy']
    rfl
  simpa [execIRFunctionFuel_adequate_goal] using h

theorem ir_yul_function_equiv_from_state_of_fuel_goal
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

theorem ir_yul_function_equiv_from_state_of_fuel_goal_and_adequacy
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

theorem ir_yul_function_equiv_from_state_of_stmt_equiv_and_adequacy
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

end Compiler.Proofs.YulGeneration
