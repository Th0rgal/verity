import Compiler.CompilationModel.Dispatch
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.ParamLoading
import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.YulGeneration.Equivalence

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace Function

/-- Generic transaction well-formedness needed by the current param-loading proof:
the ABI-style calldata byte size must not wrap modulo the EVM word modulus. -/
def TxCalldataSizeFitsEvm (tx : IRTransaction) : Prop :=
  4 + tx.args.length * 32 < Compiler.Constants.evmModulus

def compiledFunctionIR
    (selector : Nat) (spec : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt) :
    IRFunction :=
  { name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := match returns with
      | [single] => single.toIRType
      | _ => IRType.unit
    payable := spec.isPayable
    body := genParamLoads spec.params ++ bodyStmts }

def prebindRawArgs (state : IRState) (params : List Param) : IRState :=
  (params.map Param.toIRParam).zip state.calldata |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    state

def rawArgBindings (params : List Param) (args : List Nat) : List (String × Nat) :=
  ((params.map Param.toIRParam).zip args).map (fun entry => (entry.1.name, entry.2))

@[simp] theorem prebindRawArgs_calldata (state : IRState) (params : List Param) :
    (prebindRawArgs state params).calldata = state.calldata := by
  unfold prebindRawArgs
  induction (params.map Param.toIRParam).zip state.calldata generalizing state with
  | nil =>
      rfl
  | cons entry rest ih =>
      simpa [List.foldl, IRState.setVar] using ih (state.setVar entry.1.name entry.2)

theorem prebindRawArgs_exact_rawArgBindings
    {state : IRState}
    {bindings0 : List (String × Nat)}
    (hexact : FunctionBody.bindingsExactlyMatchIRVars bindings0 state)
    (params : List Param) :
    FunctionBody.bindingsExactlyMatchIRVars
      ((rawArgBindings params state.calldata).foldl
        (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) bindings0)
      (prebindRawArgs state params) := by
  unfold prebindRawArgs rawArgBindings
  induction (List.zip (List.map Param.toIRParam params) state.calldata) generalizing bindings0 state with
  | nil =>
      simpa
  | cons entry rest ih =>
      have hstep :
          FunctionBody.bindingsExactlyMatchIRVars
            (SourceSemantics.bindValue bindings0 entry.1.name entry.2)
            (state.setVar entry.1.name entry.2) :=
        FunctionBody.bindingsExactlyMatchIRVars_setVar_bindValue hexact entry.1.name entry.2
      simpa [List.foldl, SourceSemantics.bindValue] using
        ih (bindings0 := SourceSemantics.bindValue bindings0 entry.1.name entry.2)
          (state := state.setVar entry.1.name entry.2) hstep

theorem rawArgBindings_names_of_length_le
    (params : List Param)
    (args : List Nat)
    (hlen : params.length ≤ args.length) :
    (rawArgBindings params args).map Prod.fst = params.map Param.name := by
  induction params generalizing args with
  | nil =>
      simp [rawArgBindings]
  | cons param rest ih =>
      cases args with
      | nil =>
          cases Nat.not_succ_le_zero _ hlen
      | cons arg restArgs =>
          have htail :
              (rawArgBindings rest restArgs).map Prod.fst = rest.map Param.name :=
            ih restArgs (Nat.le_of_succ_le_succ hlen)
          have hcons :
              param.toIRParam.name = param.name ∧
                (rawArgBindings rest restArgs).map Prod.fst = rest.map Param.name :=
            ⟨rfl, htail⟩
          simpa [rawArgBindings] using hcons

theorem rawArgBindings_names_of_bindSupportedParams
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    (rawArgBindings params args).map Prod.fst = bindings.map Prod.fst := by
  rw [rawArgBindings_names_of_length_le params args
    (ParamLoading.bindSupportedParams_some_length hbind)]
  symm
  exact ParamLoading.bindSupportedParams_names hbind

def execResultToIRResult (initialState : IRState) : IRExecResult → IRResult
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
        finalStorage := initialState.storage
        finalMappings := Compiler.Proofs.storageAsMappings initialState.storage
        events := initialState.events }

theorem compileFunctionSpec_ok_of_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (hvalidate : validateFunctionSpec spec = Except.ok ())
    (hreturns : functionReturns spec = Except.ok returns)
    (hbody :
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) spec.body = Except.ok bodyStmts) :
    compileFunctionSpec fields events errors selector spec =
      Except.ok (compiledFunctionIR selector spec returns bodyStmts) := by
  unfold CompilationModel.compileFunctionSpec
  rw [hvalidate, hreturns, hbody]
  rfl

theorem compileFunctionSpec_ok_params
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors selector spec = Except.ok irFn) :
    irFn.params = spec.params.map Param.toIRParam := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.params.map (·.name)) spec.body
      · rw [hvalidate, hreturns, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, hbody] at hcompile
        injection hcompile with hEq
        simpa using congrArg IRFunction.params hEq.symm

theorem compileFunctionSpec_ok_selector
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors selector spec = Except.ok irFn) :
    irFn.selector = selector := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.params.map (·.name)) spec.body
      · rw [hvalidate, hreturns, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, hbody] at hcompile
        injection hcompile with hEq
        simpa using congrArg IRFunction.selector hEq.symm

theorem compileFunctionSpec_ok_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors selector spec = Except.ok irFn) :
    ∃ returns bodyStmts,
      validateFunctionSpec spec = Except.ok () ∧
      functionReturns spec = Except.ok returns ∧
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) spec.body = Except.ok bodyStmts ∧
      irFn = compiledFunctionIR selector spec returns bodyStmts := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.params.map (·.name)) spec.body
      · rw [hvalidate, hreturns, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, hbody] at hcompile
        injection hcompile with hEq
        refine ⟨returns, bodyStmts, ?_⟩
        exact ⟨by simpa using hvalidate, by simpa using hreturns,
          by simpa using hbody, hEq.symm⟩

theorem exec_compiledFunctionIR_of_body
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hbody :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params ++ bodyStmts).length + 1)
        (compiledFunctionIR selector spec returns bodyStmts)
        state.calldata state =
      execResultToIRResult state tailResult := by
  let preboundState := prebindRawArgs state spec.params
  have hbind' :
      SourceSemantics.bindSupportedParams spec.params preboundState.calldata = some bindings := by
    simpa [preboundState] using hbind
  have hcalldataSizeFits' :
      4 + preboundState.calldata.length * 32 < Compiler.Constants.evmModulus := by
    simpa [preboundState] using hcalldataSizeFits
  have hprefix :
      execIRStmts ((genParamLoads spec.params ++ bodyStmts).length + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [preboundState, List.length_append, Nat.add_assoc] using
      ParamLoading.exec_genParamLoads_supported_then
        (state := preboundState)
        (params := spec.params)
        (bindings := bindings)
        (rest := bodyStmts)
        hsupported hcalldataSizeFits' hbind'
  have hprefix' :
      execIRStmts ((genParamLoads spec.params).length + bodyStmts.length + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [List.length_append, Nat.add_assoc] using hprefix
  have hprebound :
      List.foldl (fun s x => s.setVar x.1.name x.2) state
        ((List.map Param.toIRParam spec.params).zip state.calldata) = preboundState := by
    rfl
  unfold Compiler.Proofs.YulGeneration.execIRFunctionFuel
  unfold Compiler.Proofs.YulGeneration.execIRStmtsFuel
  simp [compiledFunctionIR, execResultToIRResult]
  rw [hprebound]
  rw [hprefix', hbody]
  rfl

theorem interpretFunction_eq_execResultToIRResult_of_body
    (model : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult)
    (rollback : IRState) (irResult : IRExecResult)
    (bindings : List (String × Nat))
    (hbind :
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult)
    (hrollbackStorage :
      rollback.storage =
        SourceSemantics.encodeStorage model
          (SourceSemantics.withTransactionContext initialWorld tx))
    (hrollbackEvents :
      rollback.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irResult) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execResultToIRResult rollback irResult) := by
  have hpack :=
    FunctionBody.stmtResultToSourceResult_matches_irExecResult
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
      (rollback := rollback)
      (sourceResult := sourceResult)
      (irResult := irResult)
      hrollbackStorage hrollbackEvents rfl hmatch
  simpa [SourceSemantics.interpretFunction, hbind, hsource,
    FunctionBody.stmtResultToSourceResult, FunctionBody.sourceResultMatchesIRResult,
    FunctionBody.irResultOfExecResult, execResultToIRResult] using hpack

theorem runtimeStateMatchesIR_applyBindingsToIRState
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (bindings : List (String × Nat)) :
    FunctionBody.runtimeStateMatchesIR fields runtime
      (ParamLoading.applyBindingsToIRState state bindings) := by
  induction bindings generalizing state with
  | nil =>
      simpa [ParamLoading.applyBindingsToIRState]
  | cons entry rest ih =>
      simpa [ParamLoading.applyBindingsToIRState, IRState.setVar] using
        ih (state := state.setVar entry.1 entry.2) hmatch

theorem runtimeStateMatchesIR_prebindRawArgs
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (params : List Param) :
    FunctionBody.runtimeStateMatchesIR fields runtime (prebindRawArgs state params) := by
  unfold prebindRawArgs
  induction (List.zip (List.map Param.toIRParam params) state.calldata) generalizing state with
  | nil =>
      simpa
  | cons entry rest ih =>
      simpa [List.foldl, IRState.setVar] using
        ih (state := state.setVar entry.1.name entry.2) hmatch

/-- TODO(#1510): discharge the remaining initial-state normalization gap between
source `withTransactionContext` values and the raw `IRTransaction` payload stored
in `initialIRStateForTx`. -/
axiom initialIRStateForTx_matches_runtime
    (model : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := [] }
      (FunctionBody.initialIRStateForTx model tx initialWorld)

/-- TODO(#1510): replace this temporary bridge with a proof that the ABI
parameter-loading prefix produces an IR variable environment exactly matching
the decoded source bindings. This is the first strategy-3 subgoal. -/
axiom supported_function_param_state_exact
    (state : IRState)
    (params : List Param)
    (bindings : List (String × Nat))
    (hinit : FunctionBody.bindingsExactlyMatchIRVars [] state)
    (hparamNamesNodup : (params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings)

/-- TODO(#1510): replace this temporary bridge with the generic body simulation
proof under the exact-state invariant produced by parameter loading. This is
the second strategy-3 subgoal after `supported_function_param_state_exact`. -/
axiom supported_function_body_correct_from_exact_state
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec

/-- TODO(#1510): replace this fuel-bridging axiom with a proof that the public
`execIRFunction` entrypoint is equivalent to the explicit fuel used by the
current body-level theorem for compiled supported functions. -/
axiom supported_function_execIRFunction_eq_fuel
    (model : CompilationModel)
    (selector : Nat)
    (fn : FunctionSpec)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hreturns : functionReturns fn = Except.ok returns) :
    execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld) =
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)

theorem compileFunctionSpec_correct_of_body
    (model : CompilationModel)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hcompile : compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hcompiled :=
    compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled with hirFn
  have hrollbackStorage :
      initialState.storage =
        SourceSemantics.encodeStorage model
          (SourceSemantics.withTransactionContext initialWorld tx) := by
    simpa [initialState, FunctionBody.initialIRStateForTx] using
      (FunctionBody.encodeStorage_withTransactionContext model initialWorld tx).symm
  have hrollbackEvents :
      initialState.events =
        SourceSemantics.encodeEvents
          (SourceSemantics.withTransactionContext initialWorld tx).events := by
    simp [initialState, FunctionBody.initialIRStateForTx]
  have hsourceMatch :=
    interpretFunction_eq_execResultToIRResult_of_body
      (model := model) (fn := fn) (tx := tx) (initialWorld := initialWorld)
      (sourceResult := sourceResult) (rollback := initialState) (irResult := irExec)
      (bindings := bindings) hbind hsource hrollbackStorage hrollbackEvents hmatch
  have hcompiledExec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) hparamsSupported hcalldataSizeFits hbind hbodyExec
  subst hirFn
  rw [hcompiledExec]
  simpa [initialState] using hsourceMatch

theorem compileFunctionSpec_correct_of_body_supported
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat))
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec
        (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors selector fn = Except.ok irFn)
    (hparamsSupported : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hsource :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult)
    (hbodyExec :
      execIRStmts (bodyStmts.length + 1)
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bodyStmts = irExec)
    (hmatch :
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads fn.params ++ bodyStmts).length + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields :=
    hSupported.normalizedFields
  have hbodyCompile' :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized] using hbodyCompile
  have hcompile' :
      compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn := by
    simpa [hnormalized] using hcompile
  simpa [hnormalized] using
    compileFunctionSpec_correct_of_body
      (model := model)
      (selector := selector)
      (fn := fn)
      (irFn := irFn)
      (returns := returns)
      (bodyStmts := bodyStmts)
      (tx := tx)
      (initialWorld := initialWorld)
      (sourceResult := sourceResult)
      (irExec := irExec)
      (bindings := bindings)
      hvalidate hreturns hbodyCompile' hcompile' hparamsSupported hcalldataSizeFits
      hbind hsource hbodyExec hmatch

theorem supported_function_correct
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hcompile :
      compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hSupported.selectorFunctionParamNamesNodup hfn
  have hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) :=
    supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hpreboundRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        (prebindRawArgs initialState fn.params) := by
    simpa [initialState] using
      runtimeStateMatchesIR_prebindRawArgs
        (state := initialState)
        (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
        (fields := SourceSemantics.effectiveFields model)
        (params := fn.params)
        (initialIRStateForTx_matches_runtime model tx initialWorld)
  have hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) :=
    runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  rcases supported_function_body_correct_from_exact_state
      model selectors hSupported hvalidateInputs fn selector returns bodyStmts tx initialWorld
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs initialState fn.params) bindings)
      bindings hfn hbodyCompile hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hfuel :=
    compileFunctionSpec_correct_of_body_supported
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (selector := selector)
    (fn := fn)
    (irFn := irFn)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (tx := tx)
    (initialWorld := initialWorld)
    (sourceResult := sourceResult)
    (irExec := irExec)
    (bindings := bindings)
    hvalidate hreturns
    (by simpa [hSupported.normalizedFields] using hbodyCompile)
    (by simpa [hSupported.normalizedFields] using hcompile)
    (hSupported.selectorFunctionParamsSupported hfn)
    hcalldataSizeFits hbind hsource hbodyExec hmatch
  rw [supported_function_execIRFunction_eq_fuel
    (model := model)
    (selector := selector)
    (fn := fn)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (irFn := irFn)
    (tx := tx)
    (initialWorld := initialWorld)
    hcompile hbodyCompile hreturns]
  exact hfuel

end Function

end Compiler.Proofs.IRGeneration
