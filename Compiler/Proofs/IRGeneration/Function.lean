import Compiler.CompilationModel.Dispatch
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.GenericInduction
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

/-- Source-side transaction context stores addresses as 160-bit values and the
remaining observed environment fields as `Uint256`s. The generic Layer-2 proof
therefore needs the IR transaction payload to already fit those bounds. -/
def TxContextNormalized (tx : IRTransaction) : Prop :=
  tx.sender < Compiler.Constants.addressModulus ∧
  tx.thisAddress < Compiler.Constants.addressModulus ∧
  tx.msgValue < Compiler.Constants.evmModulus ∧
  tx.blockTimestamp < Compiler.Constants.evmModulus ∧
  tx.blockNumber < Compiler.Constants.evmModulus ∧
  tx.chainId < Compiler.Constants.evmModulus

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

private theorem yulStmtList_length_le_sizeOf : (stmts : List YulStmt) → stmts.length ≤ sizeOf stmts
  | [] => by simp
  | _ :: rest => by
      have hrest := yulStmtList_length_le_sizeOf rest
      simp
      omega

private theorem compiledFunctionIR_body_length_le_sizeOf
    (selector : Nat) (spec : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt) :
    (compiledFunctionIR selector spec returns bodyStmts).body.length + 1 ≤
      sizeOf (compiledFunctionIR selector spec returns bodyStmts).body + 1 := by
  simpa [compiledFunctionIR] using Nat.add_le_add_right
    (yulStmtList_length_le_sizeOf (genParamLoads spec.params ++ bodyStmts)) 1

private theorem yulStmtList_extraFuel_append_ge
    (pre body : List YulStmt) :
    sizeOf (pre ++ body) - (pre ++ body).length ≥ sizeOf body - body.length := by
  induction pre with
  | nil =>
      simp
  | cons stmt rest ih =>
      simp [List.length_append] at ih ⊢
      omega

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

theorem exec_compiledFunctionIR_of_body_extraFuel
    (state : IRState) (selector : Nat) (spec : FunctionSpec)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (bindings : List (String × Nat)) (tailResult : IRExecResult)
    (extraFuel : Nat)
    (hsupported : ∀ param ∈ spec.params, SupportedExternalParamType param.ty)
    (hcalldataSizeFits : 4 + state.calldata.length * 32 < Compiler.Constants.evmModulus)
    (hbind : SourceSemantics.bindSupportedParams spec.params state.calldata = some bindings)
    (hbody :
      execIRStmts (bodyStmts.length + extraFuel + 1)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state spec.params) bindings)
        bodyStmts = tailResult) :
    Compiler.Proofs.YulGeneration.execIRFunctionFuel
        ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1)
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
      execIRStmts ((genParamLoads spec.params ++ bodyStmts).length + extraFuel + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + extraFuel + 1)
          (ParamLoading.applyBindingsToIRState preboundState bindings)
          bodyStmts := by
    simpa [preboundState, List.length_append, Nat.add_assoc] using
      ParamLoading.exec_genParamLoads_supported_then_extraFuel
        (state := preboundState)
        (params := spec.params)
        (bindings := bindings)
        (rest := bodyStmts)
        (extraFuel := extraFuel)
        hsupported hcalldataSizeFits' hbind'
  have hprefix' :
      execIRStmts ((genParamLoads spec.params).length + bodyStmts.length + extraFuel + 1) preboundState
          (genParamLoads spec.params ++ bodyStmts) =
        execIRStmts (bodyStmts.length + extraFuel + 1)
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

/-- Folding `bindValue` over names that never mention `queryName` leaves its
lookup unchanged. -/
private theorem lookupBinding?_foldl_bindValue_not_mem
    (bindings : List (String × Nat))
    (init : List (String × Nat))
    (queryName : String)
    (hnotmem : queryName ∉ bindings.map Prod.fst) :
    FunctionBody.lookupBinding?
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) init)
      queryName =
    FunctionBody.lookupBinding? init queryName := by
  induction bindings generalizing init with
  | nil =>
      simp
  | cons entry rest ih =>
      have hqueryNe : queryName ≠ entry.1 := by
        intro hEq
        apply hnotmem
        simp [hEq]
      have hrestNotMem : queryName ∉ rest.map Prod.fst := by
        intro hmem
        apply hnotmem
        simp [hmem]
      rw [List.foldl, ih _ hrestNotMem,
        FunctionBody.lookupBinding?_bindValue_ne init entry.1 queryName entry.2 hqueryNe]

/-- If a name occurs in the final binding list with unique parameter names,
folding `bindValue` over any initial environment reconstructs that lookup
exactly. -/
private theorem lookupBinding?_foldl_bindValue_mem
    (bindings : List (String × Nat))
    (init : List (String × Nat))
    (queryName : String)
    (hmem : queryName ∈ bindings.map Prod.fst)
    (hnodup : (bindings.map Prod.fst).Nodup) :
    FunctionBody.lookupBinding?
      (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) init)
      queryName =
    FunctionBody.lookupBinding? bindings queryName := by
  induction bindings generalizing init with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hheadNotMem, hrestNodup⟩
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hEq | hmemRest
      · subst hEq
        have hrestNotMem : entry.1 ∉ rest.map Prod.fst := hheadNotMem
        rw [List.foldl]
        rw [lookupBinding?_foldl_bindValue_not_mem rest
          (SourceSemantics.bindValue init entry.1 entry.2) entry.1 hrestNotMem]
        rw [FunctionBody.lookupBinding?_bindValue_eq]
        unfold FunctionBody.lookupBinding?
        simp
      · have hqueryNe : queryName ≠ entry.1 := by
          intro hEq
          apply hheadNotMem
          simpa [hEq] using hmemRest
        rw [List.foldl]
        rw [ih (SourceSemantics.bindValue init entry.1 entry.2) hmemRest hrestNodup]
        have hbeq : (entry.1 == queryName) = false := by
          have hqueryNe' : ¬ entry.1 = queryName := by
            intro hEq
            exact hqueryNe hEq.symm
          simp [hqueryNe']
        unfold FunctionBody.lookupBinding?
        simp [List.find?, hbeq]

/-- The raw prebinding fold starts from an empty environment, so names absent
from the raw ABI prefix stay absent afterwards. -/
private theorem lookupBinding?_rawArgBindings_fold_not_mem
    (params : List Param)
    (args : List Nat)
    (queryName : String)
    (hnotmem : queryName ∉ (rawArgBindings params args).map Prod.fst) :
    FunctionBody.lookupBinding?
      ((rawArgBindings params args).foldl
        (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) [])
      queryName = none := by
  rw [lookupBinding?_foldl_bindValue_not_mem (rawArgBindings params args) [] queryName hnotmem]
  simp [FunctionBody.lookupBinding?]

private theorem lookupBinding?_eq_none_of_not_mem
    (bindings : List (String × Nat))
    (queryName : String)
    (hnotmem : queryName ∉ bindings.map Prod.fst) :
    FunctionBody.lookupBinding? bindings queryName = none := by
  unfold FunctionBody.lookupBinding?
  induction bindings with
  | nil =>
      simp
  | cons entry rest ih =>
      have hqueryNe : queryName ≠ entry.1 := by
        intro hEq
        apply hnotmem
        simp [hEq]
      have hrestNotMem : queryName ∉ rest.map Prod.fst := by
        intro hmem
        apply hnotmem
        simp [hmem]
      have hbeq : (entry.1 == queryName) = false := by
        have hqueryNe' : ¬ entry.1 = queryName := by
          intro hEq
          exact hqueryNe hEq.symm
        simp [hqueryNe']
      simp [List.find?, hbeq, ih hrestNotMem]

private theorem lookupBinding?_some_of_mem
    (bindings : List (String × Nat))
    (queryName : String)
    (hmem : queryName ∈ bindings.map Prod.fst) :
    ∃ value, FunctionBody.lookupBinding? bindings queryName = some value := by
  induction bindings with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      by_cases hEq : entry.1 = queryName
      · refine ⟨entry.2, ?_⟩
        subst hEq
        unfold FunctionBody.lookupBinding?
        simp
      · rcases hmem with hhead | htail
        · cases hEq hhead.symm
        · rcases ih htail with ⟨value, hvalue⟩
          refine ⟨value, ?_⟩
          have hbeq : (entry.1 == queryName) = false := by
            simp [hEq]
          unfold FunctionBody.lookupBinding? at hvalue ⊢
          cases hfind : List.find? (fun candidate => candidate.1 == queryName) rest with
          | none =>
              simp [List.find?, hbeq, hfind] at hvalue
          | some found =>
              cases found with
              | mk foundName foundValue =>
                  simp [List.find?, hbeq, hfind] at hvalue ⊢
                  cases hvalue
                  rfl

/-- The initial IR state matches the source runtime once the transaction
context already fits the bounded source-level numeric domains. -/
theorem initialIRStateForTx_matches_runtime
    (model : CompilationModel)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : TxContextNormalized tx) :
    FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := [] }
      (FunctionBody.initialIRStateForTx model tx initialWorld) := by sorry
-- SORRY'D:   rcases htxNormalized with
-- SORRY'D:     ⟨hsender, hthis, hmsgValue, htimestamp, hnumber, hchain⟩
-- SORRY'D:   have hsenderEvm : tx.sender < Compiler.Constants.evmModulus := by
-- SORRY'D:     dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hsender ⊢
-- SORRY'D:     omega
-- SORRY'D:   have hthisEvm : tx.thisAddress < Compiler.Constants.evmModulus := by
-- SORRY'D:     dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hthis ⊢
-- SORRY'D:     omega
-- SORRY'D:   have hsenderAddr : tx.sender < Verity.Core.Address.modulus := by
-- SORRY'D:     simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus] using hsender
-- SORRY'D:   have hthisAddr : tx.thisAddress < Verity.Core.Address.modulus := by
-- SORRY'D:     simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus] using hthis
-- SORRY'D:   refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
-- SORRY'D:   · simpa [FunctionBody.initialIRStateForTx, SourceSemantics.effectiveFields,
-- SORRY'D:       SourceSemantics.encodeStorage] using
-- SORRY'D:       (FunctionBody.encodeStorage_withTransactionContext model initialWorld tx).symm
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
-- SORRY'D:       Verity.wordToAddress]
-- SORRY'D:     symm
-- SORRY'D:     calc
-- SORRY'D:       tx.sender % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
-- SORRY'D:           = tx.sender % Verity.Core.Address.modulus := by
-- SORRY'D:               rw [Nat.mod_eq_of_lt hsenderEvm]
-- SORRY'D:       _ = tx.sender := Nat.mod_eq_of_lt hsenderAddr
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
-- SORRY'D:     symm
-- SORRY'D:     exact Nat.mod_eq_of_lt hmsgValue
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
-- SORRY'D:       Verity.wordToAddress]
-- SORRY'D:     symm
-- SORRY'D:     calc
-- SORRY'D:       tx.thisAddress % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
-- SORRY'D:           = tx.thisAddress % Verity.Core.Address.modulus := by
-- SORRY'D:               rw [Nat.mod_eq_of_lt hthisEvm]
-- SORRY'D:       _ = tx.thisAddress := Nat.mod_eq_of_lt hthisAddr
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
-- SORRY'D:     symm
-- SORRY'D:     exact Nat.mod_eq_of_lt htimestamp
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
-- SORRY'D:     symm
-- SORRY'D:     exact Nat.mod_eq_of_lt hnumber
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
-- SORRY'D:     symm
-- SORRY'D:     exact Nat.mod_eq_of_lt hchain
-- SORRY'D:   · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]

-- SORRY'D: /-- The ABI parameter-loading prefix reconstructs exactly the decoded source
-- SORRY'D: bindings for any supported function with pairwise-distinct parameter names. -/
theorem supported_function_param_state_exact
    (state : IRState)
    (params : List Param)
    (bindings : List (String × Nat))
    (hinit : FunctionBody.bindingsExactlyMatchIRVars [] state)
    (hparamNamesNodup : (params.map (·.name)).Nodup)
    (hbind : SourceSemantics.bindSupportedParams params state.calldata = some bindings) :
    FunctionBody.bindingsExactlyMatchIRVars bindings
      (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings) := by
  let rawInitBindings :=
    (rawArgBindings params state.calldata).foldl
      (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2) []
  have hprebound :
      FunctionBody.bindingsExactlyMatchIRVars rawInitBindings
        (prebindRawArgs state params) := by
    simpa [rawInitBindings] using prebindRawArgs_exact_rawArgBindings hinit params
  have hfinal :
      FunctionBody.bindingsExactlyMatchIRVars
        (bindings.foldl (fun acc entry => SourceSemantics.bindValue acc entry.1 entry.2)
          rawInitBindings)
        (ParamLoading.applyBindingsToIRState (prebindRawArgs state params) bindings) :=
    FunctionBody.bindingsExactlyMatchIRVars_applyBindingsToIRState hprebound
  intro queryName
  rw [hfinal queryName]
  by_cases hmem : queryName ∈ bindings.map Prod.fst
  · exact lookupBinding?_foldl_bindValue_mem bindings rawInitBindings queryName hmem
      (ParamLoading.bindSupportedParams_names_nodup hparamNamesNodup hbind)
  · rw [lookupBinding?_foldl_bindValue_not_mem bindings rawInitBindings queryName hmem]
    have hrawNames :
        (rawArgBindings params state.calldata).map Prod.fst = bindings.map Prod.fst :=
      rawArgBindings_names_of_bindSupportedParams hbind
    have hrawNotMem : queryName ∉ (rawArgBindings params state.calldata).map Prod.fst := by
      rw [hrawNames]
      exact hmem
    rw [lookupBinding?_rawArgBindings_fold_not_mem params state.calldata queryName hrawNotMem]
    symm
    exact lookupBinding?_eq_none_of_not_mem bindings queryName hmem

theorem supported_function_body_correct_from_exact_state_core
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
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
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem
    have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmem
    exact lookupBinding?_some_of_mem bindings name hmemBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      hcore hscope hstateBindings hbounded hstateRuntime' with
    ⟨bodyIR, hbodyCoreCompile, hcoreSem, _⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyCoreCompile
    injection hbodyCoreCompile with hEq
    exact hEq.symm
  subst bodyIR
  refine ⟨_, _, rfl, rfl, hcoreSem⟩

theorem supported_function_body_correct_from_exact_state_core_extraFuel
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body)
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
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
    intro name hmem
    have hmemBindings : name ∈ bindings.map Prod.fst := by
      rw [ParamLoading.bindSupportedParams_names hbind]
      simpa using hmem
    exact lookupBinding?_some_of_mem bindings name hmemBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      extraFuel hcore hscope hstateBindings hbounded hstateRuntime' with
    ⟨bodyIR, hbodyCoreCompile, hcoreSem, _⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyCoreCompile
    injection hbodyCoreCompile with hEq
    exact hEq.symm
  subst bodyIR
  refine ⟨_, _, rfl, rfl, hcoreSem⟩

theorem supported_function_body_correct_from_exact_state_terminal_core_extraFuel
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body)
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
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by sorry
-- SORRY'D:   have hscope :
-- SORRY'D:       FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
-- SORRY'D:     intro name hmem
-- SORRY'D:     have hmemBindings : name ∈ bindings.map Prod.fst := by
-- SORRY'D:       rw [ParamLoading.bindSupportedParams_names hbind]
-- SORRY'D:       simpa using hmem
-- SORRY'D:     exact lookupBinding?_some_of_mem bindings name hmemBindings
-- SORRY'D:   have hscopeExact :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope
-- SORRY'D:         (fn.params.map (·.name)) bindings state :=
-- SORRY'D:     FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
-- SORRY'D:   have hbounded : FunctionBody.bindingsBounded bindings :=
-- SORRY'D:     FunctionBody.bindingsBounded_of_bindSupportedParams hbind
-- SORRY'D:   have hstateRuntime' :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         state := by
-- SORRY'D:     simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
-- SORRY'D:   have hbodyCompile' :
-- SORRY'D:       compileStmtList (SourceSemantics.effectiveFields model) [] []
-- SORRY'D:         .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
-- SORRY'D:     simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
-- SORRY'D:   let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
-- SORRY'D:   rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                     bindings := bindings })
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (inScopeNames := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (extraFuel := sizeSlack)
-- SORRY'D:       hterminal
-- SORRY'D:       FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:       hscope
-- SORRY'D:       hscopeExact
-- SORRY'D:       hbounded
-- SORRY'D:       hstateRuntime' with
-- SORRY'D:     ⟨bodyIR, hbodyTerminalCompile, hterminalSem⟩
-- SORRY'D:   have hbodyEq : bodyIR = bodyStmts := by
-- SORRY'D:     rw [hbodyCompile'] at hbodyTerminalCompile
-- SORRY'D:     injection hbodyTerminalCompile with hEq
-- SORRY'D:     exact hEq.symm
-- SORRY'D:   subst bodyIR
-- SORRY'D:   have hfuel :
-- SORRY'D:       sizeOf bodyStmts + sizeSlack + 1 =
-- SORRY'D:         bodyStmts.length + extraFuel + 1 := by
-- SORRY'D:     dsimp [sizeSlack]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, rfl, rfl, ?_⟩
-- SORRY'D:   simpa [hfuel, sizeSlack] using hterminalSem

private theorem firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hvalidate : validateCompileInputs spec selectors = Except.ok ()) :
    firstFieldWriteSlotConflict
        (applySlotAliasRanges spec.fields spec.slotAliasRanges) = none := by sorry
-- SORRY'D:   unfold validateCompileInputs at hvalidate
-- SORRY'D:   cases hshapes : validateIdentifierShapes spec with
-- SORRY'D:   | error err =>
-- SORRY'D:       simp [hshapes] at hvalidate
-- SORRY'D:   | ok _ =>
-- SORRY'D:       cases hbadAlias : firstInvalidSlotAliasRange spec.slotAliasRanges with
-- SORRY'D:       | some bad =>
-- SORRY'D:           simp [hshapes, hbadAlias] at hvalidate
-- SORRY'D:       | none =>
-- SORRY'D:           cases hoverlap : firstSlotAliasSourceOverlap spec.slotAliasRanges with
-- SORRY'D:           | some overlap =>
-- SORRY'D:               simp [hshapes, hbadAlias, hoverlap] at hvalidate
-- SORRY'D:           | none =>
-- SORRY'D:               cases hdyn : firstInternalDynamicParam spec.functions with
-- SORRY'D:               | some dyn =>
-- SORRY'D:                   simp [hshapes, hbadAlias, hoverlap, hdyn] at hvalidate
-- SORRY'D:               | none =>
-- SORRY'D:                   cases hdupParam : firstDuplicateFunctionParamName spec.functions with
-- SORRY'D:                   | some dup =>
-- SORRY'D:                       simp [hshapes, hbadAlias, hoverlap, hdyn, hdupParam] at hvalidate
-- SORRY'D:                   | none =>
-- SORRY'D:                       cases hdupCtor : firstDuplicateConstructorParamName spec.constructor with
-- SORRY'D:                       | some dup =>
-- SORRY'D:                           simp [hshapes, hbadAlias, hoverlap, hdyn, hdupParam, hdupCtor] at hvalidate
-- SORRY'D:                       | none =>
-- SORRY'D:                           simp [hshapes, hbadAlias, hoverlap, hdyn, hdupParam, hdupCtor] at hvalidate
-- SORRY'D:                           set fields := applySlotAliasRanges spec.fields spec.slotAliasRanges with hfields
-- SORRY'D:                           cases hdupFn : firstDuplicateName (spec.functions.map (fun fn => fn.name)) with
-- SORRY'D:                           | some dup =>
-- SORRY'D:                               simp [hdupFn] at hvalidate
-- SORRY'D:                           | none =>
-- SORRY'D:                               cases hdupErr : firstDuplicateName (spec.errors.map (fun err => err.name)) with
-- SORRY'D:                               | some dup =>
-- SORRY'D:                                   simp [hdupErr] at hvalidate
-- SORRY'D:                               | none =>
-- SORRY'D:                                   cases hdupField : firstDuplicateName (spec.fields.map (fun field => field.name)) with
-- SORRY'D:                                   | some dup =>
-- SORRY'D:                                       simp [hdupField] at hvalidate
-- SORRY'D:                                   | none =>
-- SORRY'D:                                       cases hpacked : firstInvalidPackedBits spec.fields with
-- SORRY'D:                                       | some bad =>
-- SORRY'D:                                           simp [hpacked] at hvalidate
-- SORRY'D:                                       | none =>
-- SORRY'D:                                           cases hmappingPacked : firstMappingPackedBits spec.fields with
-- SORRY'D:                                           | some field =>
-- SORRY'D:                                               simp [hmappingPacked] at hvalidate
-- SORRY'D:                                           | none =>
-- SORRY'D:                                               cases harrayElem : firstUnsupportedStorageArrayElemType spec.fields with
-- SORRY'D:                                               | some bad =>
-- SORRY'D:                                                   simp [harrayElem] at hvalidate
-- SORRY'D:                                               | none =>
-- SORRY'D:                                                   cases hinvalidStruct : firstInvalidStructField spec.fields with
-- SORRY'D:                                                   | error err =>
-- SORRY'D:                                                       simp [hinvalidStruct] at hvalidate
-- SORRY'D:                                                   | ok _ =>
-- SORRY'D:                                                       cases hconflict : firstFieldWriteSlotConflict fields with
-- SORRY'D:                                                       | some conflict =>
-- SORRY'D:                                                           simp [hfields, hdupFn, hdupErr, hdupField,
-- SORRY'D:                                                             hpacked, hmappingPacked, harrayElem,
-- SORRY'D:                                                             hinvalidStruct, hconflict] at hvalidate
-- SORRY'D:                                                       | none =>
-- SORRY'D:                                                           simpa [hfields] using hconflict

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

theorem compileFunctionSpec_correct_of_body_normalized_extraFuel
    (model : CompilationModel)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
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
      execIRStmts (bodyStmts.length + extraFuel + 1)
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
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hbodyCompile' :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized] using hbodyCompile
  have hcompile' :
      compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn := by
    simpa [hnormalized] using hcompile
  have hcompiled :=
    compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile'
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile'] at hcompiled
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
          ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body_extraFuel
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) (extraFuel := extraFuel)
      hparamsSupported hcalldataSizeFits hbind hbodyExec
  subst hirFn
  rw [hcompiledExec]
  simpa [initialState] using hsourceMatch

theorem compileFunctionSpec_correct_of_body_supported_extraFuel
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (selector : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (returns : List ParamType) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (sourceResult : SourceSemantics.StmtResult) (irExec : IRExecResult)
    (bindings : List (String × Nat)) (extraFuel : Nat)
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
      execIRStmts (bodyStmts.length + extraFuel + 1)
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
        ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
        irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compileFunctionSpec_correct_of_body_normalized_extraFuel
    model
    hSupported.normalizedFields
    selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
    bindings extraFuel hvalidate hreturns hbodyCompile hcompile hparamsSupported
    hcalldataSizeFits hbind hsource hbodyExec hmatch

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
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
    (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   classical
-- SORRY'D:   let _ := hvalidateInputs
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hinitBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hparamNamesNodup :
-- SORRY'D:       (fn.params.map (·.name)).Nodup :=
-- SORRY'D:     hSupported.selectorFunctionParamNamesNodup hfn
-- SORRY'D:   have hstateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) :=
-- SORRY'D:     supported_function_param_state_exact
-- SORRY'D:       initialState fn.params bindings hinitBindings hparamNamesNodup hbind
-- SORRY'D:   have hpreboundRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (prebindRawArgs initialState fn.params) := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       runtimeStateMatchesIR_prebindRawArgs
-- SORRY'D:         (state := initialState)
-- SORRY'D:         (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:         (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:         (params := fn.params)
-- SORRY'D:         (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized)
-- SORRY'D:   have hstateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) :=
-- SORRY'D:     runtimeStateMatchesIR_applyBindingsToIRState
-- SORRY'D:       (state := prebindRawArgs initialState fn.params)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       hpreboundRuntime
-- SORRY'D:   have hbodyStateBindings := hstateBindings
-- SORRY'D:   have hbodyStateRuntime := hstateRuntime
-- SORRY'D:   by_cases hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body
-- SORRY'D:   · let extraFuel := sizeOf irFn.body - irFn.body.length
-- SORRY'D:     have hbodyCorrect :
-- SORRY'D:         ∃ sourceResult irExec,
-- SORRY'D:           SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
-- SORRY'D:             { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:               bindings := bindings }
-- SORRY'D:             fn.body = sourceResult ∧
-- SORRY'D:           execIRStmts (bodyStmts.length + extraFuel + 1)
-- SORRY'D:             (ParamLoading.applyBindingsToIRState
-- SORRY'D:               (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:             bodyStmts = irExec ∧
-- SORRY'D:           FunctionBody.stmtResultMatchesIRExec
-- SORRY'D:             (SourceSemantics.effectiveFields model) sourceResult irExec := by
-- SORRY'D:       exact supported_function_body_correct_from_exact_state_core_extraFuel
-- SORRY'D:         (model := model)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (bodyStmts := bodyStmts)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (state := ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (extraFuel := extraFuel)
-- SORRY'D:         (hnormalized := by
-- SORRY'D:           simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:         (hnoEvents := hSupported.noEvents)
-- SORRY'D:         (hnoErrors := hSupported.noErrors)
-- SORRY'D:         hbind hcore hbodyCompile hbodyStateRuntime hbodyStateBindings
-- SORRY'D:     rcases hbodyCorrect with
-- SORRY'D:       ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:     have hfuel :=
-- SORRY'D:       compileFunctionSpec_correct_of_body_supported_extraFuel
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (selector := selector)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (returns := returns)
-- SORRY'D:         (bodyStmts := bodyStmts)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (sourceResult := sourceResult)
-- SORRY'D:         (irExec := irExec)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (extraFuel := extraFuel)
-- SORRY'D:         hvalidate hreturns
-- SORRY'D:         (by simpa [hSupported.normalizedFields] using hbodyCompile)
-- SORRY'D:         (by simpa [hSupported.normalizedFields] using hcompile)
-- SORRY'D:         (hSupported.selectorFunctionParamsSupported hfn)
-- SORRY'D:         hcalldataSizeFits hbind hsource hbodyExec hmatch
-- SORRY'D:     have hcompiled :=
-- SORRY'D:       compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:         selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:     have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:       rw [hcompile] at hcompiled
-- SORRY'D:       injection hcompiled
-- SORRY'D:     subst hirFn
-- SORRY'D:     have hbodyFuel :
-- SORRY'D:         (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:           sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:       have hlenle :
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
-- SORRY'D:             sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:         exact Nat.le_of_add_le_add_right
-- SORRY'D:           (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
-- SORRY'D:       dsimp [extraFuel]
-- SORRY'D:       simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
-- SORRY'D:     have hfuelEq' :
-- SORRY'D:         bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
-- SORRY'D:           1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:       have hbodyFuel' :
-- SORRY'D:           (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:             sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:         simpa [compiledFunctionIR] using hbodyFuel
-- SORRY'D:       calc
-- SORRY'D:         bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
-- SORRY'D:             = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
-- SORRY'D:                 simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
-- SORRY'D:         _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
-- SORRY'D:         _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
-- SORRY'D:     have hadequacy :
-- SORRY'D:         Compiler.Proofs.YulGeneration.execIRFunctionFuel
-- SORRY'D:             (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
-- SORRY'D:             (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
-- SORRY'D:           execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
-- SORRY'D:       simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
-- SORRY'D:         (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
-- SORRY'D:     have hfuel' :
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (SourceSemantics.interpretFunction model fn tx initialWorld)
-- SORRY'D:           (Compiler.Proofs.YulGeneration.execIRFunctionFuel
-- SORRY'D:             (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
-- SORRY'D:             (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
-- SORRY'D:       simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
-- SORRY'D:         hfuelEq'] using hfuel
-- SORRY'D:     simpa [hadequacy] using hfuel'

-- SORRY'D: /-- Direct helper-aware function/IR preservation target for the non-core path.
-- SORRY'D: Future helper-summary/rank proofs should feed this theorem via the explicit
-- SORRY'D: helper-aware body/IR goal, rather than via a collapse back to legacy
-- SORRY'D: helper-free source semantics. -/
theorem supported_function_correct_with_helper_proofs_body_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
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
    (htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   have hfuel :=
-- SORRY'D:     compileFunctionSpec_correct_of_body_supported_extraFuel
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (sourceResult := sourceResult)
-- SORRY'D:       (irExec := irExec)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       hvalidate hreturns
-- SORRY'D:       (by simpa [hSupported.normalizedFields] using hbodyCompile)
-- SORRY'D:       (by simpa [hSupported.normalizedFields] using hcompile)
-- SORRY'D:       (hSupported.selectorFunctionParamsSupported hfn)
-- SORRY'D:       hcalldataSizeFits hbind hsource hbodyExec hmatch
-- SORRY'D:   subst hirFn
-- SORRY'D:   have hfuelEq' :
-- SORRY'D:       bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
-- SORRY'D:         1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:     have hbodyFuel' :
-- SORRY'D:         (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:           sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:       simpa [compiledFunctionIR] using hcompiledBodyFuel
-- SORRY'D:     calc
-- SORRY'D:       bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
-- SORRY'D:           = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
-- SORRY'D:               simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
-- SORRY'D:       _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
-- SORRY'D:       _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
-- SORRY'D:   have hadequacy :
-- SORRY'D:       Compiler.Proofs.YulGeneration.execIRFunctionFuel
-- SORRY'D:           (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
-- SORRY'D:         execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
-- SORRY'D:     simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
-- SORRY'D:       (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
-- SORRY'D:         (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
-- SORRY'D:   have hfuel' :
-- SORRY'D:       FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:         (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:         (Compiler.Proofs.YulGeneration.execIRFunctionFuel
-- SORRY'D:           (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
-- SORRY'D:     simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
-- SORRY'D:       (hSupported := hSupported) hfn tx initialWorld,
-- SORRY'D:       compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
-- SORRY'D:       hfuelEq'] using hfuel
-- SORRY'D:   simpa [hadequacy] using hfuel'

-- SORRY'D: /-- Exact helper-aware function/IR preservation target for the non-core path.
-- SORRY'D: This lets callers stay on the exact helper-aware body/IR seam and only collapse
-- SORRY'D: back to the legacy function theorem boundary through compiled-body
-- SORRY'D: disjointness. -/
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
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
    (htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts)
    (hhelperIR :
      execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld))
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyBody :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel :=
    supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
      runtimeContract
      model fn bodyStmts hSupported.helperFuel tx initialWorld
      (ParamLoading.applyBindingsToIRState
        (prebindRawArgs
          (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
        bindings)
      bindings extraFuel
      hbodyCorrect
      hbodyDisjoint
  have hlegacy :=
    supported_function_correct_with_helper_proofs_body_goal
      model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
      bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
      hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hlegacyBody hcalldataSizeFits
  simpa [hhelperIR] using hlegacy

/-- Structured exact helper-aware function/IR wrapper under compiled-body
disjointness. The exact helper-aware body theorem can now be reused all the way
up to function-level results without requiring callers to restate the
conservative-extension equality manually. -/
theorem supported_function_correct_with_helper_proofs_body_goal_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
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
    (htxNormalized : TxContextNormalized tx)
    (extraFuel : Nat)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   have hbodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     simpa [compiledFunctionIR] using
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable.of_append_prefix
-- SORRY'D:         (contract := runtimeContract)
-- SORRY'D:         (pre := genParamLoads fn.params)
-- SORRY'D:         (suf := bodyStmts)
-- SORRY'D:         hfnBodyDisjoint
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyCorrect
-- SORRY'D:       hbodyDisjoint
-- SORRY'D:       (execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         irFn
-- SORRY'D:         tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)
-- SORRY'D:         hfnBodyDisjoint)
-- SORRY'D:       hcalldataSizeFits

-- SORRY'D: /-- Function-level exact helper-aware theorem over the fully split internal-helper
-- SORRY'D: interfaces, under per-body compiled disjointness. This is the direct wrapper
-- SORRY'D: future rank-induction helper proofs should target: they can discharge the split
-- SORRY'D: statement-list interfaces and avoid hand-assembling the exact body goal. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_split_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hhelperFree :
-- SORRY'D:       StmtListHelperFreeStepInterface
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hexpr :
-- SORRY'D:       StmtListExprInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hstruct :
-- SORRY'D:       StmtListStructuralInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hresidual :
-- SORRY'D:       StmtListResidualHelperSurfaceStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hinitBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hparamNamesNodup :
-- SORRY'D:       (fn.params.map (·.name)).Nodup :=
-- SORRY'D:     hSupported.selectorFunctionParamNamesNodup hfn
-- SORRY'D:   have hbodyStateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     have hpreboundRuntime :
-- SORRY'D:         FunctionBody.runtimeStateMatchesIR
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:             bindings := [] }
-- SORRY'D:           (prebindRawArgs initialState fn.params) := by
-- SORRY'D:       simpa [initialState] using
-- SORRY'D:         runtimeStateMatchesIR_prebindRawArgs
-- SORRY'D:           (state := initialState)
-- SORRY'D:           (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                         bindings := [] })
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (params := fn.params)
-- SORRY'D:           (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized)
-- SORRY'D:     exact runtimeStateMatchesIR_applyBindingsToIRState
-- SORRY'D:       (state := prebindRawArgs initialState fn.params)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                     bindings := [] })
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       hpreboundRuntime
-- SORRY'D:   have hbodyStateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     exact supported_function_param_state_exact
-- SORRY'D:       initialState fn.params bindings hinitBindings hparamNamesNodup hbind
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   let extraFuel := sizeOf irFn.body - irFn.body.length
-- SORRY'D:   have hbodyExtraFuelLower :
-- SORRY'D:       sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     simpa [compiledFunctionIR] using
-- SORRY'D:       yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
-- SORRY'D:   have hcompiledBodyFuel :
-- SORRY'D:       (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:         sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     have hlenle :
-- SORRY'D:         (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
-- SORRY'D:           sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:       exact Nat.le_of_add_le_add_right
-- SORRY'D:         (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
-- SORRY'D:     simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
-- SORRY'D:   have hscope :
-- SORRY'D:       FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
-- SORRY'D:     intro name hmem
-- SORRY'D:     have hmemBindings : name ∈ bindings.map Prod.fst := by
-- SORRY'D:       rw [ParamLoading.bindSupportedParams_names hbind]
-- SORRY'D:       simpa using hmem
-- SORRY'D:     exact lookupBinding?_some_of_mem bindings name hmemBindings
-- SORRY'D:   have hbounded : FunctionBody.bindingsBounded bindings :=
-- SORRY'D:     FunctionBody.bindingsBounded_of_bindSupportedParams hbind
-- SORRY'D:   have hbodyCorrect :
-- SORRY'D:       SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
-- SORRY'D:         runtimeContract
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel := by
-- SORRY'D:     exact
-- SORRY'D:       supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel
-- SORRY'D:         hbodyExtraFuelLower
-- SORRY'D:         hSupported.helperFuel_pos
-- SORRY'D:         (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:         hSupported.noEvents
-- SORRY'D:         hSupported.noErrors
-- SORRY'D:         hhelperFree
-- SORRY'D:         hcall
-- SORRY'D:         hassign
-- SORRY'D:         hexpr
-- SORRY'D:         hstruct
-- SORRY'D:         hresidual
-- SORRY'D:         hdisjoint
-- SORRY'D:         hbodyCompile
-- SORRY'D:         hscope
-- SORRY'D:         hbounded
-- SORRY'D:         hbodyStateRuntime
-- SORRY'D:         hbodyStateBindings
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_body_goal_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyCorrect
-- SORRY'D:       hfnBodyDisjoint hcalldataSizeFits

-- SORRY'D: /-- Function-level exact helper-aware wrapper that isolates the genuinely new
-- SORRY'D: Tier 4 obligations. The still-vacuous helper-free / expr / structural /
-- SORRY'D: residual interfaces are discharged directly from the existing supported-body
-- SORRY'D: witness, so future rank induction only needs to provide the direct statement-
-- SORRY'D: position helper call and helper-assign interfaces together with compiled-body
-- SORRY'D: disjointness. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
-- SORRY'D:   have hnoConflict :
-- SORRY'D:       firstFieldWriteSlotConflict (SourceSemantics.effectiveFields model) = none := by
-- SORRY'D:     simpa [SourceSemantics.effectiveFields] using
-- SORRY'D:       firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
-- SORRY'D:         (spec := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         hvalidateInputs
-- SORRY'D:   have hhelperFree :
-- SORRY'D:       StmtListHelperFreeStepInterface
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     hsupportedFn.body.helperFreeStepInterface
-- SORRY'D:       hnoConflict
-- SORRY'D:   have hexpr :
-- SORRY'D:       StmtListExprInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:   have hstruct :
-- SORRY'D:       StmtListStructuralInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:   have hresidual :
-- SORRY'D:       StmtListResidualHelperSurfaceStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_split_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized hhelperFree hcall hassign
-- SORRY'D:       hexpr hstruct hresidual hdisjoint hfnBodyDisjoint hcalldataSizeFits

-- SORRY'D: /-- Function-level direct-helper wrapper stated over reusable single-head
-- SORRY'D: helper-step builders instead of preassembled list interfaces. This is the
-- SORRY'D: closest current theorem boundary to the eventual helper-rank induction:
-- SORRY'D: once rank induction can build the exact `Stmt.internalCall` /
-- SORRY'D: `Stmt.internalCallAssign` head steps, the surrounding list-interface plumbing is
-- SORRY'D: discharged here. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCall calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hcallStep
-- SORRY'D:   have hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hassignStep
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized hcall hassign hdisjoint
-- SORRY'D:       hfnBodyDisjoint hcalldataSizeFits

-- SORRY'D: /-- Function-level direct-helper wrapper whose head-step assumptions range only
-- SORRY'D: over helper callees that actually appear in `fn.body`. This aligns the exact
-- SORRY'D: Tier 4 theorem seam with `SupportedBodyHelperInterface.calleeRanksDecrease`,
-- SORRY'D: which is also indexed by `helperCallNames fn` rather than arbitrary names. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         calleeName ∈ helperCallNames fn →
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCall calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         calleeName ∈ helperCallNames fn →
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (by
-- SORRY'D:         intro scope calleeName args hmem
-- SORRY'D:         exact hcallStep (scope := scope) (calleeName := calleeName) (args := args)
-- SORRY'D:           (by simpa [helperCallNames] using hmem))
-- SORRY'D:   have hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (by
-- SORRY'D:         intro scope names calleeName args hmem
-- SORRY'D:         exact hassignStep
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (names := names)
-- SORRY'D:           (calleeName := calleeName)
-- SORRY'D:           (args := args)
-- SORRY'D:           (by simpa [helperCallNames] using hmem))
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized hcall hassign hdisjoint
-- SORRY'D:       hfnBodyDisjoint hcalldataSizeFits

-- SORRY'D: /-- Function-level Tier 4 wrapper that consumes a single exact direct-helper
-- SORRY'D: head-step catalog for `fn.body`. This is the proof object future rank
-- SORRY'D: induction should build once `calleeRanksDecrease` is wired non-vacuously. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hcatalog :
-- SORRY'D:       DirectInternalHelperHeadStepCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases
-- SORRY'D:       stmtListDirectInternalHelperStepInterfaces_of_headStepCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := model)
-- SORRY'D:         (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:         (scope := fn.params.map (·.name))
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hcatalog with
-- SORRY'D:     ⟨hcall, hassign⟩
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
-- SORRY'D:       fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
-- SORRY'D:       hreturns hbodyCompile hcompile hbind htxNormalized hcall hassign hdisjoint
-- SORRY'D:       hfnBodyDisjoint hcalldataSizeFits

-- SORRY'D: /-- Function-level Tier 4 wrapper one seam earlier than
-- SORRY'D: `...head_step_catalog...`: callers provide singleton helper-call compilation and
-- SORRY'D: bridge proofs, and the reusable direct-helper catalog is assembled here. This is
-- SORRY'D: the intended theorem boundary for future rank induction. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hbridge :
-- SORRY'D:       DirectInternalHelperHeadStepBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_bridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hbridge)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the callee-local bridge boundary. This
-- SORRY'D: matches `SupportedBodyHelperInterface.calleeRanksDecrease` directly: callers
-- SORRY'D: provide one reusable call bridge and one reusable assign bridge per helper
-- SORRY'D: callee referenced by `fn.body`, and the body-level bridge catalog is assembled
-- SORRY'D: here. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hcallee :
-- SORRY'D:       DirectInternalHelperPerCalleeBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hcallee)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the assign-only callee-local bridge
-- SORRY'D: boundary. Under the current fragment the direct-helper void-call bridge side is
-- SORRY'D: still vacuous, so callers only need to package one reusable assign bridge per
-- SORRY'D: referenced helper callee. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadAssignBridge :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (hSupported.supportedFunctionOfSelectorDispatched hfn).body
-- SORRY'D:           hheadAssignBridge)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the fully split callee-local boundary.
-- SORRY'D: Compile-side obligations for direct helper heads and semantic bridge
-- SORRY'D: obligations are supplied independently, then assembled directly into the exact
-- SORRY'D: body-level head-step catalog future rank induction should build. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_compileCatalog_and_semanticBridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hheadCompile
-- SORRY'D:           hheadSemantic)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper that isolates runtime helper witness lookup
-- SORRY'D: from the remaining semantic singleton-step work. The runtime witness catalog can
-- SORRY'D: be produced independently from a compiled helper table, leaving the semantic
-- SORRY'D: core as the only future rank-induction obligation, while this wrapper now lands
-- SORRY'D: directly on the exact body-level head-step catalog. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticCoreCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_compileCatalog_and_runtimeWitnessCatalog_and_semanticCoreCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hheadCompile
-- SORRY'D:           hruntimeWitness
-- SORRY'D:           hheadSemantic)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the smaller semantic-kernel seam. Source
-- SORRY'D: helper witnesses and helper-summary soundness are recovered from the supported
-- SORRY'D: function inventory already present at this theorem boundary, so callers only
-- SORRY'D: need to provide the irreducible semantic kernel plus compile/runtime catalogs,
-- SORRY'D: and this wrapper now lands directly on the exact body-level head-step catalog. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hHelpers
-- SORRY'D:           hheadCompile
-- SORRY'D:           hruntimeWitness
-- SORRY'D:           (SourceSemantics.SupportedSpecHelperProofs.functionSummariesSound
-- SORRY'D:             hSupported hHelperProofs hfn)
-- SORRY'D:           hheadKernel)
-- SORRY'D:        (hdisjoint := hdisjoint)
-- SORRY'D:        (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:        (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper one seam earlier than the runtime-witness
-- SORRY'D: catalog boundary. The compiled runtime helper table already determines the
-- SORRY'D: per-callee runtime witness inventory for `fn`, so callers only need to supply
-- SORRY'D: the global table together with the compile catalog and irreducible semantic
-- SORRY'D: kernel, and this wrapper now lands directly on the exact body-level head-step
-- SORRY'D: catalog. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hHelpers
-- SORRY'D:           hheadCompile
-- SORRY'D:           hRuntime
-- SORRY'D:           (SourceSemantics.SupportedSpecHelperProofs.functionSummariesSound
-- SORRY'D:             hSupported hHelperProofs hfn)
-- SORRY'D:           hheadKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the assign-only compile and semantic seam.
-- SORRY'D: Under the current fragment the direct-helper void-call compile side is still
-- SORRY'D: vacuous, so callers only need to provide assign-side compile obligations
-- SORRY'D: together with the assign semantic kernel and runtime helper table, and this
-- SORRY'D: wrapper now lands directly on the exact body-level head-step catalog future
-- SORRY'D: rank induction should build. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadAssignCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hsupportedFn.body
-- SORRY'D:           hheadAssignCompile
-- SORRY'D:           hRuntime
-- SORRY'D:           (SourceSemantics.SupportedSpecHelperProofs.functionSummariesSound
-- SORRY'D:             hSupported hHelperProofs hfn)
-- SORRY'D:           hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the split semantic-kernel boundary. The
-- SORRY'D: remaining helper-rank work can now discharge direct helper void calls and
-- SORRY'D: direct helper return-binding calls independently, while runtime helper-table
-- SORRY'D: facts are still reconstructed mechanically. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_callSemanticKernelCatalog_and_assignSemanticKernelCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hHelpers
-- SORRY'D:           hheadCompile
-- SORRY'D:           hRuntime
-- SORRY'D:           (SourceSemantics.SupportedSpecHelperProofs.functionSummariesSound
-- SORRY'D:             hSupported hHelperProofs hfn)
-- SORRY'D:           (directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
-- SORRY'D:             (runtimeContract := runtimeContract)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
-- SORRY'D:           hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 4 wrapper on the split semantic-kernel boundary. The
-- SORRY'D: remaining helper-rank work can now discharge direct helper void calls and
-- SORRY'D: direct helper return-binding calls independently, while runtime helper-table
-- SORRY'D: facts are still reconstructed mechanically. -/
-- SORRY'D: theorem
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (selector : Nat)
-- SORRY'D:     (returns : List ParamType)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- SORRY'D:     (hreturns : functionReturns fn = Except.ok returns)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hcompile :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (htxNormalized : TxContextNormalized tx)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadCallKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeCallSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
-- SORRY'D:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   let hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers
-- SORRY'D:   exact
-- SORRY'D:     supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_callSemanticKernelCatalog_and_assignSemanticKernelCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hHelpers
-- SORRY'D:           hheadCompile
-- SORRY'D:           hRuntime
-- SORRY'D:           (SourceSemantics.SupportedSpecHelperProofs.functionSummariesSound
-- SORRY'D:             hSupported hHelperProofs hfn)
-- SORRY'D:           hheadCallKernel
-- SORRY'D:           hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Function-level Tier 2 bridge for bodies admitted by the alternate
-- SORRY'D: singleton storage-write state interface. This keeps the theorem local to one
-- SORRY'D: function: global normalization and no-event/no-error assumptions remain
-- SORRY'D: explicit, while the body proof can now use the non-vacuous singleton
-- SORRY'D: mapping-write step interfaces instead of contradiction. -/
-- TYPESIG_SORRY: theorem supported_function_correct_with_body_interface_except_mapping_writes
-- TYPESIG_SORRY:     (model : CompilationModel)
-- TYPESIG_SORRY:     (fn : FunctionSpec)
-- TYPESIG_SORRY:     (helperFuel : Nat)
-- TYPESIG_SORRY:     (hnormalized :
-- TYPESIG_SORRY:       applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
-- TYPESIG_SORRY:     (hnoEvents : model.events = [])
-- TYPESIG_SORRY:     (hnoErrors : model.errors = [])
-- TYPESIG_SORRY:     (hparams : SupportedParamProfile fn.params)
-- TYPESIG_SORRY:     (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
-- TYPESIG_SORRY:     (selector : Nat)
-- TYPESIG_SORRY:     (returns : List ParamType)
-- TYPESIG_SORRY:     (bodyStmts : List YulStmt)
-- TYPESIG_SORRY:     (irFn : IRFunction)
-- TYPESIG_SORRY:     (tx : IRTransaction)
-- TYPESIG_SORRY:     (initialWorld : Verity.ContractState)
-- TYPESIG_SORRY:     (bindings : List (String × Nat))
-- TYPESIG_SORRY:     (hvalidate : validateFunctionSpec fn = Except.ok ())
-- TYPESIG_SORRY:     (hreturns : functionReturns fn = Except.ok returns)
-- TYPESIG_SORRY:     (hbodyCompile :
-- TYPESIG_SORRY:       compileStmtList model.fields model.events model.errors .calldata [] false
-- TYPESIG_SORRY:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- TYPESIG_SORRY:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- TYPESIG_SORRY:     (htxNormalized : TxContextNormalized tx)
-- TYPESIG_SORRY:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- TYPESIG_SORRY:     FunctionBody.sourceResultMatchesIRResult
-- TYPESIG_SORRY:       (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
-- TYPESIG_SORRY:       (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hinitBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hparamNamesNodup :
-- SORRY'D:       (fn.params.map (·.name)).Nodup :=
-- SORRY'D:     hparams.namesNodup
-- SORRY'D:   have hbodyStateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     have hpreboundRuntime :
-- SORRY'D:         FunctionBody.runtimeStateMatchesIR
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:             bindings := [] }
-- SORRY'D:           (prebindRawArgs initialState fn.params) := by
-- SORRY'D:       simpa [initialState] using
-- SORRY'D:         runtimeStateMatchesIR_prebindRawArgs
-- SORRY'D:           (state := initialState)
-- SORRY'D:           (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (params := fn.params)
-- SORRY'D:           (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized)
-- SORRY'D:     exact runtimeStateMatchesIR_applyBindingsToIRState
-- SORRY'D:       (state := prebindRawArgs initialState fn.params)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       hpreboundRuntime
-- SORRY'D:   have hbodyStateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     exact supported_function_param_state_exact
-- SORRY'D:       initialState fn.params bindings hinitBindings hparamNamesNodup hbind
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   let extraFuel := sizeOf irFn.body - irFn.body.length
-- SORRY'D:   have hbodyExtraFuelLower :
-- SORRY'D:       sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     simpa [compiledFunctionIR] using
-- SORRY'D:       yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
-- SORRY'D:   have hcompiledBodyFuel :
-- SORRY'D:       (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:         sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     have hlenle :
-- SORRY'D:         (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
-- SORRY'D:           sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:       exact Nat.le_of_add_le_add_right
-- SORRY'D:         (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
-- SORRY'D:     simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
-- SORRY'D:   have hbodyWithHelpers :
-- SORRY'D:       SupportedFunctionBodyWithHelpersIRPreservationGoal
-- SORRY'D:         model fn bodyStmts helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel := by
-- SORRY'D:     by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
-- SORRY'D:     · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
-- SORRY'D:           (model := model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (bodyStmts := bodyStmts)
-- SORRY'D:           (tx := tx)
-- SORRY'D:           (initialWorld := initialWorld)
-- SORRY'D:           (state := ParamLoading.applyBindingsToIRState
-- SORRY'D:             (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:           (bindings := bindings)
-- SORRY'D:           (extraFuel := extraFuel)
-- SORRY'D:           (hextraFuel := hbodyExtraFuelLower)
-- SORRY'D:           (hnormalized := by
-- SORRY'D:             simpa [SourceSemantics.effectiveFields] using hnormalized)
-- SORRY'D:           (hnoEvents := hnoEvents)
-- SORRY'D:           (hnoErrors := hnoErrors)
-- SORRY'D:           hbind
-- SORRY'D:           hterminal
-- SORRY'D:           hbodyCompile
-- SORRY'D:           hbodyStateRuntime
-- SORRY'D:           hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:       refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
-- SORRY'D:       have hhelperGoal :
-- SORRY'D:           SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             helperFuel
-- SORRY'D:             { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:               bindings := bindings }
-- SORRY'D:             fn.body :=
-- SORRY'D:         SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fuel := helperFuel)
-- SORRY'D:           (state := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                       bindings := bindings })
-- SORRY'D:           (stmts := fn.body)
-- SORRY'D:           hBody.helperSurfaceClosed
-- SORRY'D:       simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
-- SORRY'D:         hhelperGoal.trans hsource
-- SORRY'D:     · have hscope :
-- SORRY'D:           FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
-- SORRY'D:         intro name hmem
-- SORRY'D:         have hmemBindings : name ∈ bindings.map Prod.fst := by
-- SORRY'D:           rw [ParamLoading.bindSupportedParams_names hbind]
-- SORRY'D:           simpa using hmem
-- SORRY'D:         exact lookupBinding?_some_of_mem bindings name hmemBindings
-- SORRY'D:       have hbounded : FunctionBody.bindingsBounded bindings :=
-- SORRY'D:         FunctionBody.bindingsBounded_of_bindSupportedParams hbind
-- SORRY'D:       have hhelperFree :
-- SORRY'D:           StmtListHelperFreeStepInterface
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn.params.map (·.name))
-- SORRY'D:             fn.body := by
-- SORRY'D:         simpa [SourceSemantics.effectiveFields, hnormalized] using
-- SORRY'D:           hBody.helperFreeStepInterface hnoConflict hsafety
-- SORRY'D:       exact supported_function_body_correct_from_exact_state_generic_with_helpers
-- SORRY'D:         model fn bodyStmts helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel hbodyExtraFuelLower
-- SORRY'D:         (by simpa [SourceSemantics.effectiveFields] using hnormalized)
-- SORRY'D:         hnoEvents
-- SORRY'D:         hnoErrors
-- SORRY'D:         hBody.helperSurfaceClosed
-- SORRY'D:         hhelperFree
-- SORRY'D:         hbodyCompile
-- SORRY'D:         hscope
-- SORRY'D:         hbounded
-- SORRY'D:         hbodyStateRuntime
-- SORRY'D:         hbodyStateBindings
-- SORRY'D:   rcases hbodyWithHelpers with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:   have hhelperGoal :
-- SORRY'D:       SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         helperFuel
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         fn.body :=
-- SORRY'D:     SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (fuel := helperFuel)
-- SORRY'D:       (state := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                   bindings := bindings })
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       hBody.helperSurfaceClosed
-- SORRY'D:   have hsourceLegacy :
-- SORRY'D:       SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         fn.body = sourceResult := by
-- SORRY'D:     simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
-- SORRY'D:       hhelperGoal.symm.trans hsource
-- SORRY'D:   have hlegacy :
-- SORRY'D:       FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:         (SourceSemantics.interpretFunction model fn tx initialWorld)
-- SORRY'D:         (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     have hfuel :=
-- SORRY'D:       compileFunctionSpec_correct_of_body_normalized_extraFuel
-- SORRY'D:         model
-- SORRY'D:         hnormalized
-- SORRY'D:         selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
-- SORRY'D:         bindings extraFuel hvalidate hreturns
-- SORRY'D:         (by simpa [hnormalized] using hbodyCompile)
-- SORRY'D:         (by simpa [hnormalized] using hcompile)
-- SORRY'D:         hparams.supported
-- SORRY'D:         hcalldataSizeFits
-- SORRY'D:         hbind
-- SORRY'D:         hsourceLegacy
-- SORRY'D:         hbodyExec
-- SORRY'D:         hmatch
-- SORRY'D:     subst hirFn
-- SORRY'D:     have hbodyFuel :
-- SORRY'D:         (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:           sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:       have hlenle :
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
-- SORRY'D:             sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
-- SORRY'D:         exact Nat.le_of_add_le_add_right
-- SORRY'D:           (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
-- SORRY'D:       dsimp [extraFuel]
-- SORRY'D:       simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
-- SORRY'D:     have hfuelEq' :
-- SORRY'D:         bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
-- SORRY'D:           1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:       have hbodyFuel' :
-- SORRY'D:           (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
-- SORRY'D:             sizeOf (genParamLoads fn.params ++ bodyStmts) := by
-- SORRY'D:         simpa [compiledFunctionIR] using hbodyFuel
-- SORRY'D:       calc
-- SORRY'D:         bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
-- SORRY'D:             = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
-- SORRY'D:                 simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
-- SORRY'D:         _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
-- SORRY'D:         _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
-- SORRY'D:     have hadequacy :
-- SORRY'D:         Compiler.Proofs.YulGeneration.execIRFunctionFuel
-- SORRY'D:             (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
-- SORRY'D:             (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
-- SORRY'D:           execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
-- SORRY'D:       simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
-- SORRY'D:         (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
-- SORRY'D:           (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
-- SORRY'D:     simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
-- SORRY'D:       hfuelEq', initialState] using hfuel
-- SORRY'D:   simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
-- SORRY'D:     model helperFuel fn tx initialWorld hBody.helperSurfaceClosed] using hlegacy

-- SORRY'D: /-- Function-level Tier 2 bridge from the alternate contract support witness.
-- SORRY'D: This is the selector-dispatched analogue of `supported_function_correct`,
-- SORRY'D: reusing the weakened body interface instead of the default fail-closed state
-- SORRY'D: surface. -/
-- TYPESIG_SORRY: theorem supported_function_correct_except_mapping_writes
-- TYPESIG_SORRY:     (model : CompilationModel)
-- TYPESIG_SORRY:     (selectors : List Nat)
-- TYPESIG_SORRY:     (hSupported : SupportedSpecExceptMappingWrites model selectors)
-- TYPESIG_SORRY:     (fn : FunctionSpec)
-- TYPESIG_SORRY:     (selector : Nat)
-- TYPESIG_SORRY:     (irFn : IRFunction)
-- TYPESIG_SORRY:     (tx : IRTransaction)
-- TYPESIG_SORRY:     (initialWorld : Verity.ContractState)
-- TYPESIG_SORRY:     (bindings : List (String × Nat))
-- TYPESIG_SORRY:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- TYPESIG_SORRY:     (hcompileFn :
-- TYPESIG_SORRY:       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
-- TYPESIG_SORRY:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
-- TYPESIG_SORRY:     (htxNormalized : TxContextNormalized tx)
-- TYPESIG_SORRY:     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
-- TYPESIG_SORRY:     FunctionBody.sourceResultMatchesIRResult
-- TYPESIG_SORRY:       (SourceSemantics.interpretFunction model fn tx initialWorld)
-- TYPESIG_SORRY:       (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   rcases compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors selector fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   have hcorrect :=
-- SORRY'D:     supported_function_correct_with_body_interface_except_mapping_writes
-- SORRY'D:       (model := model)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (helperFuel := hSupported.helperFuel)
-- SORRY'D:       (hnormalized := hSupported.normalizedFields)
-- SORRY'D:       (hnoEvents := hSupported.noEvents)
-- SORRY'D:       (hnoErrors := hSupported.noErrors)
-- SORRY'D:       (hparams := (hSupported.supportedFunctionOfSelectorDispatched hfn).params)
-- SORRY'D:       (hBody := (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
-- SORRY'D:       (hnoConflict := hnoConflict)
-- SORRY'D:       (hsafety := hsafety)
-- SORRY'D:       (selector := selector)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := compiledFunctionIR selector fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:   simpa using hcorrect

-- SORRY'D: /-- Goal-based helper-proof-carrying variant of `supported_function_correct`.
-- SORRY'D: This keeps the current helper-free source-side conservative-extension premise
-- SORRY'D: available as a wrapper, but the exact future helper seam is now the direct
-- SORRY'D: helper-aware body/IR goal exposed by
-- SORRY'D: `supported_function_correct_with_helper_proofs_body_goal`. -/
theorem supported_function_correct_with_helper_proofs_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
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
    (htxNormalized : TxContextNormalized tx)
    (hbodyHelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   classical
-- SORRY'D:   let _ := hvalidateInputs
-- SORRY'D:   have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hinitBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hparamNamesNodup :
-- SORRY'D:       (fn.params.map (·.name)).Nodup :=
-- SORRY'D:     hSupported.selectorFunctionParamNamesNodup hfn
-- SORRY'D:   have hbodyStateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     have hpreboundRuntime :
-- SORRY'D:         FunctionBody.runtimeStateMatchesIR
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:             bindings := [] }
-- SORRY'D:           (prebindRawArgs initialState fn.params) := by
-- SORRY'D:       simpa [initialState] using
-- SORRY'D:         runtimeStateMatchesIR_prebindRawArgs
-- SORRY'D:           (state := initialState)
-- SORRY'D:           (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (params := fn.params)
-- SORRY'D:           (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized)
-- SORRY'D:     exact runtimeStateMatchesIR_applyBindingsToIRState
-- SORRY'D:       (state := prebindRawArgs initialState fn.params)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       hpreboundRuntime
-- SORRY'D:   have hbodyStateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     exact supported_function_param_state_exact
-- SORRY'D:       initialState fn.params bindings hinitBindings hparamNamesNodup hbind
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   let extraFuel := sizeOf irFn.body - irFn.body.length
-- SORRY'D:   have hbodyExtraFuelLower :
-- SORRY'D:       sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     simpa [compiledFunctionIR] using
-- SORRY'D:       yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
-- SORRY'D:   have hbodyWithHelpers :
-- SORRY'D:       SupportedFunctionBodyWithHelpersIRPreservationGoal
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel := by
-- SORRY'D:     by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
-- SORRY'D:     · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
-- SORRY'D:           (model := model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (bodyStmts := bodyStmts)
-- SORRY'D:           (tx := tx)
-- SORRY'D:           (initialWorld := initialWorld)
-- SORRY'D:           (state := ParamLoading.applyBindingsToIRState
-- SORRY'D:             (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:           (bindings := bindings)
-- SORRY'D:           (extraFuel := extraFuel)
-- SORRY'D:           (hextraFuel := hbodyExtraFuelLower)
-- SORRY'D:           (hnormalized := by
-- SORRY'D:             simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:           (hnoEvents := hSupported.noEvents)
-- SORRY'D:           (hnoErrors := hSupported.noErrors)
-- SORRY'D:           hbind
-- SORRY'D:           hterminal
-- SORRY'D:           hbodyCompile
-- SORRY'D:           hbodyStateRuntime
-- SORRY'D:           hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:       refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
-- SORRY'D:       simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
-- SORRY'D:         hbodyHelperGoal.trans hsource
-- SORRY'D:     · have hscope :
-- SORRY'D:           FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
-- SORRY'D:         intro name hmem
-- SORRY'D:         have hmemBindings : name ∈ bindings.map Prod.fst := by
-- SORRY'D:           rw [ParamLoading.bindSupportedParams_names hbind]
-- SORRY'D:           simpa using hmem
-- SORRY'D:         exact lookupBinding?_some_of_mem bindings name hmemBindings
-- SORRY'D:       have hbounded : FunctionBody.bindingsBounded bindings :=
-- SORRY'D:         FunctionBody.bindingsBounded_of_bindSupportedParams hbind
-- SORRY'D:       have hnoConflict :
-- SORRY'D:           firstFieldWriteSlotConflict model.fields = none := by
-- SORRY'D:         simpa [hSupported.normalizedFields] using
-- SORRY'D:           firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
-- SORRY'D:             (spec := model)
-- SORRY'D:             (selectors := selectors)
-- SORRY'D:             hvalidateInputs
-- SORRY'D:       have hhelperFree :
-- SORRY'D:           StmtListHelperFreeStepInterface
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn.params.map (·.name))
-- SORRY'D:             fn.body :=
-- SORRY'D:         hsupportedFn.body.helperFreeStepInterface
-- SORRY'D:           (by simpa [SourceSemantics.effectiveFields] using hnoConflict)
-- SORRY'D:       exact supported_function_body_correct_from_exact_state_generic_with_helpers
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel hbodyExtraFuelLower
-- SORRY'D:         (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:         hSupported.noEvents
-- SORRY'D:         hSupported.noErrors
-- SORRY'D:         hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:         hhelperFree
-- SORRY'D:         hbodyCompile
-- SORRY'D:         hscope
-- SORRY'D:         hbounded
-- SORRY'D:         hbodyStateRuntime
-- SORRY'D:         hbodyStateBindings
-- SORRY'D:   exact supported_function_correct_with_helper_proofs_body_goal
-- SORRY'D:     model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
-- SORRY'D:     bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
-- SORRY'D:     hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyWithHelpers hcalldataSizeFits

-- SORRY'D: /-- Helper-proof-carrying variant of `supported_function_correct`.
-- SORRY'D: This still closes the source-side helper seam through the temporary
-- SORRY'D: helper-excluding `SupportedStmtList` fragment, but now only as a wrapper around
-- SORRY'D: the explicit goal-based theorem surface. -/
theorem supported_function_correct_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
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
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by sorry
-- SORRY'D:   classical
-- SORRY'D:   let _ := hvalidateInputs
-- SORRY'D:   have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
-- SORRY'D:   let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hinitBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
-- SORRY'D:     simpa [initialState] using
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
-- SORRY'D:   have hparamNamesNodup :
-- SORRY'D:       (fn.params.map (·.name)).Nodup :=
-- SORRY'D:     hSupported.selectorFunctionParamNamesNodup hfn
-- SORRY'D:   have hbodyStateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     have hpreboundRuntime :
-- SORRY'D:         FunctionBody.runtimeStateMatchesIR
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:             bindings := [] }
-- SORRY'D:           (prebindRawArgs initialState fn.params) := by
-- SORRY'D:       simpa [initialState] using
-- SORRY'D:         runtimeStateMatchesIR_prebindRawArgs
-- SORRY'D:           (state := initialState)
-- SORRY'D:           (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (params := fn.params)
-- SORRY'D:           (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized)
-- SORRY'D:     exact runtimeStateMatchesIR_applyBindingsToIRState
-- SORRY'D:       (state := prebindRawArgs initialState fn.params)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [] })
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       hpreboundRuntime
-- SORRY'D:   have hbodyStateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings) := by
-- SORRY'D:     exact supported_function_param_state_exact
-- SORRY'D:       initialState fn.params bindings hinitBindings hparamNamesNodup hbind
-- SORRY'D:   have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
-- SORRY'D:       selector fn returns bodyStmts hvalidate hreturns hbodyCompile
-- SORRY'D:   have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
-- SORRY'D:     rw [hcompile] at hcompiled
-- SORRY'D:     injection hcompiled
-- SORRY'D:   let extraFuel := sizeOf irFn.body - irFn.body.length
-- SORRY'D:   have hbodyExtraFuelLower :
-- SORRY'D:       sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
-- SORRY'D:     subst hirFn
-- SORRY'D:     dsimp [extraFuel]
-- SORRY'D:     simpa [compiledFunctionIR] using
-- SORRY'D:       yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
-- SORRY'D:   have hbodyWithHelpers :
-- SORRY'D:       SupportedFunctionBodyWithHelpersIRPreservationGoal
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel := by
-- SORRY'D:     by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
-- SORRY'D:     · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
-- SORRY'D:           (model := model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (bodyStmts := bodyStmts)
-- SORRY'D:           (tx := tx)
-- SORRY'D:           (initialWorld := initialWorld)
-- SORRY'D:           (state := ParamLoading.applyBindingsToIRState
-- SORRY'D:             (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:           (bindings := bindings)
-- SORRY'D:           (extraFuel := extraFuel)
-- SORRY'D:           (hextraFuel := hbodyExtraFuelLower)
-- SORRY'D:           (hnormalized := by
-- SORRY'D:             simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:           (hnoEvents := hSupported.noEvents)
-- SORRY'D:           (hnoErrors := hSupported.noErrors)
-- SORRY'D:           hbind
-- SORRY'D:           hterminal
-- SORRY'D:           hbodyCompile
-- SORRY'D:           hbodyStateRuntime
-- SORRY'D:           hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:       refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
-- SORRY'D:       have hbodyHelperGoal :
-- SORRY'D:           SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             hSupported.helperFuel
-- SORRY'D:             { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:               bindings := bindings }
-- SORRY'D:             fn.body :=
-- SORRY'D:         SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fuel := hSupported.helperFuel)
-- SORRY'D:           (state := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                       bindings := bindings })
-- SORRY'D:           (stmts := fn.body)
-- SORRY'D:           hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:       simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
-- SORRY'D:         hbodyHelperGoal.trans hsource
-- SORRY'D:     · have hscope :
-- SORRY'D:           FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
-- SORRY'D:         intro name hmem
-- SORRY'D:         have hmemBindings : name ∈ bindings.map Prod.fst := by
-- SORRY'D:           rw [ParamLoading.bindSupportedParams_names hbind]
-- SORRY'D:           simpa using hmem
-- SORRY'D:         exact lookupBinding?_some_of_mem bindings name hmemBindings
-- SORRY'D:       have hbounded : FunctionBody.bindingsBounded bindings :=
-- SORRY'D:         FunctionBody.bindingsBounded_of_bindSupportedParams hbind
-- SORRY'D:       have hnoConflict :
-- SORRY'D:           firstFieldWriteSlotConflict model.fields = none := by
-- SORRY'D:         simpa [hSupported.normalizedFields] using
-- SORRY'D:           firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
-- SORRY'D:             (spec := model)
-- SORRY'D:             (selectors := selectors)
-- SORRY'D:             hvalidateInputs
-- SORRY'D:       have hhelperFree :
-- SORRY'D:           StmtListHelperFreeStepInterface
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn.params.map (·.name))
-- SORRY'D:             fn.body :=
-- SORRY'D:         hsupportedFn.body.helperFreeStepInterface
-- SORRY'D:           (by simpa [SourceSemantics.effectiveFields] using hnoConflict)
-- SORRY'D:       exact supported_function_body_correct_from_exact_state_generic_with_helpers
-- SORRY'D:         model fn bodyStmts hSupported.helperFuel tx initialWorld
-- SORRY'D:         (ParamLoading.applyBindingsToIRState
-- SORRY'D:           (prebindRawArgs initialState fn.params) bindings)
-- SORRY'D:         bindings extraFuel hbodyExtraFuelLower
-- SORRY'D:         (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
-- SORRY'D:         hSupported.noEvents
-- SORRY'D:         hSupported.noErrors
-- SORRY'D:         hsupportedFn.body.helperSurfaceClosed
-- SORRY'D:         hhelperFree
-- SORRY'D:         hbodyCompile
-- SORRY'D:         hscope
-- SORRY'D:         hbounded
-- SORRY'D:         hbodyStateRuntime
-- SORRY'D:         hbodyStateBindings
-- SORRY'D:   exact supported_function_correct_with_helper_proofs_body_goal
-- SORRY'D:     model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
-- SORRY'D:     bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
-- SORRY'D:     hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyWithHelpers hcalldataSizeFits

-- SORRY'D: end Function

-- SORRY'D: end Compiler.Proofs.IRGeneration
