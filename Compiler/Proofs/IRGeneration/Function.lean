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
  tx.chainId < Compiler.Constants.evmModulus ∧
  tx.blobBaseFee < Compiler.Constants.evmModulus

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
          bindings := bindings
          selector := tx.functionSelector }
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
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.runtimeStateMatchesIR
      (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := []
        selector := tx.functionSelector }
      (FunctionBody.initialIRStateForTx model tx initialWorld) := by
  rcases htxNormalized with
    ⟨hsender, hthis, hmsgValue, htimestamp, hnumber, hchain, hblob⟩
  have hsenderEvm : tx.sender < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hsender ⊢
    omega
  have hthisEvm : tx.thisAddress < Compiler.Constants.evmModulus := by
    dsimp [Compiler.Constants.addressModulus, Compiler.Constants.evmModulus] at hthis ⊢
    omega
  have hsenderAddr : tx.sender < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus] using hsender
  have hthisAddr : tx.thisAddress < Verity.Core.Address.modulus := by
    simpa [Verity.Core.Address.modulus, Compiler.Constants.addressModulus] using hthis
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [FunctionBody.initialIRStateForTx, SourceSemantics.effectiveFields,
      SourceSemantics.encodeStorage] using
      (FunctionBody.encodeStorage_withTransactionContext model initialWorld tx).symm
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.wordToAddress]
    symm
    calc
      tx.sender % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
          = tx.sender % Verity.Core.Address.modulus := by
              rw [Nat.mod_eq_of_lt hsenderEvm]
      _ = tx.sender := Nat.mod_eq_of_lt hsenderAddr
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hmsgValue
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.wordToAddress]
    symm
    calc
      tx.thisAddress % Compiler.Constants.evmModulus % Verity.Core.Address.modulus
          = tx.thisAddress % Verity.Core.Address.modulus := by
              rw [Nat.mod_eq_of_lt hthisEvm]
      _ = tx.thisAddress := Nat.mod_eq_of_lt hthisAddr
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt htimestamp
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hnumber
  · simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hchain
  · -- blobBaseFee
    simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
    symm
    exact Nat.mod_eq_of_lt hblob
  · -- selector
    rfl
  · -- calldata
    rfl
  · -- calldataSize
    have : Verity.Core.Uint256.modulus = Compiler.Constants.evmModulus := rfl
    simp only [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext,
      Verity.Core.Uint256.ofNat, this]
    exact Nat.mod_eq_of_lt hcalldataSizeFits
  · -- memory
    funext o
    simp [FunctionBody.initialIRStateForTx, SourceSemantics.withTransactionContext]
  · -- returnValue
    rfl
  · -- events
    change (FunctionBody.initialIRStateForTx model tx initialWorld).events =
      SourceSemantics.encodeEvents
        (SourceSemantics.withTransactionContext initialWorld tx).events
    have : (SourceSemantics.withTransactionContext initialWorld tx).events = initialWorld.events :=
      rfl
    rw [this]
    rfl

/-- The ABI parameter-loading prefix reconstructs exactly the decoded source
bindings for any supported function with pairwise-distinct parameter names. -/
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
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
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
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
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
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
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
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  rcases FunctionBody.exec_compileStmtList_core_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
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
          bindings := []
          selector := tx.functionSelector }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
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
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  have hbounded : FunctionBody.bindingsBounded bindings :=
    FunctionBody.bindingsBounded_of_bindSupportedParams hbind
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] []
        .calldata [] false (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
      (state := state)
      (scope := fn.params.map (·.name))
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hterminal
      FunctionBody.scopeNamesIncluded_refl
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyTerminalCompile, hterminalSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyTerminalCompile
    injection hbodyTerminalCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    have hlenle : bodyStmts.length ≤ sizeOf bodyStmts :=
      yulStmtList_length_le_sizeOf bodyStmts
    omega
  refine ⟨_, _, rfl, rfl, ?_⟩
  simpa [hfuel, sizeSlack] using hterminalSem

private theorem firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hvalidate : validateCompileInputs spec selectors = Except.ok ()) :
    firstFieldWriteSlotConflict
        (applySlotAliasRanges spec.fields spec.slotAliasRanges) = none := by
  exact validateCompileInputs_firstFieldWriteSlotConflict_eq_none hvalidate

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
          bindings := bindings
          selector := tx.functionSelector }
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
          bindings := bindings
          selector := tx.functionSelector }
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
          bindings := bindings
          selector := tx.functionSelector }
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
    (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  classical
  let _ := hvalidateInputs
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
          bindings := []
          selector := tx.functionSelector }
        (prebindRawArgs initialState fn.params) := by
    simpa [initialState] using
      runtimeStateMatchesIR_prebindRawArgs
        (state := initialState)
        (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
        (fields := SourceSemantics.effectiveFields model)
        (params := fn.params)
        (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
          hcalldataSizeFits)
  have hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) :=
    runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings := hstateBindings
  have hbodyStateRuntime := hstateRuntime
  by_cases hcore : FunctionBody.StmtListCompileCore (fn.params.map (·.name)) fn.body
  · let extraFuel := sizeOf irFn.body - irFn.body.length
    have hbodyCorrect :
        ∃ sourceResult irExec,
          SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult ∧
          execIRStmts (bodyStmts.length + extraFuel + 1)
            (ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            bodyStmts = irExec ∧
          FunctionBody.stmtResultMatchesIRExec
            (SourceSemantics.effectiveFields model) sourceResult irExec := by
      exact supported_function_body_correct_from_exact_state_core_extraFuel
        (model := model)
        (fn := fn)
        (bodyStmts := bodyStmts)
        (tx := tx)
        (initialWorld := initialWorld)
        (state := ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        (bindings := bindings)
        (extraFuel := extraFuel)
        (hnormalized := by
          simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
        (hnoEvents := hSupported.noEvents)
        (hnoErrors := hSupported.noErrors)
        hbind hcore hbodyCompile hbodyStateRuntime hbodyStateBindings
    rcases hbodyCorrect with
      ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
    have hfuel :=
      compileFunctionSpec_correct_of_body_supported_extraFuel
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
        (extraFuel := extraFuel)
        hvalidate hreturns
        (by simpa [hSupported.normalizedFields] using hbodyCompile)
        (by simpa [hSupported.normalizedFields] using hcompile)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hsource hbodyExec hmatch
    have hcompiled :=
      compileFunctionSpec_ok_of_components model.fields model.events model.errors
        selector fn returns bodyStmts hvalidate hreturns hbodyCompile
    have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
      rw [hcompile] at hcompiled
      injection hcompiled
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
  · let extraFuel := sizeOf irFn.body - irFn.body.length
    have hbodyExtraFuelLower :
        sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
      have hcompiled :=
        compileFunctionSpec_ok_of_components model.fields model.events model.errors
          selector fn returns bodyStmts hvalidate hreturns hbodyCompile
      have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
        rw [hcompile] at hcompiled
        injection hcompiled
      subst hirFn
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using
        yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
    have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
    have hbodyHelperGoal :
        SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
          model
          (SourceSemantics.effectiveFields model)
          hSupported.helperFuel
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := bindings
            selector := tx.functionSelector }
          fn.body :=
      SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (fuel := hSupported.helperFuel)
        (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings
                    selector := tx.functionSelector })
        (stmts := fn.body)
        hsupportedFn.body.helperSurfaceClosed
    have hbodyCorrect :
        ∃ sourceResult irExec,
          SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body = sourceResult ∧
          execIRStmts (bodyStmts.length + extraFuel + 1)
            (ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            bodyStmts = irExec ∧
          FunctionBody.stmtResultMatchesIRExec
            (SourceSemantics.effectiveFields model) sourceResult irExec := by
      by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
      · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
            (model := model)
            (fn := fn)
            (bodyStmts := bodyStmts)
            (tx := tx)
            (initialWorld := initialWorld)
            (state := ParamLoading.applyBindingsToIRState
              (prebindRawArgs initialState fn.params) bindings)
            (bindings := bindings)
            (extraFuel := extraFuel)
            (hextraFuel := hbodyExtraFuelLower)
            (hnormalized := by
              simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
            (hnoEvents := hSupported.noEvents)
            (hnoErrors := hSupported.noErrors)
            hbind hterminal hbodyCompile hbodyStateRuntime hbodyStateBindings with
          ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
        exact ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      · have hscope :
            FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
          intro name hmem
          have hmemBindings : name ∈ bindings.map Prod.fst := by
            rw [ParamLoading.bindSupportedParams_names hbind]
            simpa using hmem
          exact lookupBinding?_some_of_mem bindings name hmemBindings
        have hbounded : FunctionBody.bindingsBounded bindings :=
          FunctionBody.bindingsBounded_of_bindSupportedParams hbind
        have hnoConflict :
            firstFieldWriteSlotConflict model.fields = none := by
          simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using
            firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
              (spec := model)
              (selectors := selectors)
              hvalidateInputs
        have hhelperFreeFields :
            StmtListHelperFreeStepInterface
              model.fields
              (fn.params.map (·.name))
              fn.body :=
          hsupportedFn.body.helperFreeStepInterface hnoConflict
        have hhelperFree :
            StmtListHelperFreeStepInterface
              (SourceSemantics.effectiveFields model)
              (fn.params.map (·.name))
              fn.body := by
          simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hhelperFreeFields
        rcases supported_function_body_correct_from_exact_state_generic_with_helpers
          model fn bodyStmts hSupported.helperFuel tx initialWorld
          (ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          bindings extraFuel hbodyExtraFuelLower
          (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
          hSupported.noEvents
          hSupported.noErrors
          hsupportedFn.body.helperSurfaceClosed
          hhelperFree
          hbodyCompile
          hscope
          hbounded
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
        refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
        simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
          hbodyHelperGoal.symm.trans hsource
    rcases hbodyCorrect with
      ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
    have hfuel :=
      compileFunctionSpec_correct_of_body_supported_extraFuel
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
        (extraFuel := extraFuel)
        hvalidate hreturns
        (by simpa [hSupported.normalizedFields] using hbodyCompile)
        (by simpa [hSupported.normalizedFields] using hcompile)
        (hSupported.selectorFunctionParamsSupported hfn)
        hcalldataSizeFits hbind hsource hbodyExec hmatch
    have hcompiled :=
      compileFunctionSpec_ok_of_components model.fields model.events model.errors
        selector fn returns bodyStmts hvalidate hreturns hbodyCompile
    have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
      rw [hcompile] at hcompiled
      injection hcompiled
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
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
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  rcases hbodyCorrect with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
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
  have hsourceMatch :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
        (execResultToIRResult initialState irExec) := by
    have hpack :=
      FunctionBody.stmtResultToSourceResult_matches_irExecResult
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (initialWorld := SourceSemantics.withTransactionContext initialWorld tx)
        (rollback := initialState)
        (sourceResult := sourceResult)
        (irResult := irExec)
        hrollbackStorage hrollbackEvents rfl hmatch
    simpa [supportedSourceFunctionSemantics, SourceSemantics.interpretFunctionWithHelpers,
      hbind, hsource, FunctionBody.stmtResultToSourceResult,
      FunctionBody.sourceResultMatchesIRResult, FunctionBody.irResultOfExecResult,
      execResultToIRResult] using hpack
  have hcompiledExec :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          ((genParamLoads fn.params ++ bodyStmts).length + extraFuel + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execResultToIRResult initialState irExec := by
    exact exec_compiledFunctionIR_of_body_extraFuel
      (state := initialState) (selector := selector) (spec := fn)
      (returns := returns) (bodyStmts := bodyStmts) (bindings := bindings)
      (tailResult := irExec) (extraFuel := extraFuel)
      (hSupported.selectorFunctionParamsSupported hfn)
      hcalldataSizeFits hbind hbodyExec
  subst hirFn
  have hcompiledBodyFuel' :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (genParamLoads fn.params ++ bodyStmts) := by
    simpa [compiledFunctionIR] using hcompiledBodyFuel
  have hfuelEq'' :
      extraFuel + (bodyStmts.length + (1 + (genParamLoads fn.params).length)) =
        1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
    have hbodyFuel'' :
        (genParamLoads fn.params).length + bodyStmts.length + extraFuel =
          sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hcompiledBodyFuel'
    omega
  have hadequacy :
      Compiler.Proofs.YulGeneration.execIRFunctionFuel
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
        execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
    simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
      (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
        (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
  have hfuel' :
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel
          (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
    rw [← hcompiledExec] at hsourceMatch
    simpa [compiledFunctionIR, hfuelEq'', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using hsourceMatch
  simpa [hadequacy] using hfuel'
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
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  have hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts := by
    subst hirFn
    simpa [compiledFunctionIR] using
      YulStmtListCallsDisjointFromInternalTable.of_append_prefix
        (contract := runtimeContract)
        (pre := genParamLoads fn.params)
        (suf := bodyStmts)
        hfnBodyDisjoint
  exact
    supported_function_correct_with_helper_proofs_body_goal_and_helper_ir
      model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
      fn selector returns bodyStmts irFn tx initialWorld bindings hfn hvalidate
      hreturns hbodyCompile hcompile hbind htxNormalized extraFuel hcompiledBodyFuel hbodyCorrect
      hbodyDisjoint
      (execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
        runtimeContract
        irFn
        tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        hfnBodyDisjoint)
      hcalldataSizeFits


/-- Function-level Tier 2 bridge for bodies admitted by the alternate
singleton storage-write state interface. This keeps the theorem local to one
function: global normalization and no-event/no-error assumptions remain
explicit, while the body proof can now use the non-vacuous singleton
mapping-write step interfaces instead of contradiction. -/
theorem supported_function_correct_with_body_interface_except_mapping_writes
    (model : CompilationModel)
    (fn : FunctionSpec)
    (helperFuel : Nat)
    (hnormalized :
      applySlotAliasRanges model.fields model.slotAliasRanges = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hparams : SupportedParamProfile fn.params)
    (hBody : SupportedBodyInterfaceExceptMappingWrites model fn)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (selector : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
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
      (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hparams.namesNodup
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    have hpreboundRuntime :
        FunctionBody.runtimeStateMatchesIR
          (SourceSemantics.effectiveFields model)
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := []
            selector := tx.functionSelector }
          (prebindRawArgs initialState fn.params) := by
      simpa [initialState] using
        runtimeStateMatchesIR_prebindRawArgs
          (state := initialState)
          (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
          (fields := SourceSemantics.effectiveFields model)
          (params := fn.params)
          (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized hcalldataSizeFits)
    exact runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    exact supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    subst hirFn
    dsimp [extraFuel]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
    subst hirFn
    dsimp [extraFuel]
    have hlenle :
        (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      exact Nat.le_of_add_le_add_right
        (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
    simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
  have hbodyWithHelpers :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel := by
    by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
    · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
          (model := model)
          (fn := fn)
          (bodyStmts := bodyStmts)
          (tx := tx)
          (initialWorld := initialWorld)
          (state := ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          (bindings := bindings)
          (extraFuel := extraFuel)
          (hextraFuel := hbodyExtraFuelLower)
          (hnormalized := by
            simpa [SourceSemantics.effectiveFields] using hnormalized)
          (hnoEvents := hnoEvents)
          (hnoErrors := hnoErrors)
          hbind
          hterminal
          hbodyCompile
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
      have hhelperGoal :
          SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
            model
            (SourceSemantics.effectiveFields model)
            helperFuel
            { world := SourceSemantics.withTransactionContext initialWorld tx
              bindings := bindings
              selector := tx.functionSelector }
            fn.body :=
        SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
          (spec := model)
          (fields := SourceSemantics.effectiveFields model)
          (fuel := helperFuel)
          (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                      bindings := bindings
                      selector := tx.functionSelector })
          (stmts := fn.body)
          hBody.helperSurfaceClosed
      simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
        hhelperGoal.trans hsource
    · have hscope :
          FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
        intro name hmem
        have hmemBindings : name ∈ bindings.map Prod.fst := by
          rw [ParamLoading.bindSupportedParams_names hbind]
          simpa using hmem
        exact lookupBinding?_some_of_mem bindings name hmemBindings
      have hbounded : FunctionBody.bindingsBounded bindings :=
        FunctionBody.bindingsBounded_of_bindSupportedParams hbind
      have hhelperFree :
          StmtListHelperFreeStepInterface
            (SourceSemantics.effectiveFields model)
            (fn.params.map (·.name))
            fn.body := by
        simpa [SourceSemantics.effectiveFields, hnormalized] using
          hBody.helperFreeStepInterface hnoConflict hsafety
      exact supported_function_body_correct_from_exact_state_generic_with_helpers
        model fn bodyStmts helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel hbodyExtraFuelLower
        (by simpa [SourceSemantics.effectiveFields] using hnormalized)
        hnoEvents
        hnoErrors
        hBody.helperSurfaceClosed
        hhelperFree
        hbodyCompile
        hscope
        hbounded
        hbodyStateRuntime
        hbodyStateBindings
  rcases hbodyWithHelpers with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hhelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (fuel := helperFuel)
      (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                  bindings := bindings
                  selector := tx.functionSelector })
      (stmts := fn.body)
      hBody.helperSurfaceClosed
  have hsourceLegacy :
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body = sourceResult := by
    simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
      hhelperGoal.symm.trans hsource
  have hlegacy :
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    have hfuel :=
      compileFunctionSpec_correct_of_body_normalized_extraFuel
        model
        hnormalized
        selector fn irFn returns bodyStmts tx initialWorld sourceResult irExec
        bindings extraFuel hvalidate hreturns
        (by simpa [hnormalized] using hbodyCompile)
        (by simpa [hnormalized] using hcompile)
        hparams.supported
        hcalldataSizeFits
        hbind
        hsourceLegacy
        hbodyExec
        hmatch
    subst hirFn
    have hbodyFuel :
        (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      have hlenle :
          (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
            sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
        exact Nat.le_of_add_le_add_right
          (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
      dsimp [extraFuel]
      simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
    have hfuelEq' :
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel)) =
          1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by
      have hbodyFuel' :
          (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
            sizeOf (genParamLoads fn.params ++ bodyStmts) := by
        simpa [compiledFunctionIR] using hbodyFuel
      calc
        bodyStmts.length + (1 + ((genParamLoads fn.params).length + extraFuel))
            = ((genParamLoads fn.params ++ bodyStmts).length + extraFuel) + 1 := by
                simp [List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        _ = sizeOf (genParamLoads fn.params ++ bodyStmts) + 1 := by rw [hbodyFuel']
        _ = 1 + sizeOf (genParamLoads fn.params ++ bodyStmts) := by omega
    have hadequacy :
        Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState =
          execIRFunction (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState := by
      simpa [Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate_goal] using
        (Compiler.Proofs.YulGeneration.execIRFunctionFuel_adequate
          (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState)
    have hfuel' :
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (Compiler.Proofs.YulGeneration.execIRFunctionFuel
            (sizeOf (compiledFunctionIR selector fn returns bodyStmts).body + 1)
            (compiledFunctionIR selector fn returns bodyStmts) tx.args initialState) := by
      simpa [compiledFunctionIR, List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
        hfuelEq'] using hfuel
    simpa [hadequacy] using hfuel'
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model helperFuel fn tx initialWorld hBody.helperSurfaceClosed] using hlegacy

/-- Function-level Tier 2 bridge from the alternate contract support witness.
This is the selector-dispatched analogue of `supported_function_correct`,
reusing the weakened body interface instead of the default fail-closed state
surface. -/
theorem supported_function_correct_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (selector : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (htxNormalized : TxContextNormalized tx)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases compileFunctionSpec_ok_components
      model.fields model.events model.errors selector fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hcorrect :=
    supported_function_correct_with_body_interface_except_mapping_writes
      (model := model)
      (fn := fn)
      (helperFuel := hSupported.helperFuel)
      (hnormalized := hSupported.normalizedFields)
      (hnoEvents := hSupported.noEvents)
      (hnoErrors := hSupported.noErrors)
      (hparams := (hSupported.supportedFunctionOfSelectorDispatched hfn).params)
      (hBody := (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (selector := selector)
      (returns := returns)
      (bodyStmts := bodyStmts)
      (irFn := compiledFunctionIR selector fn returns bodyStmts)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hvalidate := hvalidate)
      (hreturns := hreturns)
      (hbodyCompile := hbodyCompile)
      (hcompile := by simpa using hcompileFn)
      (hbind := hbind)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    model hSupported.helperFuel fn tx initialWorld
    (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed] using hcorrect

/-- Goal-based helper-proof-carrying variant of `supported_function_correct`.
This keeps the current helper-free source-side conservative-extension premise
available as a wrapper, but the exact future helper seam is now the direct
helper-aware body/IR goal exposed by
`supported_function_correct_with_helper_proofs_body_goal`. -/
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
          bindings := bindings
          selector := tx.functionSelector }
        fn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  classical
  let _ := hvalidateInputs
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  let initialState := FunctionBody.initialIRStateForTx model tx initialWorld
  have hinitBindings :
      FunctionBody.bindingsExactlyMatchIRVars [] initialState := by
    simpa [initialState] using
      FunctionBody.bindingsExactlyMatchIRVars_nil_initialIRStateForTx model tx initialWorld
  have hparamNamesNodup :
      (fn.params.map (·.name)).Nodup :=
    hSupported.selectorFunctionParamNamesNodup hfn
  have hbodyStateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := []
          selector := tx.functionSelector }
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    have hpreboundRuntime :
        FunctionBody.runtimeStateMatchesIR
          (SourceSemantics.effectiveFields model)
          { world := SourceSemantics.withTransactionContext initialWorld tx
            bindings := []
            selector := tx.functionSelector }
          (prebindRawArgs initialState fn.params) := by
      simpa [initialState] using
        runtimeStateMatchesIR_prebindRawArgs
          (state := initialState)
          (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
          (fields := SourceSemantics.effectiveFields model)
          (params := fn.params)
          (initialIRStateForTx_matches_runtime model tx initialWorld htxNormalized
            hcalldataSizeFits)
    exact runtimeStateMatchesIR_applyBindingsToIRState
      (state := prebindRawArgs initialState fn.params)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx, bindings := [], selector := tx.functionSelector })
      (fields := SourceSemantics.effectiveFields model)
      (bindings := bindings)
      hpreboundRuntime
  have hbodyStateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings) := by
    exact supported_function_param_state_exact
      initialState fn.params bindings hinitBindings hparamNamesNodup hbind
  have hcompiled := compileFunctionSpec_ok_of_components model.fields model.events model.errors
      selector fn returns bodyStmts hvalidate hreturns hbodyCompile
  have hirFn : irFn = compiledFunctionIR selector fn returns bodyStmts := by
    rw [hcompile] at hcompiled
    injection hcompiled
  let extraFuel := sizeOf irFn.body - irFn.body.length
  have hbodyExtraFuelLower :
      sizeOf bodyStmts - bodyStmts.length ≤ extraFuel := by
    subst hirFn
    dsimp [extraFuel]
    simpa [compiledFunctionIR] using
      yulStmtList_extraFuel_append_ge (genParamLoads fn.params) bodyStmts
  have hbodyWithHelpers :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel := by
    by_cases hterminal : FunctionBody.StmtListTerminalCore (fn.params.map (·.name)) fn.body
    · rcases supported_function_body_correct_from_exact_state_terminal_core_extraFuel
          (model := model)
          (fn := fn)
          (bodyStmts := bodyStmts)
          (tx := tx)
          (initialWorld := initialWorld)
          (state := ParamLoading.applyBindingsToIRState
            (prebindRawArgs initialState fn.params) bindings)
          (bindings := bindings)
          (extraFuel := extraFuel)
          (hextraFuel := hbodyExtraFuelLower)
          (hnormalized := by
            simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
          (hnoEvents := hSupported.noEvents)
          (hnoErrors := hSupported.noErrors)
          hbind
          hterminal
          hbodyCompile
          hbodyStateRuntime
          hbodyStateBindings with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
      refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
      simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
        hbodyHelperGoal.trans hsource
    · have hscope :
          FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings := by
        intro name hmem
        have hmemBindings : name ∈ bindings.map Prod.fst := by
          rw [ParamLoading.bindSupportedParams_names hbind]
          simpa using hmem
        exact lookupBinding?_some_of_mem bindings name hmemBindings
      have hbounded : FunctionBody.bindingsBounded bindings :=
        FunctionBody.bindingsBounded_of_bindSupportedParams hbind
      have hnoConflict :
          firstFieldWriteSlotConflict model.fields = none := by
        simpa [hSupported.normalizedFields] using
          firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
            (spec := model)
            (selectors := selectors)
            hvalidateInputs
      have hhelperFreeFields :
          StmtListHelperFreeStepInterface
            model.fields
            (fn.params.map (·.name))
            fn.body :=
        hsupportedFn.body.helperFreeStepInterface hnoConflict
      have hhelperFree :
          StmtListHelperFreeStepInterface
            (SourceSemantics.effectiveFields model)
            (fn.params.map (·.name))
            fn.body := by
        simpa [SourceSemantics.effectiveFields, hSupported.normalizedFields] using hhelperFreeFields
      exact supported_function_body_correct_from_exact_state_generic_with_helpers
        model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (prebindRawArgs initialState fn.params) bindings)
        bindings extraFuel hbodyExtraFuelLower
        (by simpa [SourceSemantics.effectiveFields] using hSupported.normalizedFields)
        hSupported.noEvents
        hSupported.noErrors
        hsupportedFn.body.helperSurfaceClosed
        hhelperFree
        hbodyCompile
        hscope
        hbounded
        hbodyStateRuntime
        hbodyStateBindings
  have hbodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
    subst hirFn
    dsimp [extraFuel]
    have hlenle :
        (compiledFunctionIR selector fn returns bodyStmts).body.length ≤
          sizeOf (compiledFunctionIR selector fn returns bodyStmts).body := by
      exact Nat.le_of_add_le_add_right
        (compiledFunctionIR_body_length_le_sizeOf selector fn returns bodyStmts)
    simpa [compiledFunctionIR] using Nat.add_sub_of_le hlenle
  exact supported_function_correct_with_helper_proofs_body_goal
    model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
    bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
    hcompile hbind htxNormalized extraFuel hbodyFuel hbodyWithHelpers hcalldataSizeFits
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
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  classical
  let _ := hvalidateInputs
  have hsupportedFn := hSupported.supportedFunctionOfSelectorDispatched hfn
  have hbodyHelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        hSupported.helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings
          selector := tx.functionSelector }
        fn.body :=
    SourceSemantics.execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (fuel := hSupported.helperFuel)
      (state := { world := SourceSemantics.withTransactionContext initialWorld tx
                  bindings := bindings
                  selector := tx.functionSelector })
      (stmts := fn.body)
      hsupportedFn.body.helperSurfaceClosed
  exact supported_function_correct_with_helper_proofs_goal
    model selectors hSupported hHelperProofs hvalidateInputs fn selector returns
    bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns hbodyCompile
    hcompile hbind htxNormalized hbodyHelperGoal hcalldataSizeFits
