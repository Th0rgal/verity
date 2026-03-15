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
      sizeOf (compiledFunctionIR selector spec returns bodyStmts).body + 1 :=
  Nat.add_le_add_right
    (yulStmtList_length_le_sizeOf (compiledFunctionIR selector spec returns bodyStmts).body) 1
private theorem yulStmtList_extraFuel_append_ge
    (pre body : List YulStmt) :
    sizeOf (pre ++ body) - (pre ++ body).length ≥ sizeOf body - body.length := by
  induction pre with
  | nil => simp
  | cons s rest ih =>
      simp only [List.cons_append, List.length_cons]
      have : sizeOf (s :: (rest ++ body)) = 1 + sizeOf s + sizeOf (rest ++ body) := by
        simp [sizeOf, List._sizeOf_1]
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
        sorry
theorem rawArgBindings_names_of_length_le
    (params : List Param)
    (args : List Nat)
    (hlen : params.length ≤ args.length) :
    (rawArgBindings params args).map Prod.fst = params.map Param.name := by
      sorry
theorem rawArgBindings_names_of_bindSupportedParams
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindSupportedParams params args = some bindings) :
    (rawArgBindings params args).map Prod.fst = bindings.map Prod.fst := by
      sorry
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
        sorry
theorem compileFunctionSpec_ok_params
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors selector spec = Except.ok irFn) :
    irFn.params = spec.params.map Param.toIRParam := by
      sorry
theorem compileFunctionSpec_ok_selector
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors selector spec = Except.ok irFn) :
    irFn.selector = selector := by
      sorry
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
        sorry
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
        sorry
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
        sorry
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
        sorry
theorem runtimeStateMatchesIR_applyBindingsToIRState
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (bindings : List (String × Nat)) :
    FunctionBody.runtimeStateMatchesIR fields runtime
      (ParamLoading.applyBindingsToIRState state bindings) := by
        sorry
theorem runtimeStateMatchesIR_prebindRawArgs
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hmatch : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (params : List Param) :
    FunctionBody.runtimeStateMatchesIR fields runtime (prebindRawArgs state params) := by
      sorry
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
      sorry
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
      sorry
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
        sorry
private theorem lookupBinding?_eq_none_of_not_mem
    (bindings : List (String × Nat))
    (queryName : String)
    (hnotmem : queryName ∉ bindings.map Prod.fst) :
    FunctionBody.lookupBinding? bindings queryName = none := by
  simp only [FunctionBody.lookupBinding?]
  have hfind : bindings.find? (fun entry => entry.1 == queryName) = none := by
    induction bindings with
    | nil => rfl
    | cons entry rest ih =>
        simp only [List.map, List.mem_cons, not_or] at hnotmem
        simp only [List.find?]
        have hne : (entry.1 == queryName) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hnotmem.1 h.symm
        simp [hne, ih hnotmem.2]
  simp [hfind]
private theorem lookupBinding?_some_of_mem :
    ∀ (bindings : List (String × Nat)) (queryName : String),
      queryName ∈ bindings.map Prod.fst →
        ∃ value, FunctionBody.lookupBinding? bindings queryName = some value
  | [], _, hmem => absurd hmem (by simp)
  | entry :: rest, queryName, hmem => by
      simp only [List.map, List.mem_cons] at hmem
      by_cases heq : entry.1 = queryName
      · exact ⟨entry.2, by simp [FunctionBody.lookupBinding?, List.find?, heq]⟩
      · have hmem' : queryName ∈ rest.map Prod.fst :=
          hmem.resolve_left (fun h => heq h.symm)
        have ⟨v, hv⟩ := lookupBinding?_some_of_mem rest queryName hmem'
        refine ⟨v, ?_⟩
        simp only [FunctionBody.lookupBinding?, List.find?] at hv ⊢
        have hne : (entry.1 == queryName) = false := by
          simp [beq_eq_false_iff_ne, heq]
        simp [hne, hv]
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
      (FunctionBody.initialIRStateForTx model tx initialWorld) := by
        sorry
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
        sorry
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
          sorry
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
          sorry
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
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
          sorry
private theorem firstFieldWriteSlotConflict_eq_none_of_validateCompileInputs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hvalidate : validateCompileInputs spec selectors = Except.ok ()) :
    firstFieldWriteSlotConflict
        (applySlotAliasRanges spec.fields spec.slotAliasRanges) = none := by
          sorry
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
          sorry
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
          sorry
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
          sorry
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
      sorry
/-- Direct helper-aware function/IR preservation target for the non-core path.
Future helper-summary/rank proofs should feed this theorem via the explicit
helper-aware body/IR goal, rather than via a collapse back to legacy
helper-free source semantics. -/
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
        sorry
/-- Exact helper-aware function/IR preservation target for the non-core path.
This lets callers stay on the exact helper-aware body/IR seam and only collapse
back to the legacy function theorem boundary through compiled-body
disjointness. -/
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
          sorry
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
          sorry
/-- Function-level exact helper-aware theorem over the fully split internal-helper
interfaces, under per-body compiled disjointness. This is the direct wrapper
future rank-induction helper proofs should target: they can discharge the split
statement-list interfaces and avoid hand-assembling the exact body goal. -/
theorem
    supported_function_correct_with_helper_proofs_split_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
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
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level exact helper-aware wrapper that isolates the genuinely new
Tier 4 obligations. The still-vacuous helper-free / expr / structural /
residual interfaces are discharged directly from the existing supported-body
witness, so future rank induction only needs to provide the direct statement-
position helper call and helper-assign interfaces together with compiled-body
disjointness. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
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
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level direct-helper wrapper stated over reusable single-head
helper-step builders instead of preassembled list interfaces. This is the
closest current theorem boundary to the eventual helper-rank induction:
once rank induction can build the exact `Stmt.internalCall` /
`Stmt.internalCallAssign` head steps, the surrounding list-interface plumbing is
discharged here. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
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
    (hcallStep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCall calleeName args)
            compiledIR)
    (hassignStep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level direct-helper wrapper whose head-step assumptions range only
over helper callees that actually appear in `fn.body`. This aligns the exact
Tier 4 theorem seam with `SupportedBodyHelperInterface.calleeRanksDecrease`,
which is also indexed by `helperCallNames fn` rather than arbitrary names. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
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
    (hcallStep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ helperCallNames fn →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCall calleeName args)
            compiledIR)
    (hassignStep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ helperCallNames fn →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level Tier 4 wrapper that consumes a single exact direct-helper
head-step catalog for `fn.body`. This is the proof object future rank
induction should build once `calleeRanksDecrease` is wired non-vacuously. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
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
    (hcatalog :
      DirectInternalHelperHeadStepCatalog
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level Tier 4 wrapper one seam earlier than
`...head_step_catalog...`: callers provide singleton helper-call compilation and
bridge proofs, and the reusable direct-helper catalog is assembled here. This is
the intended theorem boundary for future rank induction. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
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
    (hbridge :
      DirectInternalHelperHeadStepBridgeCatalog
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level Tier 4 wrapper on the callee-local bridge boundary. This
matches `SupportedBodyHelperInterface.calleeRanksDecrease` directly: callers
provide one reusable call bridge and one reusable assign bridge per helper
callee referenced by `fn.body`, and the body-level bridge catalog is assembled
here. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
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
    (hcallee :
      DirectInternalHelperPerCalleeBridgeCatalog
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level Tier 4 wrapper on the assign-only callee-local bridge
boundary. Under the current fragment the direct-helper void-call bridge side is
still vacuous, so callers only need to package one reusable assign bridge per
referenced helper callee. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
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
    (hheadAssignBridge :
      DirectInternalHelperPerCalleeAssignBridgeCatalog
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
/-- Function-level Tier 4 wrapper on the fully split callee-local boundary.
Compile-side obligations for direct helper heads and semantic bridge
obligations are supplied independently, then assembled directly into the exact
body-level head-step catalog future rank induction should build. -/
theorem
    supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
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
    (hheadCompile :
      DirectInternalHelperPerCalleeCompileCatalog
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hheadSemantic :
      DirectInternalHelperPerCalleeSemanticBridgeCatalog
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        fn)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hfnBodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
-- /-- Function-level Tier 4 wrapper that isolates runtime helper witness lookup
-- from the remaining semantic singleton-step work. The runtime witness catalog can
-- be produced independently from a compiled helper table, leaving the semantic
-- core as the only future rank-induction obligation, while this wrapper now lands
-- directly on the exact body-level head-step catalog. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hruntimeWitness :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
--         runtimeContract
--         model
--         fn)
--     (hheadSemantic :
--       DirectInternalHelperPerCalleeSemanticCoreCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Function-level Tier 4 wrapper on the smaller semantic-kernel seam. Source
-- helper witnesses and helper-summary soundness are recovered from the supported
-- function inventory already present at this theorem boundary, so callers only
-- need to provide the irreducible semantic kernel plus compile/runtime catalogs,
-- and this wrapper now lands directly on the exact body-level head-step catalog. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hruntimeWitness :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
--         runtimeContract
--         model
--         fn)
--     (hheadKernel :
--       DirectInternalHelperPerCalleeSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Function-level Tier 4 wrapper one seam earlier than the runtime-witness
-- catalog boundary. The compiled runtime helper table already determines the
-- per-callee runtime witness inventory for `fn`, so callers only need to supply
-- the global table together with the compile catalog and irreducible semantic
-- kernel, and this wrapper now lands directly on the exact body-level head-step
-- catalog. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadKernel :
--       DirectInternalHelperPerCalleeSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Function-level Tier 4 wrapper on the assign-only compile and semantic seam.
-- Under the current fragment the direct-helper void-call compile side is still
-- vacuous, so callers only need to provide assign-side compile obligations
-- together with the assign semantic kernel and runtime helper table, and this
-- wrapper now lands directly on the exact body-level head-step catalog future
-- rank induction should build. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadAssignCompile :
--       DirectInternalHelperPerCalleeAssignCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadAssignKernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Function-level Tier 4 wrapper on the split semantic-kernel boundary. The
-- remaining helper-rank work can now discharge direct helper void calls and
-- direct helper return-binding calls independently, while runtime helper-table
-- facts are still reconstructed mechanically. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadAssignKernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Function-level Tier 4 wrapper on the split semantic-kernel boundary. The
-- remaining helper-rank work can now discharge direct helper void calls and
-- direct helper return-binding calls independently, while runtime helper-table
-- facts are still reconstructed mechanically. -/
-- theorem
--     supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (selector : Nat)
--     (returns : List ParamType)
--     (bodyStmts : List YulStmt)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (bindings : List (String × Nat))
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hvalidate : validateFunctionSpec fn = Except.ok ())
--     (hreturns : functionReturns fn = Except.ok returns)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hcompile :
--       compileFunctionSpec model.fields model.events model.errors selector fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (htxNormalized : TxContextNormalized tx)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadCallKernel :
--       DirectInternalHelperPerCalleeCallSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadAssignKernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body)
--     (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
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
        sorry
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
        sorry
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
          bindings := bindings }
        fn.body)
    (hcalldataSizeFits : TxCalldataSizeFitsEvm tx) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
        sorry
/-- Helper-proof-carrying variant of `supported_function_correct`.
This still closes the source-side helper seam through the temporary
helper-excluding `SupportedStmtList` fragment, but now only as a wrapper around
the explicit goal-based theorem surface. -/
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
        sorry
end Function

end Compiler.Proofs.IRGeneration
