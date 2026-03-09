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

@[simp] theorem prebindRawArgs_calldata (state : IRState) (params : List Param) :
    (prebindRawArgs state params).calldata = state.calldata := by
  unfold prebindRawArgs
  induction (params.map Param.toIRParam).zip state.calldata generalizing state with
  | nil =>
      rfl
  | cons entry rest ih =>
      simpa [List.foldl, IRState.setVar] using ih (state.setVar entry.1.name entry.2)

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
    (hcalldataSizeFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
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
    (hcalldataSizeFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
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

end Function

end Compiler.Proofs.IRGeneration
