import Compiler.Proofs.IRGeneration.Function
import Compiler.Proofs.IRGeneration.ParamLoading

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace Dispatch

def runtimeContractOfFunctions (name : String) (functions : List IRFunction) : IRContract :=
  { name := name
    deploy := []
    constructorPayable := false
    functions := functions
    fallbackEntrypoint := none
    receiveEntrypoint := none
    usesMapping := false
    internalFunctions := [] }

@[simp] theorem runtimeContractOfFunctions_internalFunctions
    (name : String) (functions : List IRFunction) :
    (runtimeContractOfFunctions name functions).internalFunctions = [] := rfl

theorem runtimeContractOfFunctions_legacyCompatible
    (name : String) (functions : List IRFunction)
    (hlegacyBodies : ∀ fn ∈ functions, LegacyCompatibleExternalStmtList fn.body) :
    LegacyCompatibleRuntimeContract (runtimeContractOfFunctions name functions) := by
  refine ⟨runtimeContractOfFunctions_internalFunctions name functions, ?_⟩
  intro fn hmem
  exact hlegacyBodies fn hmem

theorem runtimeContractOfFunctions_disjoint
    (name : String) (functions : List IRFunction)
    (hdisjointBodies :
      ∀ fn ∈ functions,
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions name functions)
          fn.body) :
    DisjointRuntimeContract (runtimeContractOfFunctions name functions) := by
  intro fn hmem
  exact hdisjointBodies fn hmem

private theorem decodeSupportedParamWord_some_of_supported
    (ty : ParamType) (word : Nat) (hsupported : SupportedExternalParamType ty) :
    ∃ value, SourceSemantics.decodeSupportedParamWord ty word = some value := by
  -- TEMPORARY SORRY: this witness lemma needs to be updated for the current
  -- supported external parameter surface, which now includes additional cases
  -- such as `int256`. The clean fix should construct explicit witnesses for
  -- every supported constructor instead of discharging new branches by
  -- contradiction.
  sorry

private theorem bindSupportedParams_some_of_supported
    (params : List Param) (args : List Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalParamType param.ty)
    (hlen : params.length ≤ args.length) :
    ∃ bindings, SourceSemantics.bindSupportedParams params args = some bindings := by
  induction params generalizing args with
  | nil =>
      exact ⟨[], by simp [SourceSemantics.bindSupportedParams]⟩
  | cons param rest ih =>
      cases args with
      | nil =>
          cases hlen
      | cons arg restArgs =>
          have hparam : SupportedExternalParamType param.ty := hsupported param (by simp)
          rcases decodeSupportedParamWord_some_of_supported param.ty arg hparam with ⟨value, hdecode⟩
          have hrestSupported : ∀ next ∈ rest, SupportedExternalParamType next.ty := by
            intro next hnext
            exact hsupported next (by simp [hnext])
          have hrestLen : rest.length ≤ restArgs.length := Nat.le_of_succ_le_succ hlen
          rcases ih restArgs hrestSupported hrestLen with ⟨bindings, hbindings⟩
          refine ⟨(param.name, value) :: bindings, ?_⟩
          simp [SourceSemantics.bindSupportedParams, hdecode, hbindings]

private theorem find_compiledFunction_some_of_forall₂
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat)
    {pairs : List (FunctionSpec × Nat)} {irFns : List IRFunction}
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec fields events errors entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    {fn : FunctionSpec} {sel : Nat}
    (hfind :
      pairs.find? (fun entry => entry.2 == selector) = some (fn, sel)) :
    ∃ irFn,
      irFns.find? (fun irFn => irFn.selector == selector) = some irFn ∧
      compileFunctionSpec fields events errors sel fn = Except.ok irFn := by
  induction hcompiled generalizing fn sel with
  | nil =>
      simp at hfind
  | @cons entry irFn pairs irFns hhead hrest ih =>
      rcases entry with ⟨headFn, headSel⟩
      by_cases hselEq : headSel = selector
      · simp [hselEq] at hfind
        rcases hfind with ⟨rfl, rfl⟩
        have hhead' : compileFunctionSpec fields events errors selector headFn = Except.ok irFn := by
          simpa [hselEq] using hhead
        refine ⟨irFn, ?_, hhead'⟩
        have hselector : irFn.selector = selector := by
          calc
            irFn.selector = headSel :=
              Function.compileFunctionSpec_ok_selector
                fields events errors headSel headFn irFn hhead
            _ = selector := hselEq
        simp [hselector]
      · have hfindRest :
            pairs.find? (fun entry => entry.2 == selector) = some (fn, sel) := by
          simpa [hselEq] using hfind
        rcases ih hfindRest with ⟨irFn', hfindIr, hcompile⟩
        refine ⟨irFn', ?_, hcompile⟩
        have hheadSelector : irFn.selector = headSel := by
          exact Function.compileFunctionSpec_ok_selector
            fields events errors headSel headFn irFn hhead
        simp [hselEq, hheadSelector, hfindIr]

private theorem find_compiledFunction_none_of_forall₂
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat)
    {pairs : List (FunctionSpec × Nat)} {irFns : List IRFunction}
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec fields events errors entry.2 entry.1 = Except.ok irFn)
        pairs irFns)
    (hfind :
      pairs.find? (fun entry => entry.2 == selector) = none) :
    irFns.find? (fun irFn => irFn.selector == selector) = none := by
  induction hcompiled with
  | nil =>
      simp
  | @cons entry irFn pairs irFns hhead hrest ih =>
      rcases entry with ⟨headFn, headSel⟩
      by_cases hselEq : headSel = selector
      · simp [hselEq] at hfind
      · have hfindRest : pairs.find? (fun entry => entry.2 == selector) = none := by
          simpa [hselEq] using hfind
        have hheadSelector : irFn.selector = headSel := by
          exact Function.compileFunctionSpec_ok_selector
            fields events errors headSel headFn irFn hhead
        simp [hselEq, hheadSelector, ih hfindRest]

theorem interpretContract_correct_of_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn => compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  let pairs := SourceSemantics.selectorFunctionPairs model selectors
  have hinterp :
      interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      match irFns.find? (fun irFn => irFn.selector == tx.functionSelector) with
      | some irFn =>
          if irFn.params.length ≤ tx.args.length then
            execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)
          else
            { success := false
              returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
      | none =>
          { success := false
            returnValue := none
            finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            finalMappings := Compiler.Proofs.storageAsMappings
              (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events } := by
        rfl
  unfold SourceSemantics.interpretContract SourceSemantics.findFunctionBySelector
  cases hfindPairs :
      pairs.find? (fun entry => entry.2 == tx.functionSelector) with
  | none =>
      have hfindIr :
          irFns.find? (fun irFn => irFn.selector == tx.functionSelector) = none :=
        find_compiledFunction_none_of_forall₂
          model.fields model.events model.errors tx.functionSelector hcompiled hfindPairs
      rw [hinterp, hfindIr]
      simp [hfindPairs, FunctionBody.sourceResultMatchesIRResult,
        SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
        FunctionBody.encodeStorage_withTransactionContext,
        FunctionBody.encodeEvents_withTransactionContext]
  | some pair =>
      rcases pair with ⟨fn, sel⟩
      rcases find_compiledFunction_some_of_forall₂
          model.fields model.events model.errors tx.functionSelector hcompiled hfindPairs with
        ⟨irFn, hfindIr, hcompileFn⟩
      have hpairMem : (fn, sel) ∈ pairs := List.mem_of_find?_eq_some hfindPairs
      have hfnMem : fn ∈ selectorDispatchedFunctions model := by
        simpa [pairs, SourceSemantics.selectorFunctionPairs] using (List.of_mem_zip hpairMem).1
      have hparamsEq :
          irFn.params = fn.params.map Param.toIRParam :=
        Function.compileFunctionSpec_ok_params
          model.fields model.events model.errors sel fn irFn hcompileFn
      have hlenEq : irFn.params.length = fn.params.length := by
        simpa [hparamsEq]
      by_cases hlen : fn.params.length ≤ tx.args.length
      · rcases bindSupportedParams_some_of_supported fn.params tx.args
            (hparamsSupported fn hfnMem) hlen with ⟨bindings, hbindings⟩
        have hmatch := hfunction fn sel irFn bindings hfnMem hcompileFn hbindings
        have hlenIr : irFn.params.length ≤ tx.args.length := by
          simpa [hlenEq] using hlen
        rw [hinterp, hfindIr]
        simpa [hfindPairs, hlenIr] using hmatch
      · have hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none := by
          cases hbind : SourceSemantics.bindSupportedParams fn.params tx.args with
          | none =>
              rfl
          | some bindings =>
              exfalso
              exact hlen (ParamLoading.bindSupportedParams_some_length hbind)
        have hlenIr : ¬ irFn.params.length ≤ tx.args.length := by
          simpa [hlenEq] using hlen
        rw [hinterp, hfindIr]
        simp [SourceSemantics.interpretFunction, hbindNone, hlenIr,
          FunctionBody.sourceResultMatchesIRResult, SourceSemantics.revertedResult,
          FunctionBody.initialIRStateForTx, FunctionBody.encodeStorage_withTransactionContext,
          FunctionBody.encodeEvents_withTransactionContext]

/-- Helper-proof-carrying wrapper for the dispatch theorem.
The current proof still reduces helper-aware source semantics to the legacy
helper-free semantics via the helper-excluding `SupportedStmtList` body
fragment, so the additional helper proof slot is present to stabilize the
theorem boundary rather than to widen the proved fragment today. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
      (hSupported := hSupported) hfn tx initialWorld] using
      hfunction fn sel irFn bindings hfn hcompileFn hbind
  have hlegacy :=
    interpretContract_correct_of_compiled_functions
      (model := model)
      (selectors := selectors)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hlegacyFunction)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hlegacy

private theorem legacy_function_correct_of_supportedSourceFunctionSemanticsExceptMappingWrites
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    ∀ fn sel irFn bindings,
      fn ∈ selectorDispatchedFunctions model →
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  intro fn sel irFn bindings hfn hcompileFn hbind
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using
    hfunction fn sel irFn bindings hfn hcompileFn hbind

/-- Tier 2 dispatch wrapper for the alternate singleton-storage-write support
witness. This keeps the public theorem surface aligned with the ordinary
`SupportedSpec` path while reusing the existing legacy dispatch skeleton. -/
theorem interpretContract_correct_of_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  simpa [supportedSourceContractSemanticsExceptMappingWrites_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using
    (interpretContract_correct_of_compiled_functions
      (model := model)
      (selectors := selectors)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction :=
        legacy_function_correct_of_supportedSourceFunctionSemanticsExceptMappingWrites
          (model := model)
          (selectors := selectors)
          (hSupported := hSupported)
          (tx := tx)
          (initialWorld := initialWorld)
          hfunction))

/-- Helper-aware compiled-side wrapper for the dispatch theorem.
This packages the remaining compiled-side retarget work as a single
conservative-extension equality for the runtime contract produced by
`runtimeContractOfFunctions`. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hhelperIR :
      interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    interpretContract_correct_of_compiled_functions_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      hHelperProofs
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [hhelperIR] using hlegacy
-- SORRY'D:   have hlegacy :=
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hfunction)
-- SORRY'D:   simpa [hhelperIR] using hlegacy

-- SORRY'D: /-- Structured helper-aware dispatch wrapper.
-- SORRY'D: This consumes the named compiled-side conservative-extension goal together with
-- SORRY'D: the runtime-contract compatibility witness, instead of requiring callers to
-- SORRY'D: restate the resulting equality manually. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies :
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body)
    (hhelperIRGoal :
      InterpretIRWithInternalsZeroConservativeExtensionGoal
        (runtimeContractOfFunctions model.name irFns)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hhelperIR :=
      hhelperIRGoal
        (runtimeContractOfFunctions_legacyCompatible model.name irFns hlegacyBodies)
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Disjointness-based helper-aware dispatch wrapper.
This drops the stronger legacy-compatibility runtime assumption in favor of the
compiled-side condition actually needed by
`interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint`. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hdisjointIR :
      DisjointRuntimeContract (runtimeContractOfFunctions model.name irFns)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hhelperIR :=
      interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed
        (runtimeContractOfFunctions model.name irFns)
        hdisjointIR
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))
-- SORRY'D:   exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (irFns := irFns)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (hcompiled := hcompiled)
-- SORRY'D:     (hparamsSupported := hparamsSupported)
-- SORRY'D:     (hfunction := hfunction)
-- SORRY'D:     (hhelperIR :=
-- SORRY'D:       interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         hdisjointIR
-- SORRY'D:         tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld))

-- SORRY'D: /-- Narrow direct-helper-aware dispatch wrapper aligned with the current Tier 4
-- SORRY'D: function theorem seam. Callers stay on `execIRFunctionWithInternals` for each
-- SORRY'D: selected function, while the wrapper discharges the older dispatch theorem
-- SORRY'D: through per-body disjointness instead of requiring a manual whole-contract
-- SORRY'D: compiled-side equality premise. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hfunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)))
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hlegacyFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunction irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     have hmatch :=
-- SORRY'D:       hfunction fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     have hfnBodyDisjoint :
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body :=
-- SORRY'D:       hbodyDisjoint fn sel irFn hfn hcompileFn
-- SORRY'D:     have hhelperEq :
-- SORRY'D:         execIRFunctionWithInternals (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:           irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld) =
-- SORRY'D:         execIRFunction irFn tx.args
-- SORRY'D:           (FunctionBody.initialIRStateForTx model tx initialWorld) :=
-- SORRY'D:       execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         irFn
-- SORRY'D:         tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)
-- SORRY'D:         hfnBodyDisjoint
-- SORRY'D:     simpa [hhelperEq] using hmatch
-- SORRY'D:   have hdisjointIR :
-- SORRY'D:       DisjointRuntimeContract (runtimeContractOfFunctions model.name irFns) := by
-- SORRY'D:     intro irFn hmem
-- SORRY'D:     rcases exists_left_of_forall₂_mem_right hcompiled hmem with ⟨entry, hmemEntry, hcompileFn⟩
-- SORRY'D:     rcases entry with ⟨fn, sel⟩
-- SORRY'D:     have hfn :
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model := by
-- SORRY'D:       simpa [SourceSemantics.selectorFunctionPairs] using
-- SORRY'D:         (List.mem_of_mem_zipLeft hmemEntry : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     exact hbodyDisjoint fn sel irFn hfn hcompileFn
-- SORRY'D:   exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (irFns := irFns)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (hcompiled := hcompiled)
-- SORRY'D:     (hparamsSupported := hparamsSupported)
-- SORRY'D:     (hfunction := hlegacyFunction)
-- SORRY'D:     (hdisjointIR := hdisjointIR)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper stated over reusable single-head direct
-- SORRY'D: helper step builders. This lets future rank-decreasing helper induction target
-- SORRY'D: the public whole-contract theorem boundary directly, without first assembling
-- SORRY'D: per-function list interfaces. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCall calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (sel := sel)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hcompileFn := hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (hcallStep := hcallStep)
-- SORRY'D:       (hassignStep := hassignStep)
-- SORRY'D:       (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:       (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper whose direct-helper head-step assumptions are
-- SORRY'D: indexed only by helper callees that actually occur in each function body. This
-- SORRY'D: matches the `calleeRanksDecrease` inventory that future helper-rank induction
-- SORRY'D: will consume. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:           calleeName ∈ helperCallNames fn →
-- SORRY'D:           ∃ compiledIR,
-- SORRY'D:             CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:               (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:               model
-- SORRY'D:               (SourceSemantics.effectiveFields model)
-- SORRY'D:               scope
-- SORRY'D:               (Stmt.internalCall calleeName args)
-- SORRY'D:               compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:           calleeName ∈ helperCallNames fn →
-- SORRY'D:           ∃ compiledIR,
-- SORRY'D:             CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:               (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:               model
-- SORRY'D:               (SourceSemantics.effectiveFields model)
-- SORRY'D:               scope
-- SORRY'D:               (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:               compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (sel := sel)
-- SORRY'D:       (irFn := irFn)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hcompileFn := hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (hcallStep := hcallStep fn hfn)
-- SORRY'D:       (hassignStep := hassignStep fn hfn)
-- SORRY'D:       (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:       (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper that consumes one direct-helper head-step
-- SORRY'D: catalog per selector-dispatched function. This is the whole-contract theorem
-- SORRY'D: boundary future helper-rank induction should target. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hcatalog :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperHeadStepCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hcatalog := hcatalog fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper one seam earlier than
-- SORRY'D: `...head_step_catalog...`: callers provide a singleton direct-helper bridge
-- SORRY'D: catalog per dispatched function, and the reusable head-step catalogs are
-- SORRY'D: assembled here before dispatch-level reuse. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hbridge :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperHeadStepBridgeCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hcatalog := by
-- SORRY'D:         intro fn hfn
-- SORRY'D:         exact
-- SORRY'D:           directInternalHelperHeadStepCatalog_of_bridgeCatalog
-- SORRY'D:             (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hbridge fn hfn))
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the callee-local bridge boundary. This
-- SORRY'D: matches `calleeRanksDecrease` directly: callers provide one reusable bridge
-- SORRY'D: object per helper callee referenced by each dispatched body, and the body-level
-- SORRY'D: bridge catalogs are assembled here mechanically before dispatch-level reuse. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hcallee :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeBridgeCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hcatalog :=
-- SORRY'D:           directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
-- SORRY'D:             (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hcallee fn hfn))
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the assign-only callee-local bridge
-- SORRY'D: boundary. Under the current fragment, each dispatched body only needs reusable
-- SORRY'D: helper-return-binding bridges; the void-call half is still vacuous and is
-- SORRY'D: reassembled mechanically here, and the wrapper now lands directly on the exact
-- SORRY'D: contract-level head-step catalog target instead of routing through the narrower
-- SORRY'D: assign-bridge theorem chain. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hheadAssignBridge :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeAssignBridgeCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hcatalog :=
-- SORRY'D:           directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
-- SORRY'D:             (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hSupported.supportedFunctionOfSelectorDispatched hfn).body
-- SORRY'D:             (hheadAssignBridge fn hfn))
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the fully split callee-local boundary.
-- SORRY'D: Each dispatched body can now provide direct-helper head compilation and
-- SORRY'D: semantic bridge catalogs independently, and dispatch-level reuse assembles the
-- SORRY'D: existing per-callee bridge catalog mechanically. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeSemanticBridgeCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hheadCompile := hheadCompile fn hfn)
-- SORRY'D:         (hheadSemantic := hheadSemantic fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper that separates runtime helper lookup from the
-- SORRY'D: remaining semantic singleton-step work. Each body can provide a runtime witness
-- SORRY'D: catalog independently from its semantic core, and dispatch-level reuse
-- SORRY'D: reassembles the existing bridge boundary mechanically. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeSemanticCoreCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hheadCompile := hheadCompile fn hfn)
-- SORRY'D:         (hruntimeWitness := hruntimeWitness fn hfn)
-- SORRY'D:         (hheadSemantic := hheadSemantic fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the smaller semantic-kernel seam. This
-- SORRY'D: keeps the dispatch boundary aligned with the actual new proof work: compile
-- SORRY'D: catalog, runtime helper witnesses, and the irreducible semantic kernel. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hheadCompile := hheadCompile fn hfn)
-- SORRY'D:         (hruntimeWitness := hruntimeWitness fn hfn)
-- SORRY'D:         (hheadKernel := hheadKernel fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper one seam earlier than the per-function
-- SORRY'D: runtime-witness catalog boundary. A single runtime helper table for the
-- SORRY'D: compiled contract is enough to derive each function's callee-local runtime
-- SORRY'D: inventory, leaving only the compile catalogs and semantic kernels explicit. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hRuntime :
-- SORRY'D:       SupportedRuntimeHelperTableInterface
-- SORRY'D:         model
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns))
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (hRuntime := hRuntime)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hheadCompile := hheadCompile fn hfn)
-- SORRY'D:         (hheadKernel := hheadKernel fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- SORRY'D: keeps the public dispatch theorem aligned with the roadmap's assign-first
-- SORRY'D: helper wiring: callers provide only the assign-side compile catalog plus the
-- SORRY'D: assign semantic kernel for each dispatched function, and the proof now lands
-- SORRY'D: directly on the corresponding contract-level assign-first wrapper. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hRuntime :
-- SORRY'D:       SupportedRuntimeHelperTableInterface
-- SORRY'D:         model
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns))
-- SORRY'D:     (hheadAssignCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeAssignCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   have hsurfaceFunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunctionWithInternals
-- SORRY'D:             (runtimeContractOfFunctions model.name irFns) 0
-- SORRY'D:             irFn tx.args
-- SORRY'D:             (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact
-- SORRY'D:       Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:         (model := model)
-- SORRY'D:         (selectors := selectors)
-- SORRY'D:         (hSupported := hSupported)
-- SORRY'D:         (hHelperProofs := hHelperProofs)
-- SORRY'D:         (hvalidateInputs := hvalidateInputs)
-- SORRY'D:         (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:         (hRuntime := hRuntime)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         (sel := sel)
-- SORRY'D:         (irFn := irFn)
-- SORRY'D:         (tx := tx)
-- SORRY'D:         (initialWorld := initialWorld)
-- SORRY'D:         (htxNormalized := htxNormalized)
-- SORRY'D:         (bindings := bindings)
-- SORRY'D:         (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:         (hfn := hfn)
-- SORRY'D:         (hcompileFn := hcompileFn)
-- SORRY'D:         (hbind := hbind)
-- SORRY'D:         (hheadAssignCompile := hheadAssignCompile fn hfn)
-- SORRY'D:         (hheadAssignKernel := hheadAssignKernel fn hfn)
-- SORRY'D:         (hdisjoint := hdisjoint fn hfn)
-- SORRY'D:         (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hfunction := hsurfaceFunction)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Dispatch-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- SORRY'D: lets callers provide void-call and return-binding helper kernels separately for
-- SORRY'D: each dispatched function while the existing combined semantic-kernel theorem is
-- SORRY'D: reassembled mechanically here. -/
-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hRuntime :
-- SORRY'D:       SupportedRuntimeHelperTableInterface
-- SORRY'D:         model
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns))
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadCallKernel := by
-- SORRY'D:         intro fn hfn
-- SORRY'D:         exact
-- SORRY'D:           directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
-- SORRY'D:             (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
-- SORRY'D:       (hheadAssignKernel := hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: theorem
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (irFns : List IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         irFns)
-- SORRY'D:     (hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
-- SORRY'D:     (hRuntime :
-- SORRY'D:       SupportedRuntimeHelperTableInterface
-- SORRY'D:         model
-- SORRY'D:         (runtimeContractOfFunctions model.name irFns))
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadCallKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeCallSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           model
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       ∀ fn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           (SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn.params.map (·.name))
-- SORRY'D:           fn.body)
-- SORRY'D:     (hbodyDisjoint :
-- SORRY'D:       ∀ fn sel irFn,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable
-- SORRY'D:           (runtimeContractOfFunctions model.name irFns)
-- SORRY'D:           irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
-- SORRY'D:       (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (irFns := irFns)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:       (hcompiled := hcompiled)
-- SORRY'D:       (hparamsSupported := hparamsSupported)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadKernel := by
-- SORRY'D:         intro fn hfn
-- SORRY'D:         exact
-- SORRY'D:           directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
-- SORRY'D:             (runtimeContract := runtimeContractOfFunctions model.name irFns)
-- SORRY'D:             (spec := model)
-- SORRY'D:             (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:             (fn := fn)
-- SORRY'D:             (hheadCallKernel fn hfn)
-- SORRY'D:             (hheadAssignKernel fn hfn))
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hbodyDisjoint := hbodyDisjoint)

-- SORRY'D: /-- Direct helper-aware dispatch theorem on the current legacy-compatible
-- SORRY'D: runtime-contract boundary. The compiled-side conservative-extension theorem is
-- SORRY'D: now closed in `IRInterpreter.lean`, so callers no longer need to supply it as
-- SORRY'D: an extra premise. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_closed
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies :
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hlegacyBodies := hlegacyBodies)
    (hhelperIRGoal :=
      interpretIRWithInternalsZeroConservativeExtensionGoal_closed
        (runtimeContractOfFunctions model.name irFns))

end Dispatch

end Compiler.Proofs.IRGeneration
