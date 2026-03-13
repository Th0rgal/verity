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
  cases ty with
  | uint256 =>
      exact ⟨SourceSemantics.wordNormalize word, by
        simp [SourceSemantics.decodeSupportedParamWord]⟩
  | uint8 =>
      exact ⟨SourceSemantics.wordNormalize word &&& (SourceSemantics.uint8Modulus - 1), by
        simp [SourceSemantics.decodeSupportedParamWord]⟩
  | address =>
      exact ⟨SourceSemantics.wordNormalize word &&& Compiler.Constants.addressMask, by
        simp [SourceSemantics.decodeSupportedParamWord]⟩
  | bool =>
      cases hsupported
  | bytes32 =>
      exact ⟨SourceSemantics.wordNormalize word, by
        simp [SourceSemantics.decodeSupportedParamWord]⟩
  | string =>
      cases hsupported
  | tuple _ =>
      cases hsupported
  | array _ =>
      cases hsupported
  | fixedArray _ _ =>
      cases hsupported
  | bytes =>
      cases hsupported

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
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [hhelperIR] using hlegacy

/-- Structured helper-aware dispatch wrapper.
This consumes the named compiled-side conservative-extension goal together with
the runtime-contract compatibility witness, instead of requiring callers to
restate the resulting equality manually. -/
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

/-- Narrow direct-helper-aware dispatch wrapper aligned with the current Tier 4
function theorem seam. Callers stay on `execIRFunctionWithInternals` for each
selected function, while the wrapper discharges the older dispatch theorem
through per-body disjointness instead of requiring a manual whole-contract
compiled-side equality premise. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
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
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    have hmatch :=
      hfunction fn sel irFn bindings hfn hcompileFn hbind
    have hfnBodyDisjoint :
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body :=
      hbodyDisjoint fn sel irFn hfn hcompileFn
    have hhelperEq :
        execIRFunctionWithInternals (runtimeContractOfFunctions model.name irFns) 0
          irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld) =
        execIRFunction irFn tx.args
          (FunctionBody.initialIRStateForTx model tx initialWorld) :=
      execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
        (runtimeContractOfFunctions model.name irFns)
        irFn
        tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        hfnBodyDisjoint
    simpa [hhelperEq] using hmatch
  have hdisjointIR :
      DisjointRuntimeContract (runtimeContractOfFunctions model.name irFns) := by
    intro irFn hmem
    rcases exists_left_of_forall₂_mem_right hcompiled hmem with ⟨entry, hmemEntry, hcompileFn⟩
    rcases entry with ⟨fn, sel⟩
    have hfn :
        fn ∈ selectorDispatchedFunctions model := by
      simpa [SourceSemantics.selectorFunctionPairs] using
        (List.mem_of_mem_zipLeft hmemEntry : fn ∈ selectorDispatchedFunctions model)
    exact hbodyDisjoint fn sel irFn hfn hcompileFn
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hlegacyFunction)
    (hdisjointIR := hdisjointIR)

/-- Dispatch-level Tier 4 wrapper stated over reusable single-head direct
helper step builders. This lets future rank-decreasing helper induction target
the public whole-contract theorem boundary directly, without first assembling
per-function list interfaces. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcallStep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            (runtimeContractOfFunctions model.name irFns)
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCall calleeName args)
            compiledIR)
    (hassignStep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            (runtimeContractOfFunctions model.name irFns)
            model
            (SourceSemantics.effectiveFields model)
            scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (hvalidateInputs := hvalidateInputs)
      (runtimeContract := runtimeContractOfFunctions model.name irFns)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (htxNormalized := htxNormalized)
      (bindings := bindings)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
      (hcallStep := hcallStep)
      (hassignStep := hassignStep)
      (hdisjoint := hdisjoint fn hfn)
      (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper whose direct-helper head-step assumptions are
indexed only by helper callees that actually occur in each function body. This
matches the `calleeRanksDecrease` inventory that future helper-rank induction
will consume. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcallStep :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        ∀ {scope : List String} {calleeName : String} {args : List Expr},
          calleeName ∈ helperCallNames fn →
          ∃ compiledIR,
            CompiledStmtStepWithHelpersAndHelperIR
              (runtimeContractOfFunctions model.name irFns)
              model
              (SourceSemantics.effectiveFields model)
              scope
              (Stmt.internalCall calleeName args)
              compiledIR)
    (hassignStep :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
          calleeName ∈ helperCallNames fn →
          ∃ compiledIR,
            CompiledStmtStepWithHelpersAndHelperIR
              (runtimeContractOfFunctions model.name irFns)
              model
              (SourceSemantics.effectiveFields model)
              scope
              (Stmt.internalCallAssign names calleeName args)
              compiledIR)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (hvalidateInputs := hvalidateInputs)
      (runtimeContract := runtimeContractOfFunctions model.name irFns)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (htxNormalized := htxNormalized)
      (bindings := bindings)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
      (hcallStep := hcallStep fn hfn)
      (hassignStep := hassignStep fn hfn)
      (hdisjoint := hdisjoint fn hfn)
      (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper that consumes one direct-helper head-step
catalog per selector-dispatched function. This is the whole-contract theorem
boundary future helper-rank induction should target. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcatalog :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperHeadStepCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hcatalog := hcatalog fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper one seam earlier than
`...head_step_catalog...`: callers provide a singleton direct-helper bridge
catalog per dispatched function, and the reusable head-step catalogs are
assembled here before dispatch-level reuse. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hbridge :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperHeadStepBridgeCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hvalidateInputs := hvalidateInputs)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hcatalog := by
        intro fn hfn
        exact
          directInternalHelperHeadStepCatalog_of_bridgeCatalog
            (runtimeContract := runtimeContractOfFunctions model.name irFns)
            (spec := model)
            (fields := SourceSemantics.effectiveFields model)
            (fn := fn)
            (hbridge fn hfn))
      (hdisjoint := hdisjoint)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the callee-local bridge boundary. This
matches `calleeRanksDecrease` directly: callers provide one reusable bridge
object per helper callee referenced by each dispatched body, and the body-level
bridge catalogs are assembled here mechanically before dispatch-level reuse. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hcallee :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeBridgeCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hcatalog :=
          directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
            (runtimeContract := runtimeContractOfFunctions model.name irFns)
            (spec := model)
            (fields := SourceSemantics.effectiveFields model)
            (fn := fn)
            (hcallee fn hfn))
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the assign-only callee-local bridge
boundary. Under the current fragment, each dispatched body only needs reusable
helper-return-binding bridges; the void-call half is still vacuous and is
reassembled mechanically here. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hheadAssignBridge :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeAssignBridgeCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadAssignBridge := hheadAssignBridge fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the fully split callee-local boundary.
Each dispatched body can now provide direct-helper head compilation and
semantic bridge catalogs independently, and dispatch-level reuse assembles the
existing per-callee bridge catalog mechanically. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadSemantic :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeSemanticBridgeCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadCompile := hheadCompile fn hfn)
        (hheadSemantic := hheadSemantic fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper that separates runtime helper lookup from the
remaining semantic singleton-step work. Each body can provide a runtime witness
catalog independently from its semantic core, and dispatch-level reuse
reassembles the existing bridge boundary mechanically. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hruntimeWitness :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeRuntimeWitnessCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          fn)
    (hheadSemantic :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeSemanticCoreCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadCompile := hheadCompile fn hfn)
        (hruntimeWitness := hruntimeWitness fn hfn)
        (hheadSemantic := hheadSemantic fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the smaller semantic-kernel seam. This
keeps the dispatch boundary aligned with the actual new proof work: compile
catalog, runtime helper witnesses, and the irreducible semantic kernel. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hruntimeWitness :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeRuntimeWitnessCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          fn)
    (hheadKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadCompile := hheadCompile fn hfn)
        (hruntimeWitness := hruntimeWitness fn hfn)
        (hheadKernel := hheadKernel fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper one seam earlier than the per-function
runtime-witness catalog boundary. A single runtime helper table for the
compiled contract is enough to derive each function's callee-local runtime
inventory, leaving only the compile catalogs and semantic kernels explicit. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hRuntime :
      SupportedRuntimeHelperTableInterface
        model
        (runtimeContractOfFunctions model.name irFns))
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (hRuntime := hRuntime)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadCompile := hheadCompile fn hfn)
        (hheadKernel := hheadKernel fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the split semantic-kernel boundary. This
keeps the public dispatch theorem aligned with the roadmap's assign-first
helper wiring: callers provide only the assign-side compile catalog plus the
assign semantic kernel for each dispatched function, and the proof now lands
directly on the corresponding contract-level assign-first wrapper. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hRuntime :
      SupportedRuntimeHelperTableInterface
        model
        (runtimeContractOfFunctions model.name irFns))
    (hheadAssignCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeAssignCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadAssignKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsurfaceFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals
            (runtimeContractOfFunctions model.name irFns) 0
            irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact
      Contract.compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (runtimeContract := runtimeContractOfFunctions model.name irFns)
        (hRuntime := hRuntime)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind)
        (hheadAssignCompile := hheadAssignCompile fn hfn)
        (hheadAssignKernel := hheadAssignKernel fn hfn)
        (hdisjoint := hdisjoint fn hfn)
        (hfnBodyDisjoint := hbodyDisjoint fn sel irFn hfn hcompileFn)
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hsurfaceFunction)
      (hbodyDisjoint := hbodyDisjoint)

/-- Dispatch-level Tier 4 wrapper on the split semantic-kernel boundary. This
lets callers provide void-call and return-binding helper kernels separately for
each dispatched function while the existing combined semantic-kernel theorem is
reassembled mechanically here. -/
theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hRuntime :
      SupportedRuntimeHelperTableInterface
        model
        (runtimeContractOfFunctions model.name irFns))
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadAssignKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hvalidateInputs := hvalidateInputs)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hRuntime := hRuntime)
      (hheadCompile := hheadCompile)
      (hheadCallKernel := by
        intro fn hfn
        exact
          directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
            (runtimeContract := runtimeContractOfFunctions model.name irFns)
            (spec := model)
            (fields := SourceSemantics.effectiveFields model)
            (fn := fn)
            (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
      (hheadAssignKernel := hheadAssignKernel)
      (hdisjoint := hdisjoint)
      (hbodyDisjoint := hbodyDisjoint)

theorem
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hRuntime :
      SupportedRuntimeHelperTableInterface
        model
        (runtimeContractOfFunctions model.name irFns))
    (hheadCompile :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCompileCatalog
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadCallKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeCallSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hheadAssignKernel :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
          (runtimeContractOfFunctions model.name irFns)
          model
          (SourceSemantics.effectiveFields model)
          fn)
    (hdisjoint :
      ∀ fn,
        fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint
          (runtimeContractOfFunctions model.name irFns)
          (SourceSemantics.effectiveFields model)
          (fn.params.map (·.name))
          fn.body)
    (hbodyDisjoint :
      ∀ fn sel irFn,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions model.name irFns)
          irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact
    interpretContract_correct_of_compiled_functions_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hvalidateInputs := hvalidateInputs)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hRuntime := hRuntime)
      (hheadCompile := hheadCompile)
      (hheadKernel := by
        intro fn hfn
        exact
          directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
            (runtimeContract := runtimeContractOfFunctions model.name irFns)
            (spec := model)
            (fields := SourceSemantics.effectiveFields model)
            (fn := fn)
            (hheadCallKernel fn hfn)
            (hheadAssignKernel fn hfn))
      (hdisjoint := hdisjoint)
      (hbodyDisjoint := hbodyDisjoint)

/-- Direct helper-aware dispatch theorem on the current legacy-compatible
runtime-contract boundary. The compiled-side conservative-extension theorem is
now closed in `IRInterpreter.lean`, so callers no longer need to supply it as
an extra premise. -/
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
