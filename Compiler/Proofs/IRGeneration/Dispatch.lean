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
helper-free semantics via `calls.helperCompatibility`, so the additional helper
proof slot is present to stabilize the theorem boundary rather than to widen the
proved fragment today. -/
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

end Dispatch

end Compiler.Proofs.IRGeneration
