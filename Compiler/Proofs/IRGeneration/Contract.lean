import Compiler.Proofs.IRGeneration.Dispatch

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace Contract

private theorem pickUniqueFunctionByName_eq_ok_none_of_absent
    (name : String) (funcs : List FunctionSpec)
    (habsent : ∀ fn ∈ funcs, fn.name != name) :
    pickUniqueFunctionByName name funcs = Except.ok none := by
  induction funcs with
  | nil =>
      rfl
  | cons fn rest ih =>
      have hfn : (fn.name == name) = false := by
        by_cases heq : fn.name = name
        · have habs := habsent fn (by simp)
          simp [heq] at habs
        · simp [heq]
      have hrest : ∀ fn' ∈ rest, fn'.name != name := by
        intro fn' hmem
        exact habsent fn' (by simp [hmem])
      have ih' := ih hrest
      simpa [pickUniqueFunctionByName, hfn] using ih'

private theorem compiled_functions_forall₂_of_mapM_ok
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    ∀ (entries : List (FunctionSpec × Nat)) irFns,
      (entries.mapM fun (entry : FunctionSpec × Nat) =>
        compileFunctionSpec fields events errors entry.2 entry.1) = Except.ok irFns →
      List.Forall₂
        (fun (entry : FunctionSpec × Nat) irFn =>
          compileFunctionSpec fields events errors entry.2 entry.1 = Except.ok irFn)
        entries irFns := by
  intro entries
  induction entries with
  | nil =>
      intro irFns hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro irFns hmap
      rcases hstep : compileFunctionSpec fields events errors entry.2 entry.1 with _ | irFn
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail : List.mapM
            (fun (entry : FunctionSpec × Nat) =>
              compileFunctionSpec fields events errors entry.2 entry.1) entries with _ | irFnsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)

private theorem compileValidatedCore_ok_yields_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields, hSupported.noEvents, hSupported.noErrors,
    hSupported.noConstructor, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields [] [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    rcases hinternal :
        (model.functions.filter (·.isInternal)).mapM
          (compileInternalFunction model.fields [] []) with _ | internalFuncDefs
    · simp [hinternal] at hcore
    · simp [hinternal, compileConstructor] at hcore
      have hfunctions : ir.functions = irFns := by
        injection hcore with hir
        cases hir
        rfl
      have hcompiled :
          List.Forall₂
            (fun (entry : FunctionSpec × Nat) irFn =>
              compileFunctionSpec model.fields [] [] entry.2 entry.1 = Except.ok irFn)
            ((model.functions.filter
                (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors)
            irFns :=
        compiled_functions_forall₂_of_mapM_ok model.fields [] [] _ _ hmap
      simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
        hSupported.noEvents, hSupported.noErrors, hfunctions] using hcompiled

private theorem filterInternalFunctions_eq_nil_of_all_nonInternal :
    ∀ (fns : List FunctionSpec),
      (∀ fn ∈ fns, fn.isInternal = false) →
        fns.filter (·.isInternal) = []
  | [], _ => rfl
  | fn :: rest, hall => by
      have hfn : fn.isInternal = false := hall fn (by simp)
      have hrest : ∀ fn' ∈ rest, fn'.isInternal = false := by
        intro fn' hmem
        exact hall fn' (by simp [hmem])
      simp [hfn, filterInternalFunctions_eq_nil_of_all_nonInternal rest hrest]

private theorem filterInternalFunctions_eq_nil_of_supported
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    model.functions.filter (·.isInternal) = [] := by
  exact filterInternalFunctions_eq_nil_of_all_nonInternal model.functions
    (hSupported.noInternalFunctions)

private theorem compileValidatedCore_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported model selectors hSupported
  have harray : contractUsesArrayElement model = false :=
    hSupported.contractUsesArrayElement_eq_false
  have hstorageArray : contractUsesStorageArrayElement model = false :=
    hSupported.contractUsesStorageArrayElement_eq_false
  have hdynamicBytesEq : contractUsesDynamicBytesEq model = false :=
    hSupported.contractUsesDynamicBytesEq_eq_false
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields, hfallback, hreceive, harray, hstorageArray,
    hdynamicBytesEq, hnoInternalFns, hSupported.noConstructor] at hcore
  simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields model.events model.errors x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    injection hcore with _ _ _ _ _ _ _ hinternal
    exact hinternal

theorem supported_params_of_supportedSpec
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := by
    exact List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

theorem interpretIR_eq_runtimeContractOfFunctions
    (ir : IRContract)
    (runtimeName : String)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialState : IRState)
    (hfunctions : ir.functions = irFns) :
    interpretIR ir tx initialState =
      interpretIR (Dispatch.runtimeContractOfFunctions runtimeName irFns) tx initialState := by
  cases ir
  subst hfunctions
  simp [interpretIR, Dispatch.runtimeContractOfFunctions]

theorem interpretContract_correct_of_ir_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : ir.functions = irFns)
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
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretIR_eq_runtimeContractOfFunctions
    (ir := ir)
    (runtimeName := model.name)
    (irFns := irFns)
    (tx := tx)
    (initialState := FunctionBody.initialIRStateForTx model tx initialWorld)
    (hfunctions := hfunctions)]
  exact Dispatch.interpretContract_correct_of_compiled_functions
    (model := model) (selectors := selectors) (irFns := irFns)
    (tx := tx) (initialWorld := initialWorld)
    hcompiled hparamsSupported hfunction

theorem compile_preserves_semantics_of_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (_hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions)
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
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_ir_functions
    (model := model)
    (selectors := selectors)
    (ir := ir)
    (irFns := ir.functions)
    (tx := tx)
    (initialWorld := initialWorld)
    (hfunctions := rfl)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)

/-- Derive the compiled runtime function table directly from
`CompilationModel.compile = Except.ok ir` and `SupportedSpec`, without any
intermediate `List.Forall₂` hypothesis supplied by callers. -/
theorem compile_ok_yields_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_internalFunctions_nil
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

/-- Generic function-level closure from `SupportedSpec` and successful
`compileFunctionSpec`, with no residual body-level premises such as `hsource`,
`hbodyExec`, or `hmatch`. -/
theorem compileFunctionSpec_correct_generic
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hfnModel : fn ∈ model.functions := List.mem_of_mem_filter hfn
  rcases Function.compileFunctionSpec_ok_components
      model.fields model.events model.errors sel fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hcorrect :=
    Function.supported_function_correct
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hvalidateInputs := hvalidateInputs)
    (fn := fn)
    (selector := sel)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (bindings := bindings)
    (hfn := hfn)
    (hvalidate := hvalidate)
    (hreturns := hreturns)
    (hbodyCompile := hbodyCompile)
    (hcompile := by simpa using hcompileFn)
    (hbind := hbind)
    (hcalldataSizeFits := hcalldataSizeFits)
  simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using hcorrect

/-- Helper-proof-carrying function-level generic theorem.
This is the proof-ready theorem surface for the next helper-composition step.
Today the additional helper-proof argument is compatibility-redundant because
the body proof still closes helpers through `calls.helperCompatibility`. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases Function.compileFunctionSpec_ok_components
      model.fields model.events model.errors sel fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  exact Function.supported_function_correct_with_helper_proofs
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (hvalidateInputs := hvalidateInputs)
    (fn := fn)
    (selector := sel)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
    (tx := tx)
    (initialWorld := initialWorld)
    (bindings := bindings)
    (hfn := hfn)
    (hvalidate := hvalidate)
    (hreturns := hreturns)
    (hbodyCompile := hbodyCompile)
    (hcompile := by simpa using hcompileFn)
    (hbind := hbind)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)

/-- Helper-aware compiled-side wrapper for the generic function theorem.
This does not strengthen the current proof boundary by itself: it factors the
eventual retarget from `execIRFunction` to `execIRFunctionWithInternals` behind
the exact conservative-extension equality that still remains to be proved on the
compiled side. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hhelperIR :
      execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    compileFunctionSpec_correct_generic_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (hvalidateInputs := hvalidateInputs)
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
  simpa [hhelperIR] using hlegacy

/-- Primary whole-contract Layer 2 theorem: compilation preserves semantics
for any supported `CompilationModel`. No contract-specific bridge premise.
Layer 2 itself is axiom-free; the remaining documented project axiom is the
selector-level `keccak256_first_4_bytes` assumption tracked in `AXIOMS.md`. -/
theorem compile_preserves_semantics
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
    unfold CompilationModel.compile at hcompile
    simp only [bind, Except.bind] at hcompile
    rcases hvalidate : validateCompileInputs model selectors with _ | validated
    · simp [hvalidate] at hcompile
    · simpa using hvalidate
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec model selectors hSupported
  have hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact compileFunctionSpec_correct_generic
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hvalidateInputs := hvalidateInputs)
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
  have hcontract :=
    compile_preserves_semantics_of_compiled_functions
    (model := model)
    (selectors := selectors)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (_hcompile := hcompile)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hcontract

/-- Helper-proof-carrying whole-contract Layer 2 theorem.
This theorem family is the intended stable public interface for the helper
composition step tracked by `#1630`: callers can already pass explicit
summary-soundness evidence today, and once the body proof consumes it this
theorem can strengthen without another theorem-shape rewrite. The current proof
still reduces through the legacy helper-closed path, so the trusted boundary is
unchanged. -/
theorem compile_preserves_semantics_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
    unfold CompilationModel.compile at hcompile
    simp only [bind, Except.bind] at hcompile
    rcases hvalidate : validateCompileInputs model selectors with _ | validated
    · simp [hvalidate] at hcompile
    · simpa using hvalidate
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec model selectors hSupported
  have hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact compileFunctionSpec_correct_generic_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (hvalidateInputs := hvalidateInputs)
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
  exact compile_preserves_semantics_of_compiled_functions
    (model := model)
    (selectors := selectors)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (_hcompile := hcompile)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := by
      intro fn sel irFn bindings hfn hcompileFn hbind
      simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
        (hSupported := hSupported) hfn tx initialWorld] using
        hfunction fn sel irFn bindings hfn hcompileFn hbind)

/-- Helper-aware compiled-side wrapper for the whole-contract theorem.
The remaining compiled-side blocker is exactly the conservative-extension proof
that supplies `hhelperIR`; once that theorem is available, the public Layer 2
contract theorem can retarget to `interpretIRWithInternals` without another
interface change in `Contract.lean`. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hhelperIR :
      interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    compile_preserves_semantics_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (ir := ir)
      (tx := tx)
      (initialWorld := initialWorld)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompile := hcompile)
  simpa [hhelperIR] using hlegacy

/-- Structured helper-aware whole-contract wrapper.
This consumes the named compiled-side conservative-extension target together
with its explicit runtime-contract compatibility witness, instead of requiring
callers to restate the resulting equality manually. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hlegacyIR : LegacyCompatibleRuntimeContract ir)
    (hhelperIRGoal :
      InterpretIRWithInternalsZeroConservativeExtensionGoal ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hhelperIR := hhelperIRGoal
      hlegacyIR
      tx
      (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Direct helper-aware whole-contract theorem on the current legacy-compatible
runtime-contract boundary. The helper-aware compiled-side conservative-extension
goal is now closed in `IRInterpreter.lean`, so theorem users no longer need to
thread it as an extra hypothesis. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hlegacyIR : LegacyCompatibleRuntimeContract ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hlegacyIR := hlegacyIR)
    (hhelperIRGoal := interpretIRWithInternalsZeroConservativeExtensionGoal_closed ir)

/-- First direct consumer of the generic Layer 2 theorem surface: the existing
supported single-function demo model can now obtain whole-contract correctness
by instantiating `compile_preserves_semantics`, with no contract-specific body
bridge premise. -/
theorem counter_supported_spec_compile_preserves_semantics
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile :
      CompilationModel.compile counterSupportedSpecModel [0xa87d942c] = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics
        counterSupportedSpecModel [0xa87d942c] counter_supported_spec tx initialWorld)
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx counterSupportedSpecModel tx initialWorld)) := by
  exact compile_preserves_semantics
    (model := counterSupportedSpecModel)
    (selectors := [0xa87d942c])
    (hSupported := counter_supported_spec)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)

end Contract

end Compiler.Proofs.IRGeneration
