import Compiler.Proofs.IRGeneration.SourceSemantics

set_option linter.unnecessarySimpa false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace ContractShape

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
        compileFunctionSpec fields events errors [] entry.2 entry.1) = Except.ok irFns →
      List.Forall₂
        (fun (entry : FunctionSpec × Nat) irFn =>
          compileFunctionSpec fields events errors [] entry.2 entry.1 = Except.ok irFn)
        entries irFns := by
  intro entries
  induction entries with
  | nil =>
      intro irFns hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro irFns hmap
      rcases hstep : compileFunctionSpec fields events errors [] entry.2 entry.1 with _ | irFn
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail : List.mapM
            (fun (entry : FunctionSpec × Nat) =>
              compileFunctionSpec fields events errors [] entry.2 entry.1) entries with _ | irFnsTail
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
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
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
  rw [hSupported.normalizedFields,
    hSupported.noAdtTypes, hSupported.noEvents, hSupported.noErrors,
    hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields [] [] [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    rcases hinternal :
        (model.functions.filter (·.isInternal)).mapM
          (compileInternalFunction model.fields [] [] []) with _ | internalFuncDefs
    · simp [hinternal] at hcore
    · rcases hctor :
          compileConstructor model.fields [] [] [] model.constructor with _ | deployStmts
      · simp [hinternal, hctor] at hcore
        cases hcore
      · simp [hinternal, hctor] at hcore
        have hfunctions : ir.functions = irFns := by
          injection hcore with hir
          cases hir
          rfl
        have hcompiled :
            List.Forall₂
              (fun (entry : FunctionSpec × Nat) irFn =>
                compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
              ((model.functions.filter
                  (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors)
              irFns :=
          by
            simpa [hSupported.noEvents, hSupported.noErrors] using
              (compiled_functions_forall₂_of_mapM_ok model.fields [] [] _ _ hmap)
        simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
          hfunctions] using hcompiled

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
  rw [hSupported.normalizedFields, hfallback, hreceive,
    contractUsesPlainArrayElement, contractUsesArrayElementWord, harray,
    hstorageArray, hdynamicBytesEq, hnoInternalFns, hSupported.noAdtTypes] at hcore
  simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
    · simp [hmap, hctor] at hcore
      cases hcore
    · simp [hmap, hctor] at hcore
      cases hcore
      rfl

private theorem compileValidatedCore_ok_yields_deploy_compileConstructor
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    compileConstructor model.fields model.events model.errors [] model.constructor =
      Except.ok ir.deploy := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields,
    hSupported.noAdtTypes, hSupported.noEvents, hSupported.noErrors,
    hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields [] [] [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    rcases hinternal :
        (model.functions.filter (·.isInternal)).mapM
          (compileInternalFunction model.fields [] [] []) with _ | internalFuncDefs
    · simp [hinternal] at hcore
    · rcases hctor :
          compileConstructor model.fields [] [] [] model.constructor with _ | deployStmts
      · simp [hinternal, hctor] at hcore
        cases hcore
      · simp [hinternal, hctor] at hcore
        cases hcore
        simpa [hSupported.noEvents, hSupported.noErrors] using hctor

private theorem compileValidatedCore_ok_yields_noFallbackEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  unfold compileValidatedCore at hcore
  rw [hfallback, hreceive] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hinternal :
        (model.functions.filter (·.isInternal)).mapM
          (compileInternalFunction (applySlotAliasRanges model.fields model.slotAliasRanges)
            model.events model.errors model.adtTypes) with _ | internalFuncDefs
    · simp [hmap, hinternal] at hcore
    · rcases hctor :
          compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
            model.events model.errors model.adtTypes model.constructor with _ | deployStmts
      · simp [hmap, hinternal, hctor] at hcore
      · simp [hmap, hinternal, hctor] at hcore
        cases hcore
        rfl

private theorem compileValidatedCore_ok_yields_noReceiveEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  unfold compileValidatedCore at hcore
  rw [hfallback, hreceive] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hinternal :
        (model.functions.filter (·.isInternal)).mapM
          (compileInternalFunction (applySlotAliasRanges model.fields model.slotAliasRanges)
            model.events model.errors model.adtTypes) with _ | internalFuncDefs
    · simp [hmap, hinternal] at hcore
    · rcases hctor :
          compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
            model.events model.errors model.adtTypes model.constructor with _ | deployStmts
      · simp [hmap, hinternal, hctor] at hcore
      · simp [hmap, hinternal, hctor] at hcore
        cases hcore
        rfl

theorem compile_ok_yields_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
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

theorem compile_ok_yields_deploy_compileConstructor
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    compileConstructor model.fields model.events model.errors [] model.constructor =
      Except.ok ir.deploy := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_deploy_compileConstructor
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_noFallbackEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_noFallbackEntrypoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_noReceiveEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_noReceiveEntrypoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

end ContractShape

end Compiler.Proofs.IRGeneration
