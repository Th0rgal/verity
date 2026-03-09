import Compiler.Proofs.IRGeneration.Dispatch

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace Contract

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
  /- TODO(#1510): discharge this as a purely structural `Except`/`List.mapM`
  extraction lemma with no contract-specific assumptions. This is mechanical
  proof plumbing; the generic Layer 2 proof must not depend on callers
  supplying a pre-built `List.Forall₂` witness. -/
  sorry

theorem supported_params_of_supportedSpec
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := by
    exact List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).params param hparam

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

/-- TODO(#1510): derive the compiled runtime function table directly from
`CompilationModel.compile = Except.ok ir` and `SupportedSpec`, without any
intermediate `List.Forall₂` hypothesis supplied by callers. This must remain
fully generic over supported contracts. -/
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
  sorry

/-- TODO(#1510): close the function layer generically from `SupportedSpec`
and successful `compileFunctionSpec`, with no residual body-level premises
such as `hsource`, `hbodyExec`, or `hmatch`. This theorem must be reusable for
arbitrary supported contracts, not for one pre-aligned compiled function list. -/
theorem compileFunctionSpec_correct_generic
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (bindings : List (String × Nat))
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretFunction model fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  sorry

/-- Primary whole-contract Layer 2 theorem shape for the supported generic
fragment. The remaining proof obligations are isolated in the two TODO lemmas
above and must be discharged generically, without reintroducing any
contract-specific bridge premise. -/
theorem compile_preserves_semantics
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
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
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
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
    (hfunction := hfunction)

end Contract

end Compiler.Proofs.IRGeneration
