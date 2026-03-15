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

private theorem compiled_internal_functions_forall₂_of_mapM_ok
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    ∀ (entries : List FunctionSpec) internalDefs,
      (entries.mapM (compileInternalFunction fields events errors)) =
        Except.ok internalDefs →
      List.Forall₂
        (fun fn internalDef =>
          compileInternalFunction fields events errors fn = Except.ok internalDef)
        entries internalDefs := by
  intro entries
  induction entries with
  | nil =>
      intro internalDefs hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro internalDefs hmap
      rcases hstep : compileInternalFunction fields events errors entry with _ | def_
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail : List.mapM
            (compileInternalFunction fields events errors) entries with _ | defsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)
private theorem exists_right_of_forall₂_mem_left
    {α β : Type}
    {R : α → β → Prop}
    {xs : List α}
    {ys : List β}
    (hrel : List.Forall₂ R xs ys)
    {x : α}
    (hmem : x ∈ xs) :
    ∃ y, y ∈ ys ∧ R x y := by
  induction hrel with
  | nil => cases hmem
  | cons hhead _ ih =>
      cases hmem with
      | head => exact ⟨_, .head _, hhead⟩
      | tail _ hmem' =>
          rcases ih hmem' with ⟨y, hy, hr⟩
          exact ⟨y, .tail _ hy, hr⟩
private theorem field_mem_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    f ∈ fields := by
      sorry
-- private theorem legacyCompatibleExternalStmtList_append
--     (pfx suffix : List Yul.YulStmt)
--     (hprefix : LegacyCompatibleExternalStmtList pfx)
--     (hsuffix : LegacyCompatibleExternalStmtList suffix) :
--     LegacyCompatibleExternalStmtList (pfx ++ suffix) := by
--       sorry
-- private theorem legacyCompatibleExternalStmtList_of_exprStmtExprs
--     (exprs : List Yul.YulExpr) :
--     LegacyCompatibleExternalStmtList (exprs.map Yul.YulStmt.expr) := by
--       sorry
private theorem legacyCompatibleExternalStmtList_revertWithMessage
    (message : String) :
    LegacyCompatibleExternalStmtList (CompilationModel.revertWithMessage message) := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List Yul.YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List Yul.YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.letVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List Yul.YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.assignVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_require
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {message : String}
    {bodyIR : List Yul.YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.require cond message) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_return
    {fields : List Field}
    {inScopeNames : List String}
    {value : Expr}
    {bodyIR : List Yul.YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.«return» value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
    {fields : List Field}
    {inScopeNames : List String}
    {bodyIR : List Yul.YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames .stop =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List Yul.YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_scalar
    (loadWord : Yul.YulExpr → Yul.YulExpr)
    (sizeExpr : Yul.YulExpr)
    (headSize baseOffset : Nat)
    (param : Param)
    (rest : List Param)
    (headOffset : Nat)
    (hparam : SupportedExternalParamType param.ty)
    (hrest :
      LegacyCompatibleExternalStmtList
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest
            (headOffset + paramHeadSize param.ty))) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset (param :: rest) headOffset) := by
          sorry
private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_of_supported
    (loadWord : Yul.YulExpr → Yul.YulExpr)
    (sizeExpr : Yul.YulExpr)
    (headSize baseOffset : Nat)
    (params : List Param)
    (headOffset : Nat)
    (hparams : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset params headOffset) := by
          sorry
private theorem legacyCompatibleExternalStmtList_genParamLoads_of_supported
    (params : List Param)
    (hparams : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    LegacyCompatibleExternalStmtList (CompilationModel.genParamLoads params) := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List Yul.YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
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
        sorry
private theorem compileValidatedCore_ok_yields_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
        sorry
private theorem filterInternalFunctions_eq_nil_of_all_nonInternal :
    ∀ (fns : List FunctionSpec),
      (∀ fn ∈ fns, fn.isInternal = false) →
        fns.filter (·.isInternal) = []
  | [], _ => rfl
  | fn :: rest, h => by
      simp only [List.filter_cons]
      have hfn := h fn (.head _)
      simp [hfn, filterInternalFunctions_eq_nil_of_all_nonInternal rest
        (fun f hf => h f (.tail _ hf))]
private theorem filterInternalFunctions_eq_nil_of_supported
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    model.functions.filter (·.isInternal) = [] := by
      sorry
private theorem filterInternalFunctions_eq_nil_of_supported_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
    model.functions.filter (·.isInternal) = [] := by
      sorry
private theorem compileValidatedCore_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
      sorry
theorem supported_params_of_supportedSpec
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
        sorry
theorem supported_params_of_supportedSpec_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
        sorry
theorem interpretIR_eq_runtimeContractOfFunctions
    (ir : IRContract)
    (runtimeName : String)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialState : IRState)
    (hfunctions : ir.functions = irFns) :
    interpretIR ir tx initialState =
      interpretIR (Dispatch.runtimeContractOfFunctions runtimeName irFns) tx initialState := by
        sorry
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
        sorry
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
        sorry
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
        sorry
theorem compile_ok_yields_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
        sorry
theorem compile_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
      sorry
private def compileValidatedCore_ok_yields_supportedRuntimeHelperTableInterface
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    SupportedRuntimeHelperTableInterface model ir := by
      sorry
def compile_ok_yields_supportedRuntimeHelperTableInterface
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    SupportedRuntimeHelperTableInterface model ir := by
      sorry
/-- On the current `SupportedSpec` fragment, successful external-function
compilation already yields legacy-compatible helper-free IR bodies. -/
theorem compileFunctionSpec_ok_yields_legacyCompatibleExternalStmtList
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn) :
    LegacyCompatibleExternalStmtList irFn.body := by
      sorry
-- private theorem compiled_functions_legacyCompatibleExternalBodies
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors) :
--     ∀ {entries irFns},
--       List.Forall₂
--         (fun entry irFn =>
--           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
--         entries
--         irFns →
--       (∀ entry ∈ entries, entry.1 ∈ selectorDispatchedFunctions model) →
--       ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body
--   | [], [], .nil, _ => by
--       intro irFn hmem
--       cases hmem
--   | entry :: entries, irFn :: irFns, .cons hhead htail, hentries => by
--       intro target hmem
--       cases hmem with
--       | head =>
--           exact compileFunctionSpec_ok_yields_legacyCompatibleExternalStmtList
--             (model := model)
--             (selectors := selectors)
--             (hSupported := hSupported)
--             (fn := entry.1)
--             (sel := entry.2)
--             (irFn := irFn)
--             (hfn := hentries entry (by simp))
--             (hcompileFn := hhead)
--       | tail hmem =>
--           exact compiled_functions_legacyCompatibleExternalBodies
--             (model := model)
--             (selectors := selectors)
--             (hSupported := hSupported)
--             htail
--             (fun other hmemEntry => hentries other (by simp [hmemEntry]))
--             target
--             hmem

theorem compile_ok_yields_legacyCompatibleExternalBodies
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    LegacyCompatibleExternalBodies ir := by
      sorry
theorem compile_ok_yields_legacyCompatibleRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    LegacyCompatibleRuntimeContract ir := by
      sorry
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
        sorry
/-- Tier 2 generic function-level closure from
`SupportedSpecExceptMappingWrites` and successful `compileFunctionSpec`. This
exposes the widened singleton storage-write fragment on the same public theorem
surface as the ordinary supported-function wrapper. -/
theorem compileFunctionSpec_correct_generic_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
        sorry
/-- Helper-proof-carrying function-level generic theorem.
This is the proof-ready theorem surface for the next helper-composition step.
Today the additional helper-proof argument is compatibility-redundant because
the body proof still closes helpers through the helper-excluding
`SupportedStmtList` fragment. -/
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
        sorry
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
          sorry
/-- Structured helper-aware compiled-side wrapper for the generic function
theorem. This replaces the raw function-level conservative-extension equality
premise by the compiled-body disjointness witness that proves it. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_bodyCallsDisjoint
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
    (hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
-- /-- Narrow helper-aware compileFunctionSpec wrapper aligned with the current
-- Tier 4 direct-helper seam. This keeps the public compile theorem on the exact
-- helper-aware IR boundary while requiring callers to discharge only the direct
-- statement-position helper call / helper-assign interfaces plus the two compiled
-- disjointness obligations. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hcall :
--       StmtListDirectInternalHelperCallStepInterface
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hassign :
--       StmtListDirectInternalHelperAssignStepInterface
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing helper-aware wrapper stated over reusable single-head direct
-- helper builders instead of preassembled list interfaces. This is the exact
-- Tier 4 public seam that future rank induction should target at function
-- compilation boundaries. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hcallStep :
--       ∀ {scope : List String} {calleeName : String} {args : List Expr},
--         ∃ compiledIR,
--           CompiledStmtStepWithHelpersAndHelperIR
--             runtimeContract
--             model
--             (SourceSemantics.effectiveFields model)
--             scope
--             (Stmt.internalCall calleeName args)
--             compiledIR)
--     (hassignStep :
--       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
--         ∃ compiledIR,
--           CompiledStmtStepWithHelpersAndHelperIR
--             runtimeContract
--             model
--             (SourceSemantics.effectiveFields model)
--             scope
--             (Stmt.internalCallAssign names calleeName args)
--             compiledIR)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper whose direct-helper head-step assumptions are
-- indexed only by helper callees that actually occur in the current function
-- body. This matches the body-local helper-rank inventory. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hcallStep :
--       ∀ {scope : List String} {calleeName : String} {args : List Expr},
--         calleeName ∈ helperCallNames fn →
--         ∃ compiledIR,
--           CompiledStmtStepWithHelpersAndHelperIR
--             runtimeContract
--             model
--             (SourceSemantics.effectiveFields model)
--             scope
--             (Stmt.internalCall calleeName args)
--             compiledIR)
--     (hassignStep :
--       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
--         calleeName ∈ helperCallNames fn →
--         ∃ compiledIR,
--           CompiledStmtStepWithHelpersAndHelperIR
--             runtimeContract
--             model
--             (SourceSemantics.effectiveFields model)
--             scope
--             (Stmt.internalCallAssign names calleeName args)
--             compiledIR)
--     (hdisjoint :
--       StmtListHelperFreeCompiledCallsDisjoint
--         runtimeContract
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hfnBodyDisjoint :
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper that consumes a single direct-helper head-step
-- catalog for the current function body. This is the contract-level target future
-- helper-rank induction should instantiate. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hcatalog :
--       DirectInternalHelperHeadStepCatalog
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper one seam earlier than
-- `...head_step_catalog...`: callers provide singleton direct-helper compilation
-- and bridge proofs for the current body, and the reusable head-step catalog is
-- assembled here. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hbridge :
--       DirectInternalHelperHeadStepBridgeCatalog
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper on the callee-local bridge boundary. This is
-- the contract-level seam that matches the helper-rank inventory directly:
-- callers provide one reusable bridge object per helper callee referenced by the
-- current body, and the body-level bridge catalog is assembled here. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hcallee :
--       DirectInternalHelperPerCalleeBridgeCatalog
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper on the assign-only callee-local bridge
-- boundary. Under the current fragment, the void-call helper bridge half is still
-- vacuous, so callers only need one reusable assign bridge per referenced helper
-- callee, and this wrapper now lands directly on the exact body-level
-- head-step catalog target instead of routing through the narrower function-level
-- assign-bridge theorem. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hheadAssignBridge :
--       DirectInternalHelperPerCalleeAssignBridgeCatalog
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper on the fully split callee-local boundary.
-- Callers can provide direct-helper head compilation and semantic bridge
-- catalogs separately; they are reassembled into the existing per-callee bridge
-- catalog at this boundary. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
--     (hheadCompile :
--       DirectInternalHelperPerCalleeCompileCatalog
--         model
--         (SourceSemantics.effectiveFields model)
--         fn)
--     (hheadSemantic :
--       DirectInternalHelperPerCalleeSemanticBridgeCatalog
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Compile-facing Tier 4 wrapper that separates runtime helper lookup from the
-- remaining semantic singleton-step work. This matches the contract-level split:
-- compiled runtimes can provide helper witnesses independently, while future rank
-- induction only needs to supply the semantic core catalog. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Contract-level Tier 4 wrapper on the smaller semantic-kernel seam. This
-- lets callers reuse the supported-function helper inventory already present at
-- the contract theorem boundary instead of packaging a full semantic core
-- catalog by hand. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Contract-level Tier 4 wrapper one seam earlier than the runtime-witness
-- catalog boundary. A compiled runtime helper table is enough to reconstruct the
-- per-callee runtime witnesses for `fn`, so the remaining explicit helper-side
-- obligations are just the compile catalog and semantic kernel. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- keeps the public function theorem aligned with the roadmap's assign-first
-- helper wiring while still reusing the existing combined semantic-kernel chain
-- internally. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- keeps the public function theorem aligned with the roadmap's assign-first
-- helper wiring while still reusing the existing combined semantic-kernel chain
-- internally. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
-- /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- keeps the public function theorem aligned with the roadmap's assign-first
-- helper wiring while still reusing the existing combined semantic-kernel chain
-- internally. -/
-- theorem
--     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
--     (model : CompilationModel)
--     (selectors : List Nat)
--     (hSupported : SupportedSpec model selectors)
--     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
--     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
--     (runtimeContract : IRContract)
--     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
--     (fn : FunctionSpec)
--     (sel : Nat)
--     (irFn : IRFunction)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (htxNormalized : Function.TxContextNormalized tx)
--     (bindings : List (String × Nat))
--     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
--     (hfn : fn ∈ selectorDispatchedFunctions model)
--     (hcompileFn :
--       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
--     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
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
--       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
--     FunctionBody.sourceResultMatchesIRResult
--       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
--       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
--         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
--           sorry
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
        sorry
/-- Whole-contract Tier 2 bridge for specs whose selector-dispatched bodies use
the alternate singleton-storage-write state interface. This keeps the contract
proof on the same generic dispatch skeleton while widening only the function
correctness theorem it instantiates. -/
theorem compile_preserves_semantics_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
        sorry
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
        sorry
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
          sorry
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
          sorry
/-- Disjointness-based helper-aware whole-contract wrapper.
This replaces the legacy-compatible runtime assumption with the weaker
`DisjointRuntimeContract` boundary that future helper-table compilation should
still satisfy even after `ir.internalFunctions` stops being empty. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
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
    (hdisjointIR : DisjointRuntimeContract ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
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
          sorry
/-- On the current `SupportedSpec` theorem domain, the helper-aware whole-contract
wrapper no longer needs callers to provide a manual legacy-compatibility witness:
successful `CompilationModel.compile` already yields the required runtime shape. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_supported
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
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
          sorry
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
          sorry
end Contract

end Compiler.Proofs.IRGeneration
