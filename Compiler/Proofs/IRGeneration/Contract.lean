import Compiler.Proofs.IRGeneration.Dispatch

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

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
      rcases hstep : compileInternalFunction fields events errors entry with _ | internalDef
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail :
          List.mapM (compileInternalFunction fields events errors) entries with _ | internalDefsTail
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
  | nil =>
      cases hmem
  | @cons headX headY tailX tailY hhead htail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact ⟨headY, by simp, hhead⟩
      · rcases ih hmemTail with ⟨y, hy, hRy⟩
        exact ⟨y, by simp [hy], hRy⟩

private theorem legacyCompatibleExternalStmtList_append
    (before : List YulStmt)
    (after : List YulStmt)
    (hbefore : LegacyCompatibleExternalStmtList before)
    (hafter : LegacyCompatibleExternalStmtList after) :
    LegacyCompatibleExternalStmtList (before ++ after) := by
  revert after hafter
  induction hbefore with
  | nil => intro after hafter; simpa using hafter
  | comment msg rest hrest ih =>
      intro after hafter; simpa using LegacyCompatibleExternalStmtList.comment msg (rest ++ after) (ih after hafter)
  | let_ name value rest hrest ih =>
      intro after hafter; simpa using LegacyCompatibleExternalStmtList.let_ name value (rest ++ after) (ih after hafter)
  | assign name value rest hrest ih =>
      intro after hafter; simpa using LegacyCompatibleExternalStmtList.assign name value (rest ++ after) (ih after hafter)
  | expr value rest hrest ih =>
      intro after hafter; simpa using LegacyCompatibleExternalStmtList.expr value (rest ++ after) (ih after hafter)
  | if_ cond body rest hbody hrest ihBody ihRest =>
      intro after hafter
      simpa using LegacyCompatibleExternalStmtList.if_ cond body (rest ++ after) hbody (ihRest after hafter)
  | block body rest hbody hrest ihBody ihRest =>
      intro after hafter
      simpa using LegacyCompatibleExternalStmtList.block body (rest ++ after) hbody (ihRest after hafter)
  | funcDef name params rets body rest hbody hrest ihBody ihRest =>
      intro after hafter
      simpa using LegacyCompatibleExternalStmtList.funcDef name params rets body (rest ++ after) hbody (ihRest after hafter)

private theorem legacyCompatibleExternalStmtList_of_exprStmtExprs
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact LegacyCompatibleExternalStmtList.nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

private theorem legacyCompatibleExternalStmtList_revertWithMessage
    (message : String) :
    LegacyCompatibleExternalStmtList (CompilationModel.revertWithMessage message) := by
  unfold CompilationModel.revertWithMessage
  let headerExprs :=
    [ YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]
    , YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]
    , YulExpr.call "mstore"
        [YulExpr.lit 36, YulExpr.lit (CompilationModel.bytesFromString message).length]
    ]
  let dataExprs :=
    (((CompilationModel.chunkBytes32 (CompilationModel.bytesFromString message)).zipIdx).map
      (fun (chunk, idx) =>
        let offset := 68 + idx * 32
        let word := CompilationModel.wordFromBytes chunk
        YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word]))
  let revertStmt :=
    YulStmt.expr
      (YulExpr.call "revert"
        [ YulExpr.lit 0
        , YulExpr.lit
            (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
        ])
  simpa [headerExprs, dataExprs, revertStmt, List.append_assoc] using
    legacyCompatibleExternalStmtList_append
      (before := headerExprs.map YulStmt.expr)
      (after := dataExprs.map YulStmt.expr ++ [revertStmt])
      (legacyCompatibleExternalStmtList_of_exprStmtExprs headerExprs)
      (legacyCompatibleExternalStmtList_append
        (before := dataExprs.map YulStmt.expr)
        (after := [revertStmt])
        (legacyCompatibleExternalStmtList_of_exprStmtExprs dataExprs)
        (LegacyCompatibleExternalStmtList.expr
          (YulExpr.call "revert"
            [ YulExpr.lit 0
            , YulExpr.lit
                (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
            ])
          []
          LegacyCompatibleExternalStmtList.nil))

-- NOTE: The following TYPESIG_SORRY theorems were dead code duplicates of proven versions in
-- GenericInduction.lean (legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields,
-- _of_compileStmt_ok_letVar, _assignVar, _require, _return, _stop,
-- _of_compileStmt_ok_on_supportedContractSurface, _of_compileStmtList_ok_on_supportedContractSurface)
-- and of proven local versions (_genParamLoadBodyFrom_cons_scalar, _genParamLoadBodyFrom_of_supported).
-- Removed in cleanup commit.

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_uint256
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
    (headSize baseOffset : Nat)
    (name : String)
    (rest : List Param)
    (headOffset : Nat)
    (hrest :
      LegacyCompatibleExternalStmtList
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest
            (headOffset + paramHeadSize ParamType.uint256))) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset ({ name := name, ty := ParamType.uint256 } :: rest) headOffset) := by
  simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
    LegacyCompatibleExternalStmtList.let_
      name
      (loadWord (YulExpr.lit headOffset))
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.uint256))
      hrest

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_uint8
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
    (headSize baseOffset : Nat)
    (name : String)
    (rest : List Param)
    (headOffset : Nat)
    (hrest :
      LegacyCompatibleExternalStmtList
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest
            (headOffset + paramHeadSize ParamType.uint8))) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset ({ name := name, ty := ParamType.uint8 } :: rest) headOffset) := by
  simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
    LegacyCompatibleExternalStmtList.let_
      name
      (YulExpr.call "and" [loadWord (YulExpr.lit headOffset), YulExpr.lit 255])
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.uint8))
      hrest

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_address
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
    (headSize baseOffset : Nat)
    (name : String)
    (rest : List Param)
    (headOffset : Nat)
    (hrest :
      LegacyCompatibleExternalStmtList
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest
            (headOffset + paramHeadSize ParamType.address))) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset ({ name := name, ty := ParamType.address } :: rest) headOffset) := by
  simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
    LegacyCompatibleExternalStmtList.let_
      name
      (YulExpr.call "and" [loadWord (YulExpr.lit headOffset), YulExpr.hex addressMask])
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.address))
      hrest

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_bytes32
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
    (headSize baseOffset : Nat)
    (name : String)
    (rest : List Param)
    (headOffset : Nat)
    (hrest :
      LegacyCompatibleExternalStmtList
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest
            (headOffset + paramHeadSize ParamType.bytes32))) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset ({ name := name, ty := ParamType.bytes32 } :: rest) headOffset) := by
  simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
    LegacyCompatibleExternalStmtList.let_
      name
      (loadWord (YulExpr.lit headOffset))
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.bytes32))
      hrest

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_scalar
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
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
  cases param with
  | mk name ty =>
      cases ty <;> simp [SupportedExternalParamType] at hparam
      case uint256 =>
        exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_uint256
          loadWord sizeExpr headSize baseOffset name rest headOffset hrest
      case int256 =>
        simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
          LegacyCompatibleExternalStmtList.let_
            name
            (loadWord (YulExpr.lit headOffset))
            (CompilationModel.genParamLoadBodyFrom
              loadWord sizeExpr headSize baseOffset rest
                (headOffset + paramHeadSize ParamType.int256))
            hrest
      case uint8 =>
        exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_uint8
          loadWord sizeExpr headSize baseOffset name rest headOffset hrest
      case address =>
        exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_address
          loadWord sizeExpr headSize baseOffset name rest headOffset hrest
      case bytes32 =>
        exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_bytes32
          loadWord sizeExpr headSize baseOffset name rest headOffset hrest
      case bool =>
        simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
          LegacyCompatibleExternalStmtList.let_
            name
            (YulExpr.call "iszero" [YulExpr.call "iszero" [loadWord (YulExpr.lit headOffset)]])
            (CompilationModel.genParamLoadBodyFrom
              loadWord sizeExpr headSize baseOffset rest
                (headOffset + paramHeadSize ParamType.bool))
            hrest

private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_of_supported
    (loadWord : YulExpr → YulExpr)
    (sizeExpr : YulExpr)
    (headSize baseOffset : Nat)
    (params : List Param)
    (headOffset : Nat)
    (hparams : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    LegacyCompatibleExternalStmtList
      (CompilationModel.genParamLoadBodyFrom
        loadWord sizeExpr headSize baseOffset params headOffset) := by
  induction params generalizing headOffset with
  | nil =>
      exact LegacyCompatibleExternalStmtList.nil
  | cons param rest ih =>
      have hparam : SupportedExternalParamType param.ty := hparams param (by simp)
      have hrest : ∀ other ∈ rest, SupportedExternalParamType other.ty := by
        intro other hmem
        exact hparams other (by simp [hmem])
      exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_scalar
        loadWord sizeExpr headSize baseOffset param rest headOffset hparam (ih _ hrest)

private theorem legacyCompatibleExternalStmtList_genParamLoads_of_supported
    (params : List Param)
    (hparams : ∀ param ∈ params, SupportedExternalParamType param.ty) :
    LegacyCompatibleExternalStmtList (CompilationModel.genParamLoads params) := by
  unfold CompilationModel.genParamLoads CompilationModel.genParamLoadsFrom
  apply LegacyCompatibleExternalStmtList.if_
  · exact LegacyCompatibleExternalStmtList.expr
      (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      []
      LegacyCompatibleExternalStmtList.nil
  · exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_of_supported
      (loadWord := fun pos => YulExpr.call "calldataload" [pos])
      (sizeExpr := YulExpr.call "calldatasize" [])
      (headSize := (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0)
      (baseOffset := 4)
      (params := params)
      (headOffset := 4)
      hparams

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

private theorem filterInternalFunctions_eq_nil_of_supported_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
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
  · simp [hmap, compileConstructor] at hcore
    injection hcore with hir
    cases hir
    rfl

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

theorem supported_params_of_supportedSpec_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
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
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_compiled_functions_except_mapping_writes
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

-- NOTE: compileValidatedCore_ok_yields_supportedRuntimeHelperTableInterface and
-- compile_ok_yields_supportedRuntimeHelperTableInterface are BLOCKED by missing
-- DirectInternalHelperPerCalleeCompileCatalog infrastructure in GenericInduction.lean.
-- They require the helper function interface witness machinery that is not yet implemented.

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
  rcases Function.compileFunctionSpec_ok_components
      model.fields model.events model.errors sel fn irFn hcompileFn with
    ⟨returns, bodyStmts, _hvalidate, _hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hparams :=
    legacyCompatibleExternalStmtList_genParamLoads_of_supported
      fn.params
      (hSupported.selectorFunctionParamsSupported hfn)
  have hbody :=
    legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
      (hnoPacked := hSupported.noPackedFields)
      (hsurface := by
        let hbody := (hSupported.supportedFunctionOfSelectorDispatched hfn).body
        exact stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
          hbody.core.surfaceClosed
          hbody.state.surfaceClosed
          (SupportedBodyCallInterface.surfaceClosed hbody)
          hbody.effects.surfaceClosed)
      (hcompile := by
        simpa [hSupported.noEvents, hSupported.noErrors] using hbodyCompile)
  exact legacyCompatibleExternalStmtList_append _ _ hparams hbody

private theorem compiled_functions_legacyCompatibleExternalBodies
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ {entries irFns},
      List.Forall₂
        (fun (entry : FunctionSpec × Nat) irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        entries
        irFns →
      (∀ entry ∈ entries, entry.1 ∈ selectorDispatchedFunctions model) →
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body
  | [], [], .nil, _ => by
      intro irFn hmem
      cases hmem
  | entry :: entries, irFn :: irFns, .cons hhead htail, hentries => by
      intro target hmem
      cases hmem with
      | head =>
          exact compileFunctionSpec_ok_yields_legacyCompatibleExternalStmtList
            (model := model)
            (selectors := selectors)
            (hSupported := hSupported)
            (fn := entry.1)
            (sel := entry.2)
            (irFn := irFn)
            (hfn := hentries entry (by simp))
            (hcompileFn := hhead)
      | tail _ hmemTail =>
          exact compiled_functions_legacyCompatibleExternalBodies
            (model := model)
            (selectors := selectors)
            (hSupported := hSupported)
            htail
            (fun other hmemEntry => hentries other (by simp [hmemEntry]))
            target
            hmemTail

theorem compile_ok_yields_legacyCompatibleExternalBodies
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    LegacyCompatibleExternalBodies ir := by
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
  intro irFn hmem
  exact compiled_functions_legacyCompatibleExternalBodies
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    hcompiled
    (by
      intro (entry : FunctionSpec × Nat) hentry
      simpa [SourceSemantics.selectorFunctionPairs] using
        (List.of_mem_zip hentry).1)
    irFn
    hmem

theorem compile_ok_yields_legacyCompatibleRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    LegacyCompatibleRuntimeContract ir := by
  exact ⟨
    compile_ok_yields_internalFunctions_nil
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile),
    compile_ok_yields_legacyCompatibleExternalBodies
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  ⟩

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
  have hcorrect :=
    Function.supported_function_correct_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (selector := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using hcorrect

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
  exact compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (hvalidateInputs := hvalidateInputs)
    (runtimeContract := runtimeContract)
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
    (hhelperIR :=
      execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
        runtimeContract
        irFn
        tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        hbodyDisjoint)

-- NOTE: ~1174 lines of SORRY'D dead code removed here.  They were 16 commented-out
-- helper-composition theorem sketches (escalating from DirectInternalHelper…Surface
-- through PerCallee…CompileCatalog, RuntimeWitnessCatalog, SemanticKernelCatalog)
-- plus an alternative proof body.  All were blocked by missing
-- DirectInternalHelperPerCalleeCompileCatalog infrastructure.  See git history for
-- the original sketches.
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
    simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
      (hSupported := hSupported) hfn tx initialWorld] using
      (compileFunctionSpec_correct_generic
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
        (hbind := hbind))
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
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec_except_mapping_writes model selectors hSupported
  have hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact compileFunctionSpec_correct_generic_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
  exact Dispatch.interpretContract_correct_of_compiled_functions_except_mapping_writes
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (irFns := ir.functions)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)

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
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
      (hSupported := hSupported) hfn tx initialWorld] using
      (compileFunctionSpec_correct_generic_with_helper_proofs
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
        (hbind := hbind))
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
    (hhelperIR :=
      interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed ir
        hdisjointIR
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
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed
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
    (hlegacyIR :=
      compile_ok_yields_legacyCompatibleRuntimeContract
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (ir := ir)
        (hcompile := hcompile))

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
