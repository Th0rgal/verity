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

private theorem field_mem_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    f ∈ fields := by
  induction fields with
  | nil =>
      simp [findFieldWithResolvedSlot] at hfind
  | cons field rest ih =>
      simp [findFieldWithResolvedSlot] at hfind ⊢
      by_cases hname : field.name == fieldName
      · injection hfind with hfield _
        subst hfield
        simp [hname]
      · simp [hname] at hfind
        exact Or.inr (ih hfind)

private theorem legacyCompatibleExternalStmtList_append
    (prefix suffix : List YulStmt)
    (hprefix : LegacyCompatibleExternalStmtList prefix)
    (hsuffix : LegacyCompatibleExternalStmtList suffix) :
    LegacyCompatibleExternalStmtList (prefix ++ suffix) := by
  induction hprefix generalizing suffix with
  | nil =>
      simpa using hsuffix
  | comment msg rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.comment msg (rest ++ suffix) (ih hsuffix)
  | let_ name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.let_ name value (rest ++ suffix) (ih hsuffix)
  | assign name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.assign name value (rest ++ suffix) (ih hsuffix)
  | expr value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr value (rest ++ suffix) (ih hsuffix)
  | if_ cond body rest hbody hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.if_ cond body (rest ++ suffix) hbody (ih hsuffix)
  | block body rest hbody hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.block body (rest ++ suffix) hbody (ih hsuffix)
  | funcDef name params rets body rest hbody hrest ih =>
      simpa using
        LegacyCompatibleExternalStmtList.funcDef name params rets body (rest ++ suffix) hbody (ih hsuffix)

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
  apply legacyCompatibleExternalStmtList_append
  · exact legacyCompatibleExternalStmtList_of_exprStmtExprs
      [ YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]
      , YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]
      , YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit (CompilationModel.bytesFromString message).length]
      ]
  · apply legacyCompatibleExternalStmtList_append
    · exact legacyCompatibleExternalStmtList_of_exprStmtExprs
        (((CompilationModel.chunkBytes32 (CompilationModel.bytesFromString message)).zipIdx).map
          (fun (chunk, idx) =>
            let offset := 68 + idx * 32
            let word := CompilationModel.wordFromBytes chunk
            YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word]))
    · exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "revert"
          [ YulExpr.lit 0
          , YulExpr.lit
              (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
          ])
        []
        LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStorage at hcompile
  by_cases hmapping : isMapping fields fieldName
  · simp [hmapping] at hcompile
  · simp [hmapping] at hcompile
    rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
    · simp [hfind] at hcompile
    · simp [hfind] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr
      · simp [hvalue] at hcompile
      · simp [hvalue] at hcompile
        have hunpacked : f.packedBits = none :=
          hnoPacked f (field_mem_of_findFieldWithResolvedSlot_some hfind)
        rw [hunpacked] at hcompile
        cases halias : f.aliasSlots with
        | nil =>
            simp [halias] at hcompile
            injection hcompile with hbody
            subst hbody
            exact LegacyCompatibleExternalStmtList.expr
              (YulExpr.call "sstore" [YulExpr.lit slot, valueExpr])
              []
              LegacyCompatibleExternalStmtList.nil
        | cons alias rest =>
            simp [halias] at hcompile
            injection hcompile with hbody
            subst hbody
            apply LegacyCompatibleExternalStmtList.block
            · apply LegacyCompatibleExternalStmtList.let_
              exact legacyCompatibleExternalStmtList_of_exprStmtExprs
                (((slot :: alias :: rest).map
                  (fun writeSlot =>
                    YulExpr.call "sstore"
                      [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))
            · exact LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.letVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    injection hcompile with hbody
    subst hbody
    exact LegacyCompatibleExternalStmtList.let_ name valueIR [] LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.assignVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    injection hcompile with hbody
    subst hbody
    exact LegacyCompatibleExternalStmtList.assign name valueIR [] LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_require
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {message : String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.require cond message) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hfail : CompilationModel.compileRequireFailCond fields .calldata cond with _ | failCond
  · simp [hfail] at hcompile
  · simp [hfail] at hcompile
    injection hcompile with hbody
    subst hbody
    exact LegacyCompatibleExternalStmtList.if_
      failCond
      (CompilationModel.revertWithMessage message)
      []
      (legacyCompatibleExternalStmtList_revertWithMessage message)
      LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_return
    {fields : List Field}
    {inScopeNames : List String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.return value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    injection hcompile with hbody
    subst hbody
    exact LegacyCompatibleExternalStmtList.expr
      (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])]
      (LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        []
        LegacyCompatibleExternalStmtList.nil)

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
    {fields : List Field}
    {inScopeNames : List String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames .stop =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  injection hcompile with hbody
  subst hbody
  exact LegacyCompatibleExternalStmtList.expr
    (YulExpr.call "stop" [])
    []
    LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt <;> simp [stmtTouchesUnsupportedContractSurface] at hsurface
  case letVar name value =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar hcompile
  case assignVar name value =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar hcompile
  case setStorage fieldName value =>
    unfold CompilationModel.compileStmt at hcompile
    exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields hnoPacked hcompile
  case require cond message =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_require hcompile
  case return value =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_return hcompile
  case stop =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_stop hcompile
  all_goals
    cases hsurface

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
  cases hty : param.ty <;> try cases hparam
  case uint256 =>
    simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
      LegacyCompatibleExternalStmtList.let_
        param.name
        (loadWord (YulExpr.lit headOffset))
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.uint256))
        hrest
  case uint8 =>
    simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
      LegacyCompatibleExternalStmtList.let_
        param.name
        (YulExpr.call "and" [loadWord (YulExpr.lit headOffset), YulExpr.lit 255])
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.uint8))
        hrest
  case address =>
    simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
      LegacyCompatibleExternalStmtList.let_
        param.name
        (YulExpr.call "and" [loadWord (YulExpr.lit headOffset), YulExpr.hex addressMask])
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.address))
        hrest
  case bytes32 =>
    simpa [CompilationModel.genParamLoadBodyFrom, CompilationModel.genScalarLoad] using
      LegacyCompatibleExternalStmtList.let_
        param.name
        (loadWord (YulExpr.lit headOffset))
        (CompilationModel.genParamLoadBodyFrom
          loadWord sizeExpr headSize baseOffset rest (headOffset + paramHeadSize ParamType.bytes32))
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
      simp [CompilationModel.genParamLoadBodyFrom]
  | cons param rest ih =>
      have hparam : SupportedExternalParamType param.ty := hparams param (by simp)
      have hrest :
          ∀ other ∈ rest, SupportedExternalParamType other.ty := by
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

private theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  induction stmts generalizing inScopeNames bodyIR with
  | nil =>
      simpa [CompilationModel.compileStmtList] using hcompile
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2
      rcases FunctionBody.compileStmtList_cons_ok_inv
          (fields := fields)
          (inScopeNames := inScopeNames)
          (stmt := stmt)
          (rest := rest)
          hcompile with
        ⟨headIR, tailIR, hhead, htail, hbody⟩
      subst hbody
      exact legacyCompatibleExternalStmtList_append
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked hstmtSurface hhead)
        (ih hnoPacked hrestSurface htail)

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
      (hsurface := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.surfaceClosed)
      (hcompile := by
        simpa [hSupported.noEvents, hSupported.noErrors] using hbodyCompile)
  exact legacyCompatibleExternalStmtList_append hparams hbody

private theorem compiled_functions_legacyCompatibleExternalBodies
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ {entries irFns},
      List.Forall₂
        (fun entry irFn =>
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
      | tail hmem =>
          exact compiled_functions_legacyCompatibleExternalBodies
            (model := model)
            (selectors := selectors)
            (hSupported := hSupported)
            htail
            (fun other hmemEntry => hentries other (by simp [hmemEntry]))
            target
            hmem

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
      intro entry hentry
      simpa [SourceSemantics.selectorFunctionPairs] using
        (List.mem_of_mem_zipLeft hentry : entry.1 ∈ selectorDispatchedFunctions model))
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
