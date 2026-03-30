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
-- SORRY'D:   induction fields with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [findFieldWithResolvedSlot] at hfind
-- SORRY'D:   | cons field rest ih =>
-- SORRY'D:       simp [findFieldWithResolvedSlot] at hfind ⊢
-- SORRY'D:       by_cases hname : field.name == fieldName
-- SORRY'D:       · injection hfind with hfield _
-- SORRY'D:         subst hfield
-- SORRY'D:         simp [hname]
-- SORRY'D:       · simp [hname] at hfind
-- SORRY'D:         exact Or.inr (ih hfind)

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
-- SORRY'D:   induction hprefix generalizing suffix with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa using hsuffix
-- SORRY'D:   | comment msg rest hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.comment msg (rest ++ suffix) (ih hsuffix)
-- SORRY'D:   | let_ name value rest hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.let_ name value (rest ++ suffix) (ih hsuffix)
-- SORRY'D:   | assign name value rest hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.assign name value (rest ++ suffix) (ih hsuffix)
-- SORRY'D:   | expr value rest hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.expr value (rest ++ suffix) (ih hsuffix)
-- SORRY'D:   | if_ cond body rest hbody hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.if_ cond body (rest ++ suffix) hbody (ih hsuffix)
-- SORRY'D:   | block body rest hbody hrest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.block body (rest ++ suffix) hbody (ih hsuffix)
-- SORRY'D:   | funcDef name params rets body rest hbody hrest ih =>
-- SORRY'D:       simpa using
-- SORRY'D:         LegacyCompatibleExternalStmtList.funcDef name params rets body (rest ++ suffix) hbody (ih hsuffix)

private theorem legacyCompatibleExternalStmtList_of_exprStmtExprs
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact LegacyCompatibleExternalStmtList.nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih
-- SORRY'D:   induction exprs with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact LegacyCompatibleExternalStmtList.nil
-- SORRY'D:   | cons expr rest ih =>
-- SORRY'D:       simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

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
-- SORRY'D:   unfold CompilationModel.revertWithMessage
-- SORRY'D:   apply legacyCompatibleExternalStmtList_append
-- SORRY'D:   · exact legacyCompatibleExternalStmtList_of_exprStmtExprs
-- SORRY'D:       [ YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]
-- SORRY'D:       , YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]
-- SORRY'D:       , YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit (CompilationModel.bytesFromString message).length]
-- SORRY'D:       ]
-- SORRY'D:   · apply legacyCompatibleExternalStmtList_append
-- SORRY'D:     · exact legacyCompatibleExternalStmtList_of_exprStmtExprs
-- SORRY'D:         (((CompilationModel.chunkBytes32 (CompilationModel.bytesFromString message)).zipIdx).map
-- SORRY'D:           (fun (chunk, idx) =>
-- SORRY'D:             let offset := 68 + idx * 32
-- SORRY'D:             let word := CompilationModel.wordFromBytes chunk
-- SORRY'D:             YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word]))
-- SORRY'D:     · exact LegacyCompatibleExternalStmtList.expr
-- SORRY'D:         (YulExpr.call "revert"
-- SORRY'D:           [ YulExpr.lit 0
-- SORRY'D:           , YulExpr.lit
-- SORRY'D:               (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
-- SORRY'D:           ])
-- SORRY'D:         []
-- SORRY'D:         LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileSetStorage fields .calldata fieldName value =
-- TYPESIG_SORRY:         Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileSetStorage at hcompile
-- SORRY'D:   by_cases hmapping : isMapping fields fieldName
-- SORRY'D:   · simp [hmapping] at hcompile
-- SORRY'D:   · simp [hmapping] at hcompile
-- SORRY'D:     rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
-- SORRY'D:     · simp [hfind] at hcompile
-- SORRY'D:     · simp [hfind] at hcompile
-- SORRY'D:       rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr
-- SORRY'D:       · simp [hvalue] at hcompile
-- SORRY'D:       · simp [hvalue] at hcompile
-- SORRY'D:         have hunpacked : f.packedBits = none :=
-- SORRY'D:           hnoPacked f (field_mem_of_findFieldWithResolvedSlot_some hfind)
-- SORRY'D:         rw [hunpacked] at hcompile
-- SORRY'D:         cases halias : f.aliasSlots with
-- SORRY'D:         | nil =>
-- SORRY'D:             simp [halias] at hcompile
-- SORRY'D:             injection hcompile with hbody
-- SORRY'D:             subst hbody
-- SORRY'D:             exact LegacyCompatibleExternalStmtList.expr
-- SORRY'D:               (YulExpr.call "sstore" [YulExpr.lit slot, valueExpr])
-- SORRY'D:               []
-- SORRY'D:               LegacyCompatibleExternalStmtList.nil
-- SORRY'D:         | cons alias rest =>
-- SORRY'D:             simp [halias] at hcompile
-- SORRY'D:             injection hcompile with hbody
-- SORRY'D:             subst hbody
-- SORRY'D:             apply LegacyCompatibleExternalStmtList.block
-- SORRY'D:             · apply LegacyCompatibleExternalStmtList.let_
-- SORRY'D:               exact legacyCompatibleExternalStmtList_of_exprStmtExprs
-- SORRY'D:                 (((slot :: alias :: rest).map
-- SORRY'D:                   (fun writeSlot =>
-- SORRY'D:                     YulExpr.call "sstore"
-- SORRY'D:                       [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))
-- SORRY'D:             · exact LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames (.letVar name value) =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:   rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:     injection hcompile with hbody
-- SORRY'D:     subst hbody
-- SORRY'D:     exact LegacyCompatibleExternalStmtList.let_ name valueIR [] LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames (.assignVar name value) =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:   rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:     injection hcompile with hbody
-- SORRY'D:     subst hbody
-- SORRY'D:     exact LegacyCompatibleExternalStmtList.assign name valueIR [] LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_require
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {message : String}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames (.require cond message) =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:   rcases hfail : CompilationModel.compileRequireFailCond fields .calldata cond with _ | failCond
-- SORRY'D:   · simp [hfail] at hcompile
-- SORRY'D:   · simp [hfail] at hcompile
-- SORRY'D:     injection hcompile with hbody
-- SORRY'D:     subst hbody
-- SORRY'D:     exact LegacyCompatibleExternalStmtList.if_
-- SORRY'D:       failCond
-- SORRY'D:       (CompilationModel.revertWithMessage message)
-- SORRY'D:       []
-- SORRY'D:       (legacyCompatibleExternalStmtList_revertWithMessage message)
-- SORRY'D:       LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_return
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames (.return value) =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:   rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:   · simp [hvalue] at hcompile
-- SORRY'D:     injection hcompile with hbody
-- SORRY'D:     subst hbody
-- SORRY'D:     exact LegacyCompatibleExternalStmtList.expr
-- SORRY'D:       (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:       [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])]
-- SORRY'D:       (LegacyCompatibleExternalStmtList.expr
-- SORRY'D:         (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
-- SORRY'D:         []
-- SORRY'D:         LegacyCompatibleExternalStmtList.nil)

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames .stop =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:   injection hcompile with hbody
-- SORRY'D:   subst hbody
-- SORRY'D:   exact LegacyCompatibleExternalStmtList.expr
-- SORRY'D:     (YulExpr.call "stop" [])
-- SORRY'D:     []
-- SORRY'D:     LegacyCompatibleExternalStmtList.nil

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {stmt : Stmt}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
-- TYPESIG_SORRY:     (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmt
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   cases stmt <;> simp [stmtTouchesUnsupportedContractSurface] at hsurface
-- SORRY'D:   case letVar name value =>
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar hcompile
-- SORRY'D:   case assignVar name value =>
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar hcompile
-- SORRY'D:   case setStorage fieldName value =>
-- SORRY'D:     unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields hnoPacked hcompile
-- SORRY'D:   case require cond message =>
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileStmt_ok_require hcompile
-- SORRY'D:   case return value =>
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileStmt_ok_return hcompile
-- SORRY'D:   case stop =>
-- SORRY'D:     exact legacyCompatibleExternalStmtList_of_compileStmt_ok_stop hcompile
-- SORRY'D:   all_goals
-- SORRY'D:     cases hsurface

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_scalar
-- TYPESIG_SORRY:     (loadWord : YulExpr → YulExpr)
-- TYPESIG_SORRY:     (sizeExpr : YulExpr)
-- TYPESIG_SORRY:     (headSize baseOffset : Nat)
-- TYPESIG_SORRY:     (param : Param)
-- TYPESIG_SORRY:     (rest : List Param)
-- TYPESIG_SORRY:     (headOffset : Nat)
-- TYPESIG_SORRY:     (hparam : SupportedExternalParamType param.ty)
-- TYPESIG_SORRY:     (hrest :
-- TYPESIG_SORRY:       LegacyCompatibleExternalStmtList
-- TYPESIG_SORRY:         (CompilationModel.genParamLoadBodyFrom
-- TYPESIG_SORRY:           loadWord sizeExpr headSize baseOffset rest
-- TYPESIG_SORRY:             (headOffset + paramHeadSize param.ty))) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList
-- TYPESIG_SORRY:       (CompilationModel.genParamLoadBodyFrom
-- TYPESIG_SORRY:         loadWord sizeExpr headSize baseOffset (param :: rest) headOffset) := by sorry
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
-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_genParamLoadBodyFrom_of_supported
-- TYPESIG_SORRY:     (loadWord : YulExpr → YulExpr)
-- TYPESIG_SORRY:     (sizeExpr : YulExpr)
-- TYPESIG_SORRY:     (headSize baseOffset : Nat)
-- TYPESIG_SORRY:     (params : List Param)
-- TYPESIG_SORRY:     (headOffset : Nat)
-- TYPESIG_SORRY:     (hparams : ∀ param ∈ params, SupportedExternalParamType param.ty) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList
-- TYPESIG_SORRY:       (CompilationModel.genParamLoadBodyFrom
-- TYPESIG_SORRY:         loadWord sizeExpr headSize baseOffset params headOffset) := by sorry
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
-- SORRY'D:   induction params generalizing headOffset with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [CompilationModel.genParamLoadBodyFrom]
-- SORRY'D:   | cons param rest ih =>
-- SORRY'D:       have hparam : SupportedExternalParamType param.ty := hparams param (by simp)
-- SORRY'D:       have hrest :
-- SORRY'D:           ∀ other ∈ rest, SupportedExternalParamType other.ty := by
-- SORRY'D:         intro other hmem
-- SORRY'D:         exact hparams other (by simp [hmem])
-- SORRY'D:       exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_cons_scalar
-- SORRY'D:         loadWord sizeExpr headSize baseOffset param rest headOffset hparam (ih _ hrest)

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
-- SORRY'D:   unfold CompilationModel.genParamLoads CompilationModel.genParamLoadsFrom
-- SORRY'D:   apply LegacyCompatibleExternalStmtList.if_
-- SORRY'D:   · exact LegacyCompatibleExternalStmtList.expr
-- SORRY'D:       (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
-- SORRY'D:       []
-- SORRY'D:       LegacyCompatibleExternalStmtList.nil
-- SORRY'D:   · exact legacyCompatibleExternalStmtList_genParamLoadBodyFrom_of_supported
-- SORRY'D:       (loadWord := fun pos => YulExpr.call "calldataload" [pos])
-- SORRY'D:       (sizeExpr := YulExpr.call "calldatasize" [])
-- SORRY'D:       (headSize := (params.map (fun p => paramHeadSize p.ty)).foldl (· + ·) 0)
-- SORRY'D:       (baseOffset := 4)
-- SORRY'D:       (params := params)
-- SORRY'D:       (headOffset := 4)
-- SORRY'D:       hparams

-- TYPESIG_SORRY: private theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {inScopeNames : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
-- TYPESIG_SORRY:     (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR) :
-- TYPESIG_SORRY:     LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   induction stmts generalizing inScopeNames bodyIR with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa [CompilationModel.compileStmtList] using hcompile
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1
-- SORRY'D:       have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2
-- SORRY'D:       rcases FunctionBody.compileStmtList_cons_ok_inv
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (inScopeNames := inScopeNames)
-- SORRY'D:           (stmt := stmt)
-- SORRY'D:           (rest := rest)
-- SORRY'D:           hcompile with
-- SORRY'D:         ⟨headIR, tailIR, hhead, htail, hbody⟩
-- SORRY'D:       subst hbody
-- SORRY'D:       exact legacyCompatibleExternalStmtList_append
-- SORRY'D:         (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
-- SORRY'D:           hnoPacked hstmtSurface hhead)
-- SORRY'D:         (ih hnoPacked hrestSurface htail)

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

-- TYPESIG_SORRY: private theorem compileValidatedCore_ok_yields_supportedRuntimeHelperTableInterface
-- TYPESIG_SORRY:     (model : CompilationModel)
-- TYPESIG_SORRY:     (selectors : List Nat)
-- TYPESIG_SORRY:     (ir : IRContract)
-- TYPESIG_SORRY:     (hcore : compileValidatedCore model selectors = Except.ok ir) :
-- TYPESIG_SORRY:     SupportedRuntimeHelperTableInterface model ir := by sorry
-- SORRY'D:   let internalFns := model.functions.filter (·.isInternal)
-- SORRY'D:   unfold compileValidatedCore at hcore
-- SORRY'D:   rcases hfunctions :
-- SORRY'D:       ((model.functions.filter
-- SORRY'D:           (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
-- SORRY'D:         (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:           model.events model.errors x.2 x.1) with _ | functions
-- SORRY'D:   · simp [hfunctions] at hcore
-- SORRY'D:   · simp [hfunctions] at hcore
-- SORRY'D:     rcases hcompiledInternal :
-- SORRY'D:         internalFns.mapM
-- SORRY'D:           (compileInternalFunction
-- SORRY'D:             (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:             model.events
-- SORRY'D:             model.errors) with _ | internalFuncDefs
-- SORRY'D:     · simp [internalFns, hcompiledInternal] at hcore
-- SORRY'D:     · simp [internalFns, hcompiledInternal] at hcore
-- SORRY'D:       rcases hfallback :
-- SORRY'D:           pickUniqueFunctionByName "fallback" model.functions with _ | fallbackSpec
-- SORRY'D:       · simp [hfallback] at hcore
-- SORRY'D:       · simp [hfallback] at hcore
-- SORRY'D:         rcases hreceive :
-- SORRY'D:             pickUniqueFunctionByName "receive" model.functions with _ | receiveSpec
-- SORRY'D:         · simp [hreceive] at hcore
-- SORRY'D:         · simp [hreceive] at hcore
-- SORRY'D:           rcases hfallbackEntry :
-- SORRY'D:               fallbackSpec.mapM
-- SORRY'D:                 (compileSpecialEntrypoint
-- SORRY'D:                   (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:                   model.events
-- SORRY'D:                   model.errors) with _ | fallbackEntrypoint
-- SORRY'D:           · simp [hfallbackEntry] at hcore
-- SORRY'D:           · simp [hfallbackEntry] at hcore
-- SORRY'D:             rcases hreceiveEntry :
-- SORRY'D:                 receiveSpec.mapM
-- SORRY'D:                   (compileSpecialEntrypoint
-- SORRY'D:                     (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:                     model.events
-- SORRY'D:                     model.errors) with _ | receiveEntrypoint
-- SORRY'D:             · simp [hreceiveEntry] at hcore
-- SORRY'D:             · simp [hreceiveEntry] at hcore
-- SORRY'D:               cases hcore
-- SORRY'D:               refine ⟨?_⟩
-- SORRY'D:               intro calleeName witness
-- SORRY'D:               have hmemInternal : witness.callee ∈ internalFns := by
-- SORRY'D:                 exact List.mem_filter.mpr ⟨witness.summary.present, witness.summary.internal⟩
-- SORRY'D:               have hcompiled :
-- SORRY'D:                   List.Forall₂
-- SORRY'D:                     (fun fn internalDef =>
-- SORRY'D:                       compileInternalFunction
-- SORRY'D:                           (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:                           model.events
-- SORRY'D:                           model.errors
-- SORRY'D:                           fn = Except.ok internalDef)
-- SORRY'D:                     internalFns
-- SORRY'D:                     internalFuncDefs :=
-- SORRY'D:                 compiled_internal_functions_forall₂_of_mapM_ok
-- SORRY'D:                   (applySlotAliasRanges model.fields model.slotAliasRanges)
-- SORRY'D:                   model.events
-- SORRY'D:                   model.errors
-- SORRY'D:                   internalFns
-- SORRY'D:                   internalFuncDefs
-- SORRY'D:                   hcompiledInternal
-- SORRY'D:               rcases exists_right_of_forall₂_mem_left hcompiled hmemInternal with
-- SORRY'D:                 ⟨compiledStmt, hmemCompiled, hcompileStmt⟩
-- SORRY'D:               refine
-- SORRY'D:                 { sourceWitness := witness
-- SORRY'D:                   compiledStmt := compiledStmt
-- SORRY'D:                   compileOk := ?_
-- SORRY'D:                   presentInRuntime := ?_ }
-- SORRY'D:               · simpa using hcompileStmt
-- SORRY'D:               · simp [hmemCompiled]

-- TYPESIG_SORRY: theorem compile_ok_yields_supportedRuntimeHelperTableInterface
-- TYPESIG_SORRY:     (model : CompilationModel)
-- TYPESIG_SORRY:     (selectors : List Nat)
-- TYPESIG_SORRY:     (ir : IRContract)
-- TYPESIG_SORRY:     (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
-- TYPESIG_SORRY:     SupportedRuntimeHelperTableInterface model ir := by sorry
-- SORRY'D:   unfold CompilationModel.compile at hcompile
-- SORRY'D:   simp only [bind, Except.bind] at hcompile
-- SORRY'D:   rcases hvalidate : validateCompileInputs model selectors with _ | validated
-- SORRY'D:   · simp [hvalidate] at hcompile
-- SORRY'D:   · simp [hvalidate] at hcompile
-- SORRY'D:     exact compileValidatedCore_ok_yields_supportedRuntimeHelperTableInterface
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (ir := ir)
-- SORRY'D:       (hcore := hcompile)

-- SORRY'D: /-- On the current `SupportedSpec` fragment, successful external-function
-- SORRY'D: compilation already yields legacy-compatible helper-free IR bodies. -/
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

-- SORRY'D: /-- Helper-proof-carrying function-level generic theorem.
-- SORRY'D: This is the proof-ready theorem surface for the next helper-composition step.
-- SORRY'D: Today the additional helper-proof argument is compatibility-redundant because
-- SORRY'D: the body proof still closes helpers through the helper-excluding
-- SORRY'D: `SupportedStmtList` fragment. -/
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
-- SORRY'D:   exact compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (hvalidateInputs := hvalidateInputs)
-- SORRY'D:     (runtimeContract := runtimeContract)
-- SORRY'D:     (fn := fn)
-- SORRY'D:     (sel := sel)
-- SORRY'D:     (irFn := irFn)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (htxNormalized := htxNormalized)
-- SORRY'D:     (bindings := bindings)
-- SORRY'D:     (hcalldataSizeFits := hcalldataSizeFits)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hcompileFn := hcompileFn)
-- SORRY'D:     (hbind := hbind)
-- SORRY'D:     (hhelperIR :=
-- SORRY'D:       execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         irFn
-- SORRY'D:         tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)
-- SORRY'D:         hbodyDisjoint)

-- SORRY'D: /-- Narrow helper-aware compileFunctionSpec wrapper aligned with the current
-- SORRY'D: Tier 4 direct-helper seam. This keeps the public compile theorem on the exact
-- SORRY'D: helper-aware IR boundary while requiring callers to discharge only the direct
-- SORRY'D: statement-position helper call / helper-assign interfaces plus the two compiled
-- SORRY'D: disjointness obligations. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact Function.supported_function_correct_with_helper_proofs_direct_internal_helper_surface_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (hvalidateInputs := hvalidateInputs)
-- SORRY'D:     (runtimeContract := runtimeContract)
-- SORRY'D:     (fn := fn)
-- SORRY'D:     (selector := sel)
-- SORRY'D:     (returns := returns)
-- SORRY'D:     (bodyStmts := bodyStmts)
-- SORRY'D:     (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (bindings := bindings)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hvalidate := hvalidate)
-- SORRY'D:     (hreturns := hreturns)
-- SORRY'D:     (hbodyCompile := hbodyCompile)
-- SORRY'D:     (hcompile := by simpa using hcompileFn)
-- SORRY'D:     (hbind := hbind)
-- SORRY'D:     (htxNormalized := htxNormalized)
-- SORRY'D:     (hcall := hcall)
-- SORRY'D:     (hassign := hassign)
-- SORRY'D:     (hdisjoint := hdisjoint)
-- SORRY'D:     (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:     (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing helper-aware wrapper stated over reusable single-head direct
-- SORRY'D: helper builders instead of preassembled list interfaces. This is the exact
-- SORRY'D: Tier 4 public seam that future rank induction should target at function
-- SORRY'D: compilation boundaries. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCall calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact Function.supported_function_correct_with_helper_proofs_direct_internal_helper_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (hvalidateInputs := hvalidateInputs)
-- SORRY'D:     (runtimeContract := runtimeContract)
-- SORRY'D:     (fn := fn)
-- SORRY'D:     (selector := sel)
-- SORRY'D:     (returns := returns)
-- SORRY'D:     (bodyStmts := bodyStmts)
-- SORRY'D:     (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (bindings := bindings)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hvalidate := hvalidate)
-- SORRY'D:     (hreturns := hreturns)
-- SORRY'D:     (hbodyCompile := hbodyCompile)
-- SORRY'D:     (hcompile := by simpa using hcompileFn)
-- SORRY'D:     (hbind := hbind)
-- SORRY'D:     (htxNormalized := htxNormalized)
-- SORRY'D:     (hcallStep := hcallStep)
-- SORRY'D:     (hassignStep := hassignStep)
-- SORRY'D:     (hdisjoint := hdisjoint)
-- SORRY'D:     (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:     (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper whose direct-helper head-step assumptions are
-- SORRY'D: indexed only by helper callees that actually occur in the current function
-- SORRY'D: body. This matches the body-local helper-rank inventory. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hcallStep :
-- SORRY'D:       ∀ {scope : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         calleeName ∈ helperCallNames fn →
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCall calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hassignStep :
-- SORRY'D:       ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
-- SORRY'D:         calleeName ∈ helperCallNames fn →
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompiledStmtStepWithHelpersAndHelperIR
-- SORRY'D:             runtimeContract
-- SORRY'D:             model
-- SORRY'D:             (SourceSemantics.effectiveFields model)
-- SORRY'D:             scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:             compiledIR)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact Function.supported_function_correct_with_helper_proofs_direct_internal_helper_body_call_names_head_steps_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (hSupported := hSupported)
-- SORRY'D:     (hHelperProofs := hHelperProofs)
-- SORRY'D:     (hvalidateInputs := hvalidateInputs)
-- SORRY'D:     (runtimeContract := runtimeContract)
-- SORRY'D:     (fn := fn)
-- SORRY'D:     (selector := sel)
-- SORRY'D:     (returns := returns)
-- SORRY'D:     (bodyStmts := bodyStmts)
-- SORRY'D:     (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (bindings := bindings)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hvalidate := hvalidate)
-- SORRY'D:     (hreturns := hreturns)
-- SORRY'D:     (hbodyCompile := hbodyCompile)
-- SORRY'D:     (hcompile := by simpa using hcompileFn)
-- SORRY'D:     (hbind := hbind)
-- SORRY'D:     (htxNormalized := htxNormalized)
-- SORRY'D:     (hcallStep := hcallStep)
-- SORRY'D:     (hassignStep := hassignStep)
-- SORRY'D:     (hdisjoint := hdisjoint)
-- SORRY'D:     (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:     (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper that consumes a single direct-helper head-step
-- SORRY'D: catalog for the current function body. This is the contract-level target future
-- SORRY'D: helper-rank induction should instantiate. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hcatalog :
-- SORRY'D:       DirectInternalHelperHeadStepCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog := hcatalog)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper one seam earlier than
-- SORRY'D: `...head_step_catalog...`: callers provide singleton direct-helper compilation
-- SORRY'D: and bridge proofs for the current body, and the reusable head-step catalog is
-- SORRY'D: assembled here. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hbridge :
-- SORRY'D:       DirectInternalHelperHeadStepBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
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
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_bridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hbridge)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper on the callee-local bridge boundary. This is
-- SORRY'D: the contract-level seam that matches the helper-rank inventory directly:
-- SORRY'D: callers provide one reusable bridge object per helper callee referenced by the
-- SORRY'D: current body, and the body-level bridge catalog is assembled here. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hcallee :
-- SORRY'D:       DirectInternalHelperPerCalleeBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hcallee)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper on the assign-only callee-local bridge
-- SORRY'D: boundary. Under the current fragment, the void-call helper bridge half is still
-- SORRY'D: vacuous, so callers only need one reusable assign bridge per referenced helper
-- SORRY'D: callee, and this wrapper now lands directly on the exact body-level
-- SORRY'D: head-step catalog target instead of routing through the narrower function-level
-- SORRY'D: assign-bridge theorem. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadAssignBridge :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_head_step_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hcatalog :=
-- SORRY'D:         directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (hSupported.supportedFunctionOfSelectorDispatched hfn).body
-- SORRY'D:           hheadAssignBridge)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper on the fully split callee-local boundary.
-- SORRY'D: Callers can provide direct-helper head compilation and semantic bridge
-- SORRY'D: catalogs separately; they are reassembled into the existing per-callee bridge
-- SORRY'D: catalog at this boundary. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticBridgeCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_semantic_bridge_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadSemantic := hheadSemantic)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Compile-facing Tier 4 wrapper that separates runtime helper lookup from the
-- SORRY'D: remaining semantic singleton-step work. This matches the contract-level split:
-- SORRY'D: compiled runtimes can provide helper witnesses independently, while future rank
-- SORRY'D: induction only needs to supply the semantic core catalog. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         fn)
-- SORRY'D:     (hheadSemantic :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticCoreCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_core_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hruntimeWitness := hruntimeWitness)
-- SORRY'D:       (hheadSemantic := hheadSemantic)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Contract-level Tier 4 wrapper on the smaller semantic-kernel seam. This
-- SORRY'D: lets callers reuse the supported-function helper inventory already present at
-- SORRY'D: the contract theorem boundary instead of packaging a full semantic core
-- SORRY'D: catalog by hand. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hruntimeWitness :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_witness_catalog_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hruntimeWitness := hruntimeWitness)
-- SORRY'D:       (hheadKernel := hheadKernel)
-- SORRY'D:        (hdisjoint := hdisjoint)
-- SORRY'D:        (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:        (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Contract-level Tier 4 wrapper one seam earlier than the runtime-witness
-- SORRY'D: catalog boundary. A compiled runtime helper table is enough to reconstruct the
-- SORRY'D: per-callee runtime witnesses for `fn`, so the remaining explicit helper-side
-- SORRY'D: obligations are just the compile catalog and semantic kernel. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadKernel := hheadKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:        (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:        (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- SORRY'D: keeps the public function theorem aligned with the roadmap's assign-first
-- SORRY'D: helper wiring while still reusing the existing combined semantic-kernel chain
-- SORRY'D: internally. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadAssignCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   rcases Function.compileFunctionSpec_ok_components
-- SORRY'D:       model.fields model.events model.errors sel fn irFn hcompileFn with
-- SORRY'D:     ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
-- SORRY'D:   subst hirFn
-- SORRY'D:   exact
-- SORRY'D:     Function.supported_function_correct_with_helper_proofs_direct_internal_helper_assign_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (selector := sel)
-- SORRY'D:       (returns := returns)
-- SORRY'D:       (bodyStmts := bodyStmts)
-- SORRY'D:       (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
-- SORRY'D:       (tx := tx)
-- SORRY'D:       (initialWorld := initialWorld)
-- SORRY'D:       (bindings := bindings)
-- SORRY'D:       (hfn := hfn)
-- SORRY'D:       (hvalidate := hvalidate)
-- SORRY'D:       (hreturns := hreturns)
-- SORRY'D:       (hbodyCompile := hbodyCompile)
-- SORRY'D:       (hcompile := by simpa using hcompileFn)
-- SORRY'D:       (hbind := hbind)
-- SORRY'D:       (htxNormalized := htxNormalized)
-- SORRY'D:       (hheadAssignCompile := hheadAssignCompile)
-- SORRY'D:       (hheadAssignKernel := hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := by simpa using hfnBodyDisjoint)
-- SORRY'D:       (hcalldataSizeFits := hcalldataSizeFits)

-- SORRY'D: /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- SORRY'D: keeps the public function theorem aligned with the roadmap's assign-first
-- SORRY'D: helper wiring while still reusing the existing combined semantic-kernel chain
-- SORRY'D: internally. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
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
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadCallKernel :=
-- SORRY'D:         directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           (hSupported.supportedFunctionOfSelectorDispatched hfn).body)
-- SORRY'D:       (hheadAssignKernel := hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)

-- SORRY'D: /-- Contract-level Tier 4 wrapper on the split semantic-kernel boundary. This
-- SORRY'D: keeps the public function theorem aligned with the roadmap's assign-first
-- SORRY'D: helper wiring while still reusing the existing combined semantic-kernel chain
-- SORRY'D: internally. -/
-- SORRY'D: theorem
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_call_semantic_kernel_catalog_and_assign_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (selectors : List Nat)
-- SORRY'D:     (hSupported : SupportedSpec model selectors)
-- SORRY'D:     (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
-- SORRY'D:     (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (hRuntime : SupportedRuntimeHelperTableInterface model runtimeContract)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (sel : Nat)
-- SORRY'D:     (irFn : IRFunction)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (htxNormalized : Function.TxContextNormalized tx)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
-- SORRY'D:     (hfn : fn ∈ selectorDispatchedFunctions model)
-- SORRY'D:     (hcompileFn :
-- SORRY'D:       compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn)
-- SORRY'D:     (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
-- SORRY'D:     (hheadCompile :
-- SORRY'D:       DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadCallKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeCallSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hheadAssignKernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         fn)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hfnBodyDisjoint :
-- SORRY'D:       YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
-- SORRY'D:     FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:       (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:       (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
-- SORRY'D:         (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:   exact
-- SORRY'D:     compileFunctionSpec_correct_generic_with_helper_proofs_direct_internal_helper_per_callee_compile_catalog_and_runtime_helper_table_and_semantic_kernel_catalog_and_helper_ir_of_bodyCallsDisjoint
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (hRuntime := hRuntime)
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
-- SORRY'D:       (hheadCompile := hheadCompile)
-- SORRY'D:       (hheadKernel :=
-- SORRY'D:         directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
-- SORRY'D:           (runtimeContract := runtimeContract)
-- SORRY'D:           (spec := model)
-- SORRY'D:           (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:           (fn := fn)
-- SORRY'D:           hheadCallKernel
-- SORRY'D:           hheadAssignKernel)
-- SORRY'D:       (hdisjoint := hdisjoint)
-- SORRY'D:       (hfnBodyDisjoint := hfnBodyDisjoint)

-- SORRY'D: /-- Primary whole-contract Layer 2 theorem: compilation preserves semantics
-- SORRY'D: for any supported `CompilationModel`. No contract-specific bridge premise.
-- SORRY'D: Layer 2 itself is axiom-free; the remaining documented project axiom is the
-- SORRY'D: selector-level `keccak256_first_4_bytes` assumption tracked in `AXIOMS.md`. -/
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
-- SORRY'D:   have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
-- SORRY'D:     unfold CompilationModel.compile at hcompile
-- SORRY'D:     simp only [bind, Except.bind] at hcompile
-- SORRY'D:     rcases hvalidate : validateCompileInputs model selectors with _ | validated
-- SORRY'D:     · simp [hvalidate] at hcompile
-- SORRY'D:     · simpa using hvalidate
-- SORRY'D:   have hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         ir.functions :=
-- SORRY'D:     compile_ok_yields_compiled_functions
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (ir := ir)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:   have hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
-- SORRY'D:     supported_params_of_supportedSpec model selectors hSupported
-- SORRY'D:   have hfunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (SourceSemantics.interpretFunction model fn tx initialWorld)
-- SORRY'D:           (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact compileFunctionSpec_correct_generic
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
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
-- SORRY'D:   have hcontract :=
-- SORRY'D:     compile_preserves_semantics_of_compiled_functions
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (ir := ir)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (_hcompile := hcompile)
-- SORRY'D:     (hcompiled := hcompiled)
-- SORRY'D:     (hparamsSupported := hparamsSupported)
-- SORRY'D:     (hfunction := hfunction)
-- SORRY'D:   simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
-- SORRY'D:     (hSupported := hSupported) tx initialWorld] using hcontract

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
-- SORRY'D:   have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
-- SORRY'D:     unfold CompilationModel.compile at hcompile
-- SORRY'D:     simp only [bind, Except.bind] at hcompile
-- SORRY'D:     rcases hvalidate : validateCompileInputs model selectors with _ | validated
-- SORRY'D:     · simp [hvalidate] at hcompile
-- SORRY'D:     · simpa using hvalidate
-- SORRY'D:   have hcompiled :
-- SORRY'D:       List.Forall₂
-- SORRY'D:         (fun entry irFn =>
-- SORRY'D:           compileFunctionSpec model.fields model.events model.errors entry.2 entry.1 = Except.ok irFn)
-- SORRY'D:         (SourceSemantics.selectorFunctionPairs model selectors)
-- SORRY'D:         ir.functions :=
-- SORRY'D:     compile_ok_yields_compiled_functions
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (ir := ir)
-- SORRY'D:       (hcompile := hcompile)
-- SORRY'D:   have hparamsSupported :
-- SORRY'D:       ∀ fn ∈ selectorDispatchedFunctions model,
-- SORRY'D:         ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
-- SORRY'D:     supported_params_of_supportedSpec model selectors hSupported
-- SORRY'D:   have hfunction :
-- SORRY'D:       ∀ fn sel irFn bindings,
-- SORRY'D:         fn ∈ selectorDispatchedFunctions model →
-- SORRY'D:         compileFunctionSpec model.fields model.events model.errors sel fn = Except.ok irFn →
-- SORRY'D:         SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
-- SORRY'D:         FunctionBody.sourceResultMatchesIRResult
-- SORRY'D:           (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
-- SORRY'D:           (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
-- SORRY'D:     intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:     exact compileFunctionSpec_correct_generic_with_helper_proofs
-- SORRY'D:       (model := model)
-- SORRY'D:       (selectors := selectors)
-- SORRY'D:       (hSupported := hSupported)
-- SORRY'D:       (hHelperProofs := hHelperProofs)
-- SORRY'D:       (hvalidateInputs := hvalidateInputs)
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
-- SORRY'D:   exact compile_preserves_semantics_of_compiled_functions
-- SORRY'D:     (model := model)
-- SORRY'D:     (selectors := selectors)
-- SORRY'D:     (ir := ir)
-- SORRY'D:     (tx := tx)
-- SORRY'D:     (initialWorld := initialWorld)
-- SORRY'D:     (_hcompile := hcompile)
-- SORRY'D:     (hcompiled := hcompiled)
-- SORRY'D:     (hparamsSupported := hparamsSupported)
-- SORRY'D:     (hfunction := by
-- SORRY'D:       intro fn sel irFn bindings hfn hcompileFn hbind
-- SORRY'D:       simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
-- SORRY'D:         (hSupported := hSupported) hfn tx initialWorld] using
-- SORRY'D:         hfunction fn sel irFn bindings hfn hcompileFn hbind)

-- SORRY'D: /-- Helper-aware compiled-side wrapper for the whole-contract theorem.
-- SORRY'D: The remaining compiled-side blocker is exactly the conservative-extension proof
-- SORRY'D: that supplies `hhelperIR`; once that theorem is available, the public Layer 2
-- SORRY'D: contract theorem can retarget to `interpretIRWithInternals` without another
-- SORRY'D: interface change in `Contract.lean`. -/
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
