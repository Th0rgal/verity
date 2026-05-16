/-
  Function-table-aware call closure for `BridgedSafeStmts`.

  This module extends the `BridgedStmts` whitelist to cover the four call
  families that are currently carved out of `compileStmtList_always_bridged`:

  - `internalCall` — Verity helper invoked as a statement, compiles to
    `YulStmt.expr (YulExpr.call <internal_name> args)`.
  - `internalCallAssign` — same with multi-value binding, compiles to
    `YulStmt.letMany names (YulExpr.call <internal_name> args)`.
  - `externalCallBind` — typed external contract call, compiles to either
    of the two shapes above with `<external_stub_name>` instead.
  - `ecm` — External Call Module (per-module compile, opaque shape).

  Each call shape requires a function-table hypothesis: the callee must
  resolve to a function whose body is itself in the bridged-stmt fragment.

  Run: `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanCallClosure`
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSourceExprClosure
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.InternalNaming

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel

/-- A flat helper-function table: name → bridged body. Carrying `BridgedStmts`
in the entries means the table itself is the proof that every callable user
function has a bridged body. This makes user-function-call closures
parameterizable without mutual recursion. -/
def BridgedFunctionTable := List (String × { body : List YulStmt // BridgedStmts body })

/-- Look up a function name in a `BridgedFunctionTable`. Returns the body
together with its `BridgedStmts` witness, packaged as a subtype. -/
def BridgedFunctionTable.lookup
    (table : BridgedFunctionTable) (name : String) :
    Option { body : List YulStmt // BridgedStmts body } :=
  match table.find? (fun entry => entry.fst == name) with
  | some (_, witness) => some witness
  | none => none

/-- A Yul call expression to a user-defined Yul function, with each argument
satisfying `BridgedExpr` AND the callee resolving to a bridged body in the
helper-function table.

This is the closure unit for `internalCall`, `internalCallAssign`, and
`externalCallBind`: each compiles to `YulExpr.call <func_name> args` where
`func_name` is NOT a builtin but a user-defined Yul function declared in the
emitted contract's helper-function table. -/
inductive BridgedUserFunctionCall
    (table : BridgedFunctionTable) : YulExpr → Prop
  | call (funcName : String) (args : List YulExpr)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg)
      (hFn : (BridgedFunctionTable.lookup table funcName).isSome) :
      BridgedUserFunctionCall table (.call funcName args)

/-- Statement-level closure: a `YulStmt.expr (.call <user_fn> args)` invocation
where args satisfy `BridgedExpr` and the callee resolves in `table`. Captures
the compiled shape of `Stmt.internalCall` and the no-result variant of
`Stmt.externalCallBind`. -/
inductive BridgedUserFunctionCallExpr
    (table : BridgedFunctionTable) : YulStmt → Prop
  | mk (funcName : String) (args : List YulExpr)
      (hCall : BridgedUserFunctionCall table (.call funcName args)) :
      BridgedUserFunctionCallExpr table (.expr (.call funcName args))

/-- Statement-level closure: a `YulStmt.letMany names (.call <user_fn> args)`
binding where args satisfy `BridgedExpr` and the callee resolves in `table`.
Captures the compiled shape of `Stmt.internalCallAssign` and the with-result
variant of `Stmt.externalCallBind`. -/
inductive BridgedUserFunctionCallBind
    (table : BridgedFunctionTable) : YulStmt → Prop
  | mk (names : List String) (funcName : String) (args : List YulExpr)
      (hCall : BridgedUserFunctionCall table (.call funcName args)) :
      BridgedUserFunctionCallBind table (.letMany names (.call funcName args))

/-- A statement list whose elements are all `BridgedUserFunctionCallExpr` or
`BridgedUserFunctionCallBind` (the two compiled shapes a user-function call
can take). -/
inductive BridgedUserFunctionCallStmts
    (table : BridgedFunctionTable) : List YulStmt → Prop
  | nil : BridgedUserFunctionCallStmts table []
  | consExpr {stmt : YulStmt} {rest : List YulStmt}
      (hHead : BridgedUserFunctionCallExpr table stmt)
      (hRest : BridgedUserFunctionCallStmts table rest) :
      BridgedUserFunctionCallStmts table (stmt :: rest)
  | consBind {stmt : YulStmt} {rest : List YulStmt}
      (hHead : BridgedUserFunctionCallBind table stmt)
      (hRest : BridgedUserFunctionCallStmts table rest) :
      BridgedUserFunctionCallStmts table (stmt :: rest)

/-- The natural converse: every entry's body in a `BridgedFunctionTable` is
itself bridged. Lifted from the subtype carrier. -/
theorem BridgedFunctionTable.bodies_bridged
    (_table : BridgedFunctionTable)
    (_name : String) {witness : { body : List YulStmt // BridgedStmts body }}
    (_hLookup : _table.lookup _name = some witness) :
    BridgedStmts witness.val :=
  witness.property

/-- Bridge: `BridgedUserFunctionCallExpr table stmt` implies `BridgedStmt stmt`
by extracting the callee witness from the table and applying
`BridgedStmt.userCallExpr`. -/
theorem BridgedStmt.of_userFunctionCallExpr
    {table : BridgedFunctionTable} {stmt : YulStmt}
    (h : BridgedUserFunctionCallExpr table stmt) :
    BridgedStmt stmt := by
  cases h with
  | mk funcName args hCall =>
    cases hCall with
    | call _ _ hArgs hFn =>
      match hLookup : table.lookup funcName with
      | none => simp [hLookup] at hFn
      | some witness =>
        exact BridgedStmt.userCallExpr funcName args witness.val hArgs
          witness.property

/-- Bridge for the `letMany` variant. -/
theorem BridgedStmt.of_userFunctionCallBind
    {table : BridgedFunctionTable} {stmt : YulStmt}
    (h : BridgedUserFunctionCallBind table stmt) :
    BridgedStmt stmt := by
  cases h with
  | mk names funcName args hCall =>
    cases hCall with
    | call _ _ hArgs hFn =>
      match hLookup : table.lookup funcName with
      | none => simp [hLookup] at hFn
      | some witness =>
        exact BridgedStmt.userCallBind names funcName args witness.val hArgs
          witness.property

/-- A list of `BridgedUserFunctionCall{Expr,Bind}` statements is bridged. -/
theorem BridgedStmts_of_userFunctionCallStmts
    {table : BridgedFunctionTable} {stmts : List YulStmt}
    (h : BridgedUserFunctionCallStmts table stmts) :
    BridgedStmts stmts := by
  induction h with
  | nil =>
    intro stmt hMem
    cases hMem
  | consExpr hHead _ ih =>
    intro stmt hMem
    cases hMem with
    | head => exact BridgedStmt.of_userFunctionCallExpr hHead
    | tail _ hTail => exact ih stmt hTail
  | consBind hHead _ ih =>
    intro stmt hMem
    cases hMem with
    | head => exact BridgedStmt.of_userFunctionCallBind hHead
    | tail _ hTail => exact ih stmt hTail

/-! ## Phase 2: source-level closure for `Stmt.internalCall` / `Stmt.internalCallAssign`

Given a `BridgedFunctionTable` whose keys are the compiled internal-function
names (`internalFunctionYulName <source_name>`), a source-level
`Stmt.internalCall` or `Stmt.internalCallAssign` with bridged argument
expressions compiles to a `BridgedUserFunctionCall{Expr,Bind}` Yul shape.
-/

/-- A source `Stmt.internalCall` or `Stmt.internalCallAssign` whose arguments
are bridged at the source level AND whose callee resolves in the function
table under its compiled Yul name. -/
inductive BridgedSourceInternalCallStmt
    (table : BridgedFunctionTable) : Stmt → Prop
  | call (funcName : String) (args : List Expr)
      (hArgs : ∀ a ∈ args, BridgedSourceExpr a)
      (hFn : (BridgedFunctionTable.lookup table
        (internalFunctionYulName funcName)).isSome) :
      BridgedSourceInternalCallStmt table (.internalCall funcName args)
  | callAssign (names : List String) (funcName : String) (args : List Expr)
      (hArgs : ∀ a ∈ args, BridgedSourceExpr a)
      (hFn : (BridgedFunctionTable.lookup table
        (internalFunctionYulName funcName)).isSome) :
      BridgedSourceInternalCallStmt table
        (.internalCallAssign names funcName args)

/-- Phase 2.1: compiling a source `Stmt.internalCall` with bridged arguments
and a callee that resolves in `table` yields a `BridgedStmts` output. -/
theorem compileStmt_internalCall_bridged
    {table : BridgedFunctionTable}
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    {stmt : Stmt} (hStmt : BridgedSourceInternalCallStmt table stmt)
    {out : List YulStmt}
    (hOk : compileStmt fields events errors dynamicSource internalRetNames
      isInternal inScopeNames adtTypes stmt = .ok out) :
    BridgedStmts out := by
  cases hStmt with
  | call funcName args hArgs hFn =>
    simp only [compileStmt, bind, Except.bind] at hOk
    cases hExprs : compileExprList fields dynamicSource args with
    | error _ => simp [hExprs] at hOk
    | ok argExprs =>
      simp [hExprs, Pure.pure, Except.pure] at hOk
      subst out
      have hArgsBridged : ∀ y ∈ argExprs, BridgedExpr y :=
        compileExprList_bridgedSource fields dynamicSource hArgs hExprs
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      exact BridgedStmt.of_userFunctionCallExpr
        (BridgedUserFunctionCallExpr.mk (internalFunctionYulName funcName)
          argExprs
          (BridgedUserFunctionCall.call (internalFunctionYulName funcName)
            argExprs hArgsBridged hFn))
  | callAssign names funcName args hArgs hFn =>
    simp only [compileStmt, bind, Except.bind] at hOk
    cases hExprs : compileExprList fields dynamicSource args with
    | error _ => simp [hExprs] at hOk
    | ok argExprs =>
      simp [hExprs, Pure.pure, Except.pure] at hOk
      subst out
      have hArgsBridged : ∀ y ∈ argExprs, BridgedExpr y :=
        compileExprList_bridgedSource fields dynamicSource hArgs hExprs
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      exact BridgedStmt.of_userFunctionCallBind
        (BridgedUserFunctionCallBind.mk names (internalFunctionYulName funcName)
          argExprs
          (BridgedUserFunctionCall.call (internalFunctionYulName funcName)
            argExprs hArgsBridged hFn))

/-- A list of source statements, each in `BridgedSourceInternalCallStmt`. -/
inductive BridgedSourceInternalCallStmts
    (table : BridgedFunctionTable) : List Stmt → Prop
  | nil : BridgedSourceInternalCallStmts table []
  | cons {stmt : Stmt} {rest : List Stmt}
      (hHead : BridgedSourceInternalCallStmt table stmt)
      (hRest : BridgedSourceInternalCallStmts table rest) :
      BridgedSourceInternalCallStmts table (stmt :: rest)

/-- List-level closure: `compileStmtList` over a list of internal-call source
statements (with table-resolving callees) yields a `BridgedStmts` output. -/
theorem compileStmtList_internalCall_bridged
    {table : BridgedFunctionTable}
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (adtTypes : List AdtTypeDef) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalCallStmts table stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames adtTypes stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
    intro _ _ _ hOk
    simp [compileStmtList, Pure.pure, Except.pure] at hOk
    subst hOk
    intro _ hMem
    cases hMem
  | cons s ss ih =>
    intro inScopeNames hStmts out hOk
    cases hStmts with
    | cons hHead hRest =>
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHeadOk : compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes s with
      | error _ => simp [hHeadOk] at hOk
      | ok headOut =>
        simp [hHeadOk] at hOk
        cases hTailOk : compileStmtList fields events errors dynamicSource
          internalRetNames isInternal (collectStmtNames s ++ inScopeNames)
          adtTypes ss with
        | error _ => simp [hTailOk] at hOk
        | ok tailOut =>
          simp [hTailOk, Pure.pure, Except.pure] at hOk
          subst out
          have hHeadBridged : BridgedStmts headOut :=
            compileStmt_internalCall_bridged fields events errors dynamicSource
              internalRetNames isInternal inScopeNames adtTypes hHead hHeadOk
          have hTailBridged : BridgedStmts tailOut :=
            ih _ hRest hTailOk
          intro yulStmt hMem
          rcases List.mem_append.mp hMem with hHead' | hTail'
          · exact hHeadBridged yulStmt hHead'
          · exact hTailBridged yulStmt hTail'

/-! ## Phase 2.3: source-level closure for `Stmt.externalCallBind`

`Stmt.externalCallBind resultVars externalName args` compiles to either
`YulStmt.expr (YulExpr.call externalName argExprs)` (when `resultVars = []`)
or `YulStmt.letMany resultVars (YulExpr.call externalName argExprs)`.  In
both shapes the callee is the literal `externalName` (no `internal_` prefix)
and resolves directly in the function table. -/

/-- A source `Stmt.externalCallBind` whose argument expressions are
`BridgedSourceExpr` and whose callee resolves in `table` under its
literal name. -/
inductive BridgedSourceExternalCallBindStmt
    (table : BridgedFunctionTable) : Stmt → Prop
  | mk (resultVars : List String) (externalName : String) (args : List Expr)
      (hArgs : ∀ a ∈ args, BridgedSourceExpr a)
      (hFn : (BridgedFunctionTable.lookup table externalName).isSome) :
      BridgedSourceExternalCallBindStmt table
        (.externalCallBind resultVars externalName args)

/-- Phase 2.3: compiling a source `Stmt.externalCallBind` with bridged
arguments and a callee that resolves in `table` yields a `BridgedStmts`
output. Branches on whether `resultVars` is empty (the `.expr` shape) or
not (the `.letMany` shape). -/
theorem compileStmt_externalCallBind_bridged
    {table : BridgedFunctionTable}
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) (adtTypes : List AdtTypeDef)
    {stmt : Stmt} (hStmt : BridgedSourceExternalCallBindStmt table stmt)
    {out : List YulStmt}
    (hOk : compileStmt fields events errors dynamicSource internalRetNames
      isInternal inScopeNames adtTypes stmt = .ok out) :
    BridgedStmts out := by
  cases hStmt with
  | mk resultVars externalName args hArgs hFn =>
    simp only [compileStmt, bind, Except.bind] at hOk
    cases hExprs : compileExprList fields dynamicSource args with
    | error _ => simp [hExprs] at hOk
    | ok argExprs =>
      simp [hExprs] at hOk
      have hArgsBridged : ∀ y ∈ argExprs, BridgedExpr y :=
        compileExprList_bridgedSource fields dynamicSource hArgs hExprs
      cases hEmpty : resultVars with
      | nil =>
        simp [hEmpty, Pure.pure, Except.pure] at hOk
        subst out
        intro yulStmt hMem
        simp only [List.mem_singleton] at hMem
        subst yulStmt
        exact BridgedStmt.of_userFunctionCallExpr
          (BridgedUserFunctionCallExpr.mk externalName argExprs
            (BridgedUserFunctionCall.call externalName argExprs hArgsBridged
              hFn))
      | cons head tail =>
        simp [hEmpty, Pure.pure, Except.pure] at hOk
        subst out
        intro yulStmt hMem
        simp only [List.mem_singleton] at hMem
        subst yulStmt
        exact BridgedStmt.of_userFunctionCallBind
          (BridgedUserFunctionCallBind.mk (head :: tail) externalName argExprs
            (BridgedUserFunctionCall.call externalName argExprs hArgsBridged
              hFn))

/-- A list of `Stmt.externalCallBind` source statements, all in
`BridgedSourceExternalCallBindStmt`. -/
inductive BridgedSourceExternalCallBindStmts
    (table : BridgedFunctionTable) : List Stmt → Prop
  | nil : BridgedSourceExternalCallBindStmts table []
  | cons {stmt : Stmt} {rest : List Stmt}
      (hHead : BridgedSourceExternalCallBindStmt table stmt)
      (hRest : BridgedSourceExternalCallBindStmts table rest) :
      BridgedSourceExternalCallBindStmts table (stmt :: rest)

/-- List-level closure for `Stmt.externalCallBind`. -/
theorem compileStmtList_externalCallBind_bridged
    {table : BridgedFunctionTable}
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (adtTypes : List AdtTypeDef) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalCallBindStmts table stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames adtTypes stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
    intro _ _ _ hOk
    simp [compileStmtList, Pure.pure, Except.pure] at hOk
    subst hOk
    intro _ hMem
    cases hMem
  | cons s ss ih =>
    intro inScopeNames hStmts out hOk
    cases hStmts with
    | cons hHead hRest =>
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHeadOk : compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes s with
      | error _ => simp [hHeadOk] at hOk
      | ok headOut =>
        simp [hHeadOk] at hOk
        cases hTailOk : compileStmtList fields events errors dynamicSource
          internalRetNames isInternal (collectStmtNames s ++ inScopeNames)
          adtTypes ss with
        | error _ => simp [hTailOk] at hOk
        | ok tailOut =>
          simp [hTailOk, Pure.pure, Except.pure] at hOk
          subst out
          have hHeadBridged : BridgedStmts headOut :=
            compileStmt_externalCallBind_bridged fields events errors
              dynamicSource internalRetNames isInternal inScopeNames adtTypes
              hHead hHeadOk
          have hTailBridged : BridgedStmts tailOut :=
            ih _ hRest hTailOk
          intro yulStmt hMem
          rcases List.mem_append.mp hMem with hHead' | hTail'
          · exact hHeadBridged yulStmt hHead'
          · exact hTailBridged yulStmt hTail'

end Compiler.Proofs.YulGeneration.Backends
