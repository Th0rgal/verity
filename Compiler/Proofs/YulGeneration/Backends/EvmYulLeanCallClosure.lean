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

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul

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

end Compiler.Proofs.YulGeneration.Backends
