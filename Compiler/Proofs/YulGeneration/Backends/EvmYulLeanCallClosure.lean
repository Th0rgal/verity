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

  The predicates defined here are consumed by `compileStmtList_always_bridged`
  extension lemmas in a follow-up; this file ships the predicate scaffolding
  only.

  Run: `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanCallClosure`
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul

/-- A Yul call expression to a user-defined Yul function (either an internal
helper or an external-call stub), with each argument satisfying `BridgedExpr`.

This is the closure unit for `internalCall`, `internalCallAssign`, and
`externalCallBind`: each compiles to `YulExpr.call <func_name> args` where
`func_name` is NOT a builtin but a user-defined Yul function declared in the
emitted contract's helper-function table.

The bridge to native EVMYulLean requires that the function table entry for
`func_name` is itself bridged — that hypothesis is captured at the
statement-list closure level (via a function-table parameter), not here. -/
inductive BridgedUserFunctionCall : YulExpr → Prop
  | call (funcName : String) (args : List YulExpr)
      (hArgs : ∀ arg ∈ args, BridgedExpr arg) :
      BridgedUserFunctionCall (.call funcName args)

/-- Statement-level closure: a `YulStmt.expr (.call <user_fn> args)` invocation
where args satisfy `BridgedExpr`. Captures the compiled shape of
`Stmt.internalCall` and the no-result variant of `Stmt.externalCallBind`. -/
inductive BridgedUserFunctionCallExpr : YulStmt → Prop
  | mk (funcName : String) (args : List YulExpr)
      (hCall : BridgedUserFunctionCall (.call funcName args)) :
      BridgedUserFunctionCallExpr (.expr (.call funcName args))

/-- Statement-level closure: a `YulStmt.letMany names (.call <user_fn> args)`
binding where args satisfy `BridgedExpr`. Captures the compiled shape of
`Stmt.internalCallAssign` and the with-result variant of
`Stmt.externalCallBind`. -/
inductive BridgedUserFunctionCallBind : YulStmt → Prop
  | mk (names : List String) (funcName : String) (args : List YulExpr)
      (hCall : BridgedUserFunctionCall (.call funcName args)) :
      BridgedUserFunctionCallBind (.letMany names (.call funcName args))

/-- A statement list whose elements are all `BridgedUserFunctionCallExpr` or
`BridgedUserFunctionCallBind` (the two compiled shapes a user-function call
can take). -/
inductive BridgedUserFunctionCallStmts : List YulStmt → Prop
  | nil : BridgedUserFunctionCallStmts []
  | consExpr {stmt : YulStmt} {rest : List YulStmt}
      (hHead : BridgedUserFunctionCallExpr stmt)
      (hRest : BridgedUserFunctionCallStmts rest) :
      BridgedUserFunctionCallStmts (stmt :: rest)
  | consBind {stmt : YulStmt} {rest : List YulStmt}
      (hHead : BridgedUserFunctionCallBind stmt)
      (hRest : BridgedUserFunctionCallStmts rest) :
      BridgedUserFunctionCallStmts (stmt :: rest)

end Compiler.Proofs.YulGeneration.Backends
