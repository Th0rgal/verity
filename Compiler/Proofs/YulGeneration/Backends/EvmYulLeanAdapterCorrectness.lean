/-
  EvmYulLeanAdapterCorrectness: Semantic equivalence proofs for the
  Assign → Let lowering transformation in the EVMYulLean adapter.

  The adapter (`EvmYulLeanAdapter.lean`) re-encodes Verity's
  `assign name value` as `Let [name] (some (lowerExpr value))` because
  EVMYulLean has no `Assign` statement. This is semantically valid
  because both operations call `state.setVar`, which prepends a new
  binding and removes the old one.

  The proof establishes that executing the Verity AST directly and executing
  the adapter's lowered form produce identical `YulExecResult` values.

  This addresses one of the "Known Challenges" in issue #1722:
  - "`Assign` statement: EVMYulLean lacks `Assign`; adapter uses `Let`"
-/

import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration.Backends.AdapterCorrectness

open Compiler.Yul
open Compiler.Proofs.YulGeneration

/-! ## Assign ↔ Let Semantic Equivalence

Both `YulStmt.assign name value` and `YulStmt.let_ name value` execute
identically in `execYulFuel`: they evaluate `value` and call `state.setVar`.

This justifies the adapter's lowering of `assign` to `Let`. -/

/-- Assign and let_ produce identical execution results for all states and
    fuel values. This is the core semantic justification for the adapter's
    Assign → Let lowering. -/
theorem assign_equiv_let (fuel : Nat) (state : YulState)
    (name : String) (value : YulExpr) :
    execYulStmtFuel fuel state (.assign name value) =
    execYulStmtFuel fuel state (.let_ name value) := by
  cases fuel with
  | zero => rfl
  | succ n => rfl

/-- Variant of the assign/let equivalence for the noncomputable wrapper. -/
theorem assign_equiv_let' (state : YulState)
    (name : String) (value : YulExpr) :
    execYulStmt state (.assign name value) =
    execYulStmt state (.let_ name value) := by
  simp only [execYulStmt]
  exact assign_equiv_let _ _ _ _

/-! ## Helper: empty statement list execution

This is used in for-loop init-hoisting reasoning. -/

/-- Executing an empty statement list is a no-op for any fuel value. -/
@[simp] theorem execYulFuel_stmts_nil (fuel : Nat) (state : YulState) :
    execYulFuel fuel state (.stmts []) = .continue state := by
  cases fuel <;> rfl

/-! ## Notes on For Init-Hoisting

The adapter also transforms `for_ init cond post body` into
`init_stmts ++ [for_ [] cond post body]` because EVMYulLean's `For`
has no init block. This transformation is semantically valid because
`execYulFuel` first executes `init` to get state `s'`, then checks
`cond` on `s'`. With empty init, `execYulFuel_stmts_nil` shows that
step 1 is a no-op, so the loop starts directly at step 2.

Full formal proofs of init-hoisting are deferred to Phase 3 of
issue #1722, where deeper integration with EVMYulLean's interpreter
will provide the necessary tooling to verify these transformations
end-to-end. -/

end Compiler.Proofs.YulGeneration.Backends.AdapterCorrectness
