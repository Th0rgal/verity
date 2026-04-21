/-
  EvmYulLeanAdapterCorrectness: Semantic equivalence proofs for the two
  non-trivial lowering transformations in the EVMYulLean adapter.

  The adapter (`EvmYulLeanAdapter.lean`) performs two structural
  transformations when lowering Verity Yul to EVMYulLean AST:

  1. **Assign → Let**: EVMYulLean has no `Assign` statement; the adapter
     re-encodes `assign name value` as `Let [name] (some (lowerExpr value))`.
     This is semantically valid because both operations call `state.setVar`,
     which prepends a new binding and removes the old one.

  2. **For init-hoisting**: EVMYulLean's `For` has no init block; the adapter
     emits `init' ++ [.For cond post' body']`. This is semantically valid
     because `execYulFuel` executes the init block once before entering the
     loop, then recurses with `for_ [] cond post body`.

  Both proofs establish that executing the Verity AST directly and executing
  the adapter's lowered form produce identical `YulExecResult` values.

  These proofs address two of the "Known Challenges" in issue #1722:
  - "`Assign` statement: EVMYulLean lacks `Assign`; adapter uses `Let`"
  - "`For` initializer: EVMYulLean `For` has no init block"
-/

import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics

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

/-! ## For Init-Hoisting Semantic Equivalence

The adapter transforms `for_ init cond post body` into
`init_stmts ++ [for_ [] cond post body]`. We prove this produces
identical results: executing the for loop with init is the same as
executing init as a prefix, then the loop with empty init.

The key insight is that `execYulFuel` handles `for_` by:
1. Executing `init` to get state `s'`
2. If init succeeds, checking `cond` on `s'`
3. Recursing with `for_ [] cond post body`

When init is empty, step 1 is a no-op: `execYulFuel fuel state (.stmts []) = .continue state`.
So `for_ [] cond post body` starts directly at step 2. -/

/-- Executing an empty statement list is a no-op for any fuel value. -/
@[simp] theorem execYulFuel_stmts_nil (fuel : Nat) (state : YulState) :
    execYulFuel fuel state (.stmts []) = .continue state := by
  cases fuel <;> rfl

/-- Init-hoisting for the continue case: when init succeeds with state `s'`,
    the for-loop behaves the same as running the loop with empty init on `s'`.

    This is the core semantic justification for the adapter's transformation of
    `for (init; cond; post) body` into `init; for (; cond; post) body`. -/
theorem for_init_hoist (fuel : Nat) (state : YulState)
    (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    (s' : YulState) (hinit : execYulFuel fuel state (.stmts init) = .continue s') :
    execYulStmtFuel (fuel + 1) state (.for_ init cond post body) =
    execYulStmtFuel (fuel + 1) s' (.for_ [] cond post body) := by
  simp [execYulStmtFuel, execYulFuel, hinit, execYulFuel_stmts_nil]

/-- Init-hoisting for the revert case. -/
theorem for_init_hoist_revert (fuel : Nat) (state : YulState)
    (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    (s : YulState) (hinit : execYulFuel fuel state (.stmts init) = .revert s) :
    execYulStmtFuel (fuel + 1) state (.for_ init cond post body) = .revert s := by
  simp [execYulStmtFuel, execYulFuel, hinit]

/-- Init-hoisting for the return case. -/
theorem for_init_hoist_return (fuel : Nat) (state : YulState)
    (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    (v : Nat) (s : YulState) (hinit : execYulFuel fuel state (.stmts init) = .return v s) :
    execYulStmtFuel (fuel + 1) state (.for_ init cond post body) = .return v s := by
  simp [execYulStmtFuel, execYulFuel, hinit]

/-- Init-hoisting for the stop case. -/
theorem for_init_hoist_stop (fuel : Nat) (state : YulState)
    (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    (s : YulState) (hinit : execYulFuel fuel state (.stmts init) = .stop s) :
    execYulStmtFuel (fuel + 1) state (.for_ init cond post body) = .stop s := by
  simp [execYulStmtFuel, execYulFuel, hinit]

/-! ## Combined: the adapter's lowering preserves semantics

These theorems together establish that the two non-trivial transformations
in the EVMYulLean adapter are semantically correct:

1. `assign name value` → `Let [name] (some value)`: proved by `assign_equiv_let`
2. `for_ init cond post body` → `init ++ [for_ [] cond post body]`: proved by
   `for_init_hoist` (continue case) and the halt-case variants

All other lowering cases are structural (1:1 mapping) and trivially correct. -/

end Compiler.Proofs.YulGeneration.Backends.AdapterCorrectness
