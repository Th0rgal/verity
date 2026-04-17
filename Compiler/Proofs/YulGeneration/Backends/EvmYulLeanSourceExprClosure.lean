/-
  Source-expression closure under `BridgedExpr` — scalar leaves.

  This module proves that the Verity compiler's `compileExpr` emits a
  `BridgedExpr` for the four scalar leaf expressions of the EDSL:
  `literal`, `param`, `constructorArg`, and `localVar`. These lower to
  `YulExpr.lit` / `YulExpr.ident` respectively and therefore satisfy
  `BridgedExpr` trivially via the `lit`/`ident` constructors.

  This is the first increment of source-expression closure. Subsequent
  increments will extend coverage to pure arithmetic, comparison, logical,
  and ternary constructors. Those extensions require `yulBinOp` and
  `yulNegatedBinOp` (currently `private def` in `ExpressionCompile.lean`)
  to be made visible to proof modules; this file intentionally stays within
  the public surface of `compileExpr` to keep the first increment landable.

  Storage, mapping, calldata, call, keccak256, and dynamic helpers are
  out of scope and will require dedicated closure proofs.

  Downstream `compileStmt` body-closure proofs will compose this closure
  with per-constructor expression-subterm lifts.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSourceExprClosure
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.YulGeneration

/-- Scalar leaf expressions of the EDSL whose `compileExpr` output is a
    `BridgedExpr`. Covers `literal`, `param`, `constructorArg`, `localVar`.

    Future increments will add arithmetic, logical, comparison, and
    ternary constructors. -/
inductive BridgedSourceExprLeaf : Expr → Prop
  | literal (n : Nat) : BridgedSourceExprLeaf (.literal n)
  | param (name : String) : BridgedSourceExprLeaf (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExprLeaf (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExprLeaf (.localVar name)

/-- Scalar-leaf closure: every `BridgedSourceExprLeaf` compiles to a
    `BridgedExpr`. The four leaf shapes lower to `YulExpr.lit` or
    `YulExpr.ident`, matching the corresponding `BridgedExpr` constructors
    directly. -/
theorem compileExpr_bridgedSource_leaf
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {e : Expr}, BridgedSourceExprLeaf e →
      ∀ {out : YulExpr}, compileExpr fields src e = .ok out → BridgedExpr out := by
  intro e hE out hOk
  cases hE with
  | literal n =>
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.lit _
  | param name =>
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident name
  | constructorArg idx =>
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident _
  | localVar name =>
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident name

end Compiler.Proofs.YulGeneration.Backends
