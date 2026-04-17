/-
  Source-expression closure under `BridgedExpr`.

  This module proves that the Verity compiler's `compileExpr` emits a
  `BridgedExpr` for the pure arithmetic / comparison / bit-operation
  fragment of the EDSL:
    - scalar leaves: `literal`, `param`, `constructorArg`, `localVar`
    - pure binops whose Yul output is `yulBinOp NAME (← a) (← b)` with
      `NAME ∈ bridgedBuiltins`: `add`, `sub`, `mul`, `div`, `sdiv`,
      `mod`, `smod`, `bitAnd`, `bitOr`, `bitXor`, `shl`, `shr`, `sar`,
      `signextend`, `eq`, `gt`, `sgt`, `lt`, `slt`
    - negated comparisons via `yulNegatedBinOp`: `ge`, `le`

  Storage, mapping, calldata, call, keccak256, dynamic helpers,
  `bitNot`/`logicalAnd`/`logicalOr`/`logicalNot`/`min`/`max`/`ceilDiv`/
  `mulDivDown`/`mulDivUp`/`wMulDown`/`wDivUp`/`ite`/ABI casts are out
  of scope and require dedicated closure proofs.

  The scalar-leaf-only theorem `compileExpr_bridgedSource_leaf` is
  retained below as a specialization.

  Downstream `compileStmt` body-closure proofs compose this closure with
  per-constructor expression-subterm lifts.

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
    `BridgedExpr`. Covers `literal`, `param`, `constructorArg`, `localVar`. -/
inductive BridgedSourceExprLeaf : Expr → Prop
  | literal (n : Nat) : BridgedSourceExprLeaf (.literal n)
  | param (name : String) : BridgedSourceExprLeaf (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExprLeaf (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExprLeaf (.localVar name)

/-- Scalar-leaf closure: every `BridgedSourceExprLeaf` compiles to a
    `BridgedExpr`. -/
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

/-- Source EDSL expressions whose `compileExpr` output is a `BridgedExpr`.
    Covers scalar leaves plus pure arithmetic/comparison/bit-op binops
    that emit `yulBinOp NAME` for `NAME ∈ bridgedBuiltins`, plus `ge`/`le`
    which emit `yulNegatedBinOp`. Storage, calldata, dynamic helpers, and
    compound forms (bitNot/logicalAnd/logicalOr/logicalNot/min/max/
    ceilDiv/mulDiv*/wMul*/wDiv*/ite) are out of scope. -/
inductive BridgedSourceExpr : Expr → Prop
  -- scalar leaves
  | literal (n : Nat) : BridgedSourceExpr (.literal n)
  | param (name : String) : BridgedSourceExpr (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExpr (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExpr (.localVar name)
  -- arithmetic binops (yulBinOp with bridged name)
  | add {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.add a b)
  | sub {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sub a b)
  | mul {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.mul a b)
  | div {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.div a b)
  | sdiv {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sdiv a b)
  | mod {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.mod a b)
  | smod {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.smod a b)
  -- bit operation binops
  | bitAnd {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitAnd a b)
  | bitOr {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitOr a b)
  | bitXor {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitXor a b)
  -- shift binops
  | shl {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.shl s v)
  | shr {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.shr s v)
  | sar {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.sar s v)
  | signextend {b v} (hb : BridgedSourceExpr b) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.signextend b v)
  -- direct comparison binops
  | eq {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.eq a b)
  | gt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.gt a b)
  | sgt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sgt a b)
  | lt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.lt a b)
  | slt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.slt a b)
  -- negated comparisons (yulNegatedBinOp)
  | ge {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.ge a b)
  | le {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.le a b)

/-- A `YulExpr.call` whose name is in `bridgedBuiltins` and whose two
    arguments are already `BridgedExpr` is itself a `BridgedExpr`. -/
private theorem bridgedExpr_binopBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (YulExpr.call func [a, b]) := by
  refine BridgedExpr.call func [a, b] (Or.inl hBridged) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact ha
  · exact hb

/-- A `YulExpr.call` whose name is in `bridgedBuiltins` and whose single
    argument is already a `BridgedExpr` is itself a `BridgedExpr`. -/
private theorem bridgedExpr_unopBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a : YulExpr}
    (ha : BridgedExpr a) :
    BridgedExpr (YulExpr.call func [a]) := by
  refine BridgedExpr.call func [a] (Or.inl hBridged) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact ha

/-- `yulBinOp op a b` is bridged when `op ∈ bridgedBuiltins` and both
    arguments are bridged. -/
private theorem bridgedExpr_yulBinOp {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (yulBinOp func a b) := by
  unfold yulBinOp
  exact bridgedExpr_binopBuiltin hBridged ha hb

/-- `yulNegatedBinOp op a b = iszero(call op [a, b])` is bridged when
    `op ∈ bridgedBuiltins` and both arguments are bridged. -/
private theorem bridgedExpr_yulNegatedBinOp {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (yulNegatedBinOp func a b) := by
  unfold yulNegatedBinOp
  exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin hBridged ha hb)

/-- Destructure a `do`-block emission of `yulBinOp` into its sub-results.
    This shape matches what `simp only [compileExpr]` produces for every
    binop constructor case. -/
private lemma compileExpr_yulBinOp_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {op : String} {a b : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (yulBinOp op x y) : Except String YulExpr) = .ok out) :
    ∃ ca cb, compileExpr fields src a = .ok ca
           ∧ compileExpr fields src b = .ok cb
           ∧ out = yulBinOp op ca cb := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          refine ⟨ca, cb, rfl, rfl, ?_⟩
          simp [hA, hB, bind, Except.bind, Pure.pure, Except.pure] at hOk
          exact hOk.symm

/-- Same destructuring for `yulNegatedBinOp` emissions (used by `ge`/`le`). -/
private lemma compileExpr_yulNegatedBinOp_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {op : String} {a b : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (yulNegatedBinOp op x y) : Except String YulExpr) = .ok out) :
    ∃ ca cb, compileExpr fields src a = .ok ca
           ∧ compileExpr fields src b = .ok cb
           ∧ out = yulNegatedBinOp op ca cb := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          refine ⟨ca, cb, rfl, rfl, ?_⟩
          simp [hA, hB, bind, Except.bind, Pure.pure, Except.pure] at hOk
          exact hOk.symm

/-- Main theorem: every `BridgedSourceExpr` compiles to a `BridgedExpr`.
    Structural induction on the source predicate. Binop cases delegate
    to `compileExpr_yulBinOp_ok` / `compileExpr_yulNegatedBinOp_ok` to
    destructure the emitted do-block, then wrap via `bridgedExpr_yulBinOp`
    / `bridgedExpr_yulNegatedBinOp`. -/
theorem compileExpr_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {e : Expr}, BridgedSourceExpr e →
      ∀ {out : YulExpr}, compileExpr fields src e = .ok out → BridgedExpr out := by
  intro e hE
  induction hE with
  | literal n =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out; exact BridgedExpr.lit _
  | param name =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out; exact BridgedExpr.ident name
  | constructorArg idx =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out; exact BridgedExpr.ident _
  | localVar name =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out; exact BridgedExpr.ident name
  | add _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | sub _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | mul _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | div _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | sdiv _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | mod _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | smod _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | bitAnd _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | bitOr _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | bitXor _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | shl _ _ ihs ihv =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (ihs hA) (ihv hB)
  | shr _ _ ihs ihv =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (ihs hA) (ihv hB)
  | sar _ _ ihs ihv =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (ihs hA) (ihv hB)
  | signextend _ _ ihb ihv =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (ihb hA) (ihv hB)
  | eq _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | gt _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | sgt _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | lt _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | slt _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | ge _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulNegatedBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulNegatedBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)
  | le _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulNegatedBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulNegatedBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)

end Compiler.Proofs.YulGeneration.Backends
