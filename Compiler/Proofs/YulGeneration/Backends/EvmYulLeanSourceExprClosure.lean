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
    - boolean-normalized operations: `logicalAnd`, `logicalOr`, `logicalNot`
    - branchless arithmetic helpers: `ceilDiv`, `mulDivDown`, `mulDivUp`,
      `wMulDown`, `wDivUp`, `min`, `max`, `ite`
    - zero-argument environment/calldata-size reads whose emitted Yul calls
      are already bridged: `caller`, `contractAddress`, `msgValue`,
      `blockTimestamp`, `blockNumber`, `chainid`, `blobbasefee`,
      `calldatasize`
    - unary calldata/memory/transient reads: `calldataload`, `mload`, `tload`

  Storage, mapping, returndata, call, keccak256, dynamic helpers, ABI casts,
  `selfBalance`, and external account/state reads are out of scope and require
  dedicated closure proofs.

  The scalar-leaf-only theorem `compileExpr_bridgedSource_leaf` is
  retained below as a specialization.

  Downstream `compileStmt` body-closure proofs compose this closure with
  per-constructor expression-subterm lifts.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSourceExprClosure
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.IRGeneration.ExprCore
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
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
    Covers scalar leaves, pure arithmetic/comparison/bit-op binops,
    boolean-normalization forms, branchless arithmetic helpers,
    zero-argument environment/calldata-size reads, unary calldata/memory/
    transient reads, and `ge`/`le` negated comparisons. Storage, mapping,
    returndata, dynamic helpers, ABI casts, calls, `selfBalance`, and external
    account/state reads are out of scope. -/
inductive BridgedSourceExpr : Expr → Prop
  -- scalar leaves
  | literal (n : Nat) : BridgedSourceExpr (.literal n)
  | param (name : String) : BridgedSourceExpr (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExpr (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExpr (.localVar name)
  -- zero-argument environment / calldata-size reads
  | caller : BridgedSourceExpr .caller
  | contractAddress : BridgedSourceExpr .contractAddress
  | msgValue : BridgedSourceExpr .msgValue
  | blockTimestamp : BridgedSourceExpr .blockTimestamp
  | blockNumber : BridgedSourceExpr .blockNumber
  | chainid : BridgedSourceExpr .chainid
  | blobbasefee : BridgedSourceExpr .blobbasefee
  | calldatasize : BridgedSourceExpr .calldatasize
  -- unary calldata / memory / transient reads
  | calldataload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.calldataload offset)
  | mload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.mload offset)
  | tload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.tload offset)
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
  | bitNot {a} (ha : BridgedSourceExpr a) :
      BridgedSourceExpr (.bitNot a)
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
  -- boolean normalization
  | logicalAnd {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.logicalAnd a b)
  | logicalOr {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.logicalOr a b)
  | logicalNot {a} (ha : BridgedSourceExpr a) :
      BridgedSourceExpr (.logicalNot a)
  -- branchless arithmetic helpers
  | ceilDiv {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.ceilDiv a b)
  | mulDivDown {a b c}
      (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b)
      (hc : BridgedSourceExpr c) :
      BridgedSourceExpr (.mulDivDown a b c)
  | mulDivUp {a b c}
      (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b)
      (hc : BridgedSourceExpr c) :
      BridgedSourceExpr (.mulDivUp a b c)
  | wMulDown {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.wMulDown a b)
  | wDivUp {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.wDivUp a b)
  | min {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.min a b)
  | max {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.max a b)
  | ite {cond thenVal elseVal}
      (hCond : BridgedSourceExpr cond) (hThen : BridgedSourceExpr thenVal)
      (hElse : BridgedSourceExpr elseVal) :
      BridgedSourceExpr (.ite cond thenVal elseVal)
  -- negated comparisons (yulNegatedBinOp)
  | ge {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.ge a b)
  | le {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.le a b)

/-- The public IR compile-core expression grammar is contained in the native
    source-expression bridge. This turns `SupportedFragment` expression
    witnesses into the `BridgedSourceExpr` premises consumed by body-closure
    proofs. -/
theorem bridgedSourceExpr_of_exprCompileCore :
    ∀ {e : Expr}, FunctionBody.ExprCompileCore e → BridgedSourceExpr e := by
  intro e hCore
  induction hCore <;> constructor <;> assumption

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

/-- A zero-argument `YulExpr.call` whose name is in `bridgedBuiltins` is a
    `BridgedExpr`. -/
private theorem bridgedExpr_nullaryBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) :
    BridgedExpr (YulExpr.call func []) := by
  refine BridgedExpr.call func [] (Or.inl hBridged) ?_
  intro arg hMem
  cases hMem

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

/-- `yulToBool e = iszero(iszero(e))` is bridged when `e` is bridged. -/
private theorem bridgedExpr_yulToBool {e : YulExpr} (hE : BridgedExpr e) :
    BridgedExpr (yulToBool e) := by
  unfold yulToBool
  exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) hE)

private theorem bridgedExpr_ceilDiv {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [a]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b],
          YulExpr.lit 1
        ]
      ]) := by
  have hBool : BridgedExpr (YulExpr.call "iszero" [YulExpr.call "iszero" [a]]) :=
    bridgedExpr_yulToBool ha
  have hSub : BridgedExpr (YulExpr.call "sub" [a, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha (BridgedExpr.lit 1)
  have hDiv : BridgedExpr (YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hb
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b],
          YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hDiv (BridgedExpr.lit 1)
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBool hAdd

private theorem bridgedExpr_mulDivDown {a b c : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) (hc : BridgedExpr c) :
    BridgedExpr (YulExpr.call "div" [YulExpr.call "mul" [a, b], c]) := by
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb) hc

private theorem bridgedExpr_mulDivUp {a b c : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) (hc : BridgedExpr c) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [a, b],
          YulExpr.call "sub" [c, YulExpr.lit 1]
        ],
        c
      ]) := by
  have hMul : BridgedExpr (YulExpr.call "mul" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hSub : BridgedExpr (YulExpr.call "sub" [c, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hc (BridgedExpr.lit 1)
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "mul" [a, b],
          YulExpr.call "sub" [c, YulExpr.lit 1]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hMul hSub
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hAdd hc

private theorem bridgedExpr_wMulDown {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "mul" [a, b],
        YulExpr.lit 1000000000000000000]) := by
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb)
    (BridgedExpr.lit 1000000000000000000)

private theorem bridgedExpr_wDivUp {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [b, YulExpr.lit 1]
        ],
        b
      ]) := by
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha
      (BridgedExpr.lit 1000000000000000000)
  have hSub : BridgedExpr (YulExpr.call "sub" [b, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb (BridgedExpr.lit 1)
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [b, YulExpr.lit 1]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hMul hSub
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hAdd hb

private theorem bridgedExpr_min {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "sub" [a,
        YulExpr.call "mul" [
          YulExpr.call "sub" [a, b],
          YulExpr.call "gt" [a, b]
        ]
      ]) := by
  have hSub : BridgedExpr (YulExpr.call "sub" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hGt : BridgedExpr (YulExpr.call "gt" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [YulExpr.call "sub" [a, b], YulExpr.call "gt" [a, b]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hGt
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hMul

private theorem bridgedExpr_max {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "add" [a,
        YulExpr.call "mul" [
          YulExpr.call "sub" [b, a],
          YulExpr.call "gt" [b, a]
        ]
      ]) := by
  have hSub : BridgedExpr (YulExpr.call "sub" [b, a]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb ha
  have hGt : BridgedExpr (YulExpr.call "gt" [b, a]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb ha
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [YulExpr.call "sub" [b, a], YulExpr.call "gt" [b, a]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hGt
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hMul

private theorem bridgedExpr_ite {cond thenVal elseVal : YulExpr}
    (hCond : BridgedExpr cond) (hThen : BridgedExpr thenVal)
    (hElse : BridgedExpr elseVal) :
    BridgedExpr
      (YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [cond]], thenVal],
        YulExpr.call "mul" [YulExpr.call "iszero" [cond], elseVal]
      ]) := by
  have hBool : BridgedExpr (YulExpr.call "iszero" [YulExpr.call "iszero" [cond]]) :=
    bridgedExpr_yulToBool hCond
  have hNeg : BridgedExpr (YulExpr.call "iszero" [cond]) :=
    bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) hCond
  have hThenTerm :
      BridgedExpr
        (YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [cond]], thenVal]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBool hThen
  have hElseTerm :
      BridgedExpr (YulExpr.call "mul" [YulExpr.call "iszero" [cond], elseVal]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hNeg hElse
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hThenTerm hElseTerm

/-- Destructure a `do`-block emission of `yulBinOp` into its sub-results.
    This shape matches what `simp only [compileExpr]` produces for every
    binop constructor case. -/
private theorem compileExpr_yulBinOp_ok
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
private theorem compileExpr_yulNegatedBinOp_ok
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

/-- Destructure a boolean-normalized binary expression emission. -/
private theorem compileExpr_yulBoolBinOp_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {op : String} {a b : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (yulBinOp op (yulToBool x) (yulToBool y)) :
        Except String YulExpr) = .ok out) :
    ∃ ca cb, compileExpr fields src a = .ok ca
           ∧ compileExpr fields src b = .ok cb
           ∧ out = yulBinOp op (yulToBool ca) (yulToBool cb) := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          refine ⟨ca, cb, rfl, rfl, ?_⟩
          simp [hA, hB, bind, Except.bind, Pure.pure, Except.pure] at hOk
          exact hOk.symm

/-- Destructure a unary builtin expression emission. -/
private theorem compileExpr_unopBuiltin_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {op : String} {a : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               pure (YulExpr.call op [x]) : Except String YulExpr) = .ok out) :
    ∃ ca, compileExpr fields src a = .ok ca ∧ out = YulExpr.call op [ca] := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      refine ⟨ca, rfl, ?_⟩
      simp [hA, bind, Except.bind, Pure.pure, Except.pure] at hOk
      exact hOk.symm

/-- Destructure a binary helper expression emission. -/
private theorem compileExpr_binaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr} {a b : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (shape x y) : Except String YulExpr) = .ok out) :
    ∃ ca cb, compileExpr fields src a = .ok ca
           ∧ compileExpr fields src b = .ok cb
           ∧ out = shape ca cb := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          refine ⟨ca, cb, rfl, rfl, ?_⟩
          simp [hA, hB, bind, Except.bind, Pure.pure, Except.pure] at hOk
          exact hOk.symm

/-- Destructure a ternary helper expression emission. -/
private theorem compileExpr_ternaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr → YulExpr}
    {a b c : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               let z ← compileExpr fields src c
               pure (shape x y z) : Except String YulExpr) = .ok out) :
    ∃ ca cb cc, compileExpr fields src a = .ok ca
              ∧ compileExpr fields src b = .ok cb
              ∧ compileExpr fields src c = .ok cc
              ∧ out = shape ca cb cc := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          cases hC : compileExpr fields src c with
          | error e => simp [hA, hB, hC, bind, Except.bind] at hOk
          | ok cc =>
              refine ⟨ca, cb, cc, rfl, rfl, rfl, ?_⟩
              simp [hA, hB, hC, bind, Except.bind, Pure.pure, Except.pure] at hOk
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
  | caller =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | contractAddress =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | msgValue =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | blockTimestamp =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | blockNumber =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | chainid =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | blobbasefee =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | calldatasize =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  | calldataload _ iho =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨co, hO, hEq⟩ := compileExpr_unopBuiltin_ok hOk
      subst hEq
      exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) (iho hO)
  | mload _ iho =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨co, hO, hEq⟩ := compileExpr_unopBuiltin_ok hOk
      subst hEq
      exact bridgedExpr_mload co (iho hO)
  | tload _ iho =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨co, hO, hEq⟩ := compileExpr_unopBuiltin_ok hOk
      subst hEq
      exact bridgedExpr_tload co (iho hO)
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
  | bitNot _ iha =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, hA, hEq⟩ := compileExpr_unopBuiltin_ok hOk
      subst hEq
      exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) (iha hA)
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
  | logicalAnd _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBoolBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
        (bridgedExpr_yulToBool (iha hA)) (bridgedExpr_yulToBool (ihb hB))
  | logicalOr _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBoolBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
        (bridgedExpr_yulToBool (iha hA)) (bridgedExpr_yulToBool (ihb hB))
  | logicalNot _ iha =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, hA, hEq⟩ := compileExpr_unopBuiltin_ok hOk
      subst hEq
      exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) (iha hA)
  | ceilDiv _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_ceilDiv (iha hA) (ihb hB)
  | mulDivDown _ _ _ iha ihb ihc =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, cc, hA, hB, hC, hEq⟩ := compileExpr_ternaryShape_ok hOk
      subst hEq
      exact bridgedExpr_mulDivDown (iha hA) (ihb hB) (ihc hC)
  | mulDivUp _ _ _ iha ihb ihc =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, cc, hA, hB, hC, hEq⟩ := compileExpr_ternaryShape_ok hOk
      subst hEq
      exact bridgedExpr_mulDivUp (iha hA) (ihb hB) (ihc hC)
  | wMulDown _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_wMulDown (iha hA) (ihb hB)
  | wDivUp _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_wDivUp (iha hA) (ihb hB)
  | min _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_min (iha hA) (ihb hB)
  | max _ _ iha ihb =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_max (iha hA) (ihb hB)
  | ite _ _ _ ihc iht ihe =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨cc, ct, ce, hC, hT, hE, hEq⟩ := compileExpr_ternaryShape_ok hOk
      subst hEq
      exact bridgedExpr_ite (ihc hC) (iht hT) (ihe hE)
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

/-- Default `require` failure condition shape: `iszero(compileExpr cond)` is
    bridged whenever the source condition expression is bridged. -/
private theorem compileRequireFailCond_default_bridgedSource
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {cond : Expr} {failCond : YulExpr}
    (hCond : BridgedSourceExpr cond)
    (hOk :
      (do
        let compiled ← compileExpr fields src cond
        pure (YulExpr.call "iszero" [compiled]) : Except String YulExpr) = .ok failCond) :
    BridgedExpr failCond := by
  cases hCompiled : compileExpr fields src cond with
  | error err =>
      rw [hCompiled] at hOk
      cases hOk
  | ok compiled =>
      rw [hCompiled] at hOk
      cases hOk
      exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
        (compileExpr_bridgedSource fields src hCond hCompiled)

/-- `compileRequireFailCond` emits a `BridgedExpr` for every pure bridged source
    condition. The `ge`/`le` cases use the compiler's direct negation
    optimization (`lt`/`gt`); all other conditions compile as `iszero(cond)`. -/
theorem compileRequireFailCond_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {cond : Expr}, BridgedSourceExpr cond →
      ∀ {failCond : YulExpr},
        compileRequireFailCond fields src cond = .ok failCond → BridgedExpr failCond := by
  intro cond hCond failCond hOk
  cases hCond with
  | ge ha hb =>
      simp only [compileRequireFailCond] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
        (compileExpr_bridgedSource fields src ha hA)
        (compileExpr_bridgedSource fields src hb hB)
  | le ha hb =>
      simp only [compileRequireFailCond] at hOk
      obtain ⟨ca, cb, hA, hB, hEq⟩ := compileExpr_yulBinOp_ok hOk
      subst hEq
      exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
        (compileExpr_bridgedSource fields src ha hA)
        (compileExpr_bridgedSource fields src hb hB)
  | literal n =>
      exact compileRequireFailCond_default_bridgedSource (.literal n)
        (by simpa [compileRequireFailCond] using hOk)
  | param name =>
      exact compileRequireFailCond_default_bridgedSource (.param name)
        (by simpa [compileRequireFailCond] using hOk)
  | constructorArg idx =>
      exact compileRequireFailCond_default_bridgedSource (.constructorArg idx)
        (by simpa [compileRequireFailCond] using hOk)
  | localVar name =>
      exact compileRequireFailCond_default_bridgedSource (.localVar name)
        (by simpa [compileRequireFailCond] using hOk)
  | caller =>
      exact compileRequireFailCond_default_bridgedSource .caller
        (by simpa [compileRequireFailCond] using hOk)
  | contractAddress =>
      exact compileRequireFailCond_default_bridgedSource .contractAddress
        (by simpa [compileRequireFailCond] using hOk)
  | msgValue =>
      exact compileRequireFailCond_default_bridgedSource .msgValue
        (by simpa [compileRequireFailCond] using hOk)
  | blockTimestamp =>
      exact compileRequireFailCond_default_bridgedSource .blockTimestamp
        (by simpa [compileRequireFailCond] using hOk)
  | blockNumber =>
      exact compileRequireFailCond_default_bridgedSource .blockNumber
        (by simpa [compileRequireFailCond] using hOk)
  | chainid =>
      exact compileRequireFailCond_default_bridgedSource .chainid
        (by simpa [compileRequireFailCond] using hOk)
  | blobbasefee =>
      exact compileRequireFailCond_default_bridgedSource .blobbasefee
        (by simpa [compileRequireFailCond] using hOk)
  | calldatasize =>
      exact compileRequireFailCond_default_bridgedSource .calldatasize
        (by simpa [compileRequireFailCond] using hOk)
  | calldataload hOffset =>
      exact compileRequireFailCond_default_bridgedSource (.calldataload hOffset)
        (by simpa [compileRequireFailCond] using hOk)
  | mload hOffset =>
      exact compileRequireFailCond_default_bridgedSource (.mload hOffset)
        (by simpa [compileRequireFailCond] using hOk)
  | tload hOffset =>
      exact compileRequireFailCond_default_bridgedSource (.tload hOffset)
        (by simpa [compileRequireFailCond] using hOk)
  | add ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.add ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | sub ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.sub ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | mul ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.mul ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | div ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.div ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | sdiv ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.sdiv ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | mod ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.mod ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | smod ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.smod ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | bitAnd ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.bitAnd ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | bitOr ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.bitOr ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | bitXor ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.bitXor ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | bitNot ha =>
      exact compileRequireFailCond_default_bridgedSource (.bitNot ha)
        (by simpa [compileRequireFailCond] using hOk)
  | shl hs hv =>
      exact compileRequireFailCond_default_bridgedSource (.shl hs hv)
        (by simpa [compileRequireFailCond] using hOk)
  | shr hs hv =>
      exact compileRequireFailCond_default_bridgedSource (.shr hs hv)
        (by simpa [compileRequireFailCond] using hOk)
  | sar hs hv =>
      exact compileRequireFailCond_default_bridgedSource (.sar hs hv)
        (by simpa [compileRequireFailCond] using hOk)
  | signextend hb hv =>
      exact compileRequireFailCond_default_bridgedSource (.signextend hb hv)
        (by simpa [compileRequireFailCond] using hOk)
  | eq ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.eq ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | gt ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.gt ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | sgt ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.sgt ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | lt ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.lt ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | slt ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.slt ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | logicalAnd ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.logicalAnd ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | logicalOr ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.logicalOr ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | logicalNot ha =>
      exact compileRequireFailCond_default_bridgedSource (.logicalNot ha)
        (by simpa [compileRequireFailCond] using hOk)
  | ceilDiv ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.ceilDiv ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | mulDivDown ha hb hc =>
      exact compileRequireFailCond_default_bridgedSource (.mulDivDown ha hb hc)
        (by simpa [compileRequireFailCond] using hOk)
  | mulDivUp ha hb hc =>
      exact compileRequireFailCond_default_bridgedSource (.mulDivUp ha hb hc)
        (by simpa [compileRequireFailCond] using hOk)
  | wMulDown ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.wMulDown ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | wDivUp ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.wDivUp ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | min ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.min ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | max ha hb =>
      exact compileRequireFailCond_default_bridgedSource (.max ha hb)
        (by simpa [compileRequireFailCond] using hOk)
  | ite hCond hThen hElse =>
      exact compileRequireFailCond_default_bridgedSource (.ite hCond hThen hElse)
        (by simpa [compileRequireFailCond] using hOk)

/-- List-level closure: when every source expression in a list is
    `BridgedSourceExpr`, `compileExprList` produces a list whose every
    element is a `BridgedExpr`.

    Used by body-closure lemmas for statement constructors that carry a
    list of source expressions (e.g., `rawLog`, `emit`, `setMapping`
    multi-slot, `setStructMember`, `returnValues`, `ecm` args). -/
theorem compileExprList_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {exprs : List Expr}, (∀ e ∈ exprs, BridgedSourceExpr e) →
      ∀ {out : List YulExpr},
        compileExprList fields src exprs = .ok out →
        ∀ yulExpr ∈ out, BridgedExpr yulExpr := by
  intro exprs
  induction exprs with
  | nil =>
      intro _ out hOk
      simp [compileExprList, Pure.pure, Except.pure] at hOk
      subst out
      intro yulExpr hMem
      cases hMem
  | cons e es ih =>
      intro hAll out hOk
      simp only [compileExprList, bind, Except.bind] at hOk
      cases hHead : compileExpr fields src e with
      | error err =>
          simp [hHead] at hOk
      | ok headExpr =>
          simp [hHead] at hOk
          cases hTail : compileExprList fields src es with
          | error err =>
              simp [hTail] at hOk
          | ok tailExprs =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceExpr e := hAll e (by simp)
              have hHeadBridged : BridgedExpr headExpr :=
                compileExpr_bridgedSource fields src hHeadSource hHead
              have hTailAll : ∀ e' ∈ es, BridgedSourceExpr e' := by
                intro e' hMem
                exact hAll e' (by simp [hMem])
              have hTailBridged : ∀ x ∈ tailExprs, BridgedExpr x :=
                ih hTailAll hTail
              intro yulExpr hMem
              simp only [List.mem_cons] at hMem
              cases hMem with
              | inl h => subst h; exact hHeadBridged
              | inr h => exact hTailBridged yulExpr h

end Compiler.Proofs.YulGeneration.Backends
