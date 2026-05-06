/-
  Source-expression closure under `BridgedExpr`.

  This module proves that the Verity compiler's `compileExpr` emits a
  `BridgedExpr` for the pure arithmetic / comparison / bit-operation
  fragment of the EDSL:
    - scalar/local leaves: `literal`, `param`, `constructorArg`, `localVar`,
      `arrayLength`
    - pure binops whose Yul output is `yulBinOp NAME (← a) (← b)` with
      `NAME ∈ bridgedBuiltins`: `add`, `sub`, `mul`, `div`, `sdiv`,
      `mod`, `smod`, `bitAnd`, `bitOr`, `bitXor`, `shl`, `shr`, `sar`,
      `signextend`, `eq`, `gt`, `sgt`, `lt`, `slt`
    - negated comparisons via `yulNegatedBinOp`: `ge`, `le`
    - boolean-normalized operations: `logicalAnd`, `logicalOr`, `logicalNot`
    - branchless arithmetic helpers: `ceilDiv`, `mulDivDown`, `mulDivUp`,
      `wMulDown`, `wDivUp`, `min`, `max`, `ite`
    - reserved exponentiation builtin surface:
      `externalCall builtinExpName [base, exponent]`
    - zero-argument environment/calldata-size reads whose emitted Yul calls
      are already bridged: `caller`, `contractAddress`, `msgValue`,
      `blockTimestamp`, `blockNumber`, `chainid`, `blobbasefee`,
      `calldatasize`
    - storage reads whose compiler field lookup succeeds: `storage`,
      `storageAddr`, `storageArrayLength`, `adtTag`, `adtField`
    - singleton and nested mapping reads through the abstract `mappingSlot`
      bridge: `mapping`, `mappingWord`, `mappingUint`, `mapping2`,
      `mapping2Word`
    - single-mapping struct-member reads through the same `mappingSlot`
      bridge: `structMember`, `structMember2`
    - unary calldata/memory/transient reads: `calldataload`, `mload`, `tload`
    - native syntactic memory-slice hashing: `keccak256`

  General external/internal calls, packed mapping entries, mapping chains,
  checked dynamic-array elements, storage-array elements, ADT
  construction/matching, returndata, dynamic helpers, ABI casts,
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
    Covers scalar/local leaves, storage reads whose compiler field lookup
    succeeds, including dynamic-array length words and ADT tag/field reads,
    singleton and nested mapping reads through the abstract `mappingSlot`
    bridge,
    mapping struct-member reads,
    pure arithmetic/comparison/bit-op binops, boolean-normalization forms,
    branchless arithmetic helpers, the reserved exponentiation builtin surface,
    zero-argument environment/calldata-size reads, unary calldata/memory/
    transient reads, syntactic memory-slice `keccak256`, and `ge`/`le` negated
    comparisons. General external/internal calls, packed mapping entries,
    mapping chains, checked dynamic-array elements, storage-array elements, ADT
    construction/matching, returndata, dynamic helpers, ABI casts,
    `selfBalance`, and external account/state reads are out of scope. -/
inductive BridgedSourceExpr : Expr → Prop
  -- scalar leaves
  | literal (n : Nat) : BridgedSourceExpr (.literal n)
  | param (name : String) : BridgedSourceExpr (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExpr (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExpr (.localVar name)
  | arrayLength (name : String) : BridgedSourceExpr (.arrayLength name)
  -- storage reads
  | storage (fieldName : String) : BridgedSourceExpr (.storage fieldName)
  | storageAddr (fieldName : String) : BridgedSourceExpr (.storageAddr fieldName)
  | storageArrayLength (fieldName : String) :
      BridgedSourceExpr (.storageArrayLength fieldName)
  | adtTag (adtName storageField : String) :
      BridgedSourceExpr (.adtTag adtName storageField)
  | adtField (adtName variantName fieldName : String) (fieldIndex : Nat)
      (storageField : String) :
      BridgedSourceExpr
        (.adtField adtName variantName fieldName fieldIndex storageField)
  | mapping {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key) :
      BridgedSourceExpr (.mapping fieldName key)
  | mappingWord {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key)
      (wordOffset : Nat) :
      BridgedSourceExpr (.mappingWord fieldName key wordOffset)
  | mappingUint {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key) :
      BridgedSourceExpr (.mappingUint fieldName key)
  | mapping2 {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2) :
      BridgedSourceExpr (.mapping2 fieldName key1 key2)
  | mapping2Word {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (wordOffset : Nat) :
      BridgedSourceExpr (.mapping2Word fieldName key1 key2 wordOffset)
  | structMember {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key)
      (memberName : String) :
      BridgedSourceExpr (.structMember fieldName key memberName)
  | structMember2 {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (memberName : String) :
      BridgedSourceExpr (.structMember2 fieldName key1 key2 memberName)
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
  | keccak256 {offset size}
      (hOffset : BridgedSourceExpr offset) (hSize : BridgedSourceExpr size) :
      BridgedSourceExpr (.keccak256 offset size)
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
  | builtinExp {base exponent}
      (hBase : BridgedSourceExpr base) (hExponent : BridgedSourceExpr exponent) :
      BridgedSourceExpr (.externalCall builtinExpName [base, exponent])
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

/-- A syntactic memory-slice `keccak256` expression is native-bridged when its
    offset and size arguments are in the public compile-core expression
    grammar. This does not add `keccak256` to `ExprCompileCore`: source/IR
    semantic correctness still needs source-side memory-slice hashing. -/
theorem bridgedSourceExpr_keccak256_of_exprCompileCore
    {offset size : Expr}
    (hOffset : FunctionBody.ExprCompileCore offset)
    (hSize : FunctionBody.ExprCompileCore size) :
    BridgedSourceExpr (.keccak256 offset size) :=
  BridgedSourceExpr.keccak256
    (bridgedSourceExpr_of_exprCompileCore hOffset)
    (bridgedSourceExpr_of_exprCompileCore hSize)

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

/-- Literal-slot `sload` is in the native bridged expression fragment. -/
private theorem bridgedExpr_sload_lit (slot : Nat) :
    BridgedExpr (YulExpr.call "sload" [YulExpr.lit slot]) := by
  refine BridgedExpr.call "sload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst arg
  exact BridgedExpr.lit slot

/-- `sload(e)` is in the native bridged expression fragment whenever the slot
    expression is bridged. -/
private theorem bridgedExpr_sload {slot : YulExpr} (hSlot : BridgedExpr slot) :
    BridgedExpr (YulExpr.call "sload" [slot]) := by
  refine BridgedExpr.call "sload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst arg
  exact hSlot

/-- `mappingSlot(base, key)` is in the native bridged expression fragment
    whenever both slot arguments are bridged. -/
private theorem bridgedExpr_mappingSlot {base key : YulExpr}
    (hBase : BridgedExpr base) (hKey : BridgedExpr key) :
    BridgedExpr (YulExpr.call "mappingSlot" [base, key]) :=
  bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBase hKey

/-- `sload(mappingSlot(lit slot, key))` is bridged for bridged keys. -/
private theorem bridgedExpr_sload_mappingSlot_lit
    (slot : Nat) {key : YulExpr} (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key]]) :=
  bridgedExpr_sload
    (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)

/-- `sload(add(mappingSlot(lit slot, key), lit wordOffset))` is bridged for
    bridged keys. -/
private theorem bridgedExpr_sload_mappingSlot_lit_add
    (slot wordOffset : Nat) {key : YulExpr} (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)
      (BridgedExpr.lit wordOffset))

/-- `sload(mappingSlot(mappingSlot(lit slot, key1), key2))` is bridged for
    bridged nested mapping keys. -/
private theorem bridgedExpr_sload_mappingSlot2_lit
    (slot : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]]) :=
  bridgedExpr_sload
    (bridgedExpr_mappingSlot
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
      hKey2)

/-- `sload(add(mappingSlot(mappingSlot(lit slot, key1), key2), lit
    wordOffset))` is bridged for bridged nested mapping keys. -/
private theorem bridgedExpr_sload_mappingSlot2_lit_add
    (slot wordOffset : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot
        (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
        hKey2)
      (BridgedExpr.lit wordOffset))

/-- The compiler's singleton mapping-read helper emits only native-bridged
    Yul when field lookup succeeds and the key expression is bridged.

    The proof intentionally stays at the `mappingSlot` helper boundary; it does
    not claim source-level memory+keccak equivalence for mapping slots. -/
private theorem compileMappingSlotRead_bridged
    {fields : List CompilationModel.Field} {field label : String}
    {keyExpr out : YulExpr} {wordOffset : Nat}
    (hKey : BridgedExpr keyExpr)
    (hOk :
      compileMappingSlotRead fields field keyExpr label wordOffset = .ok out) :
    BridgedExpr out := by
  unfold compileMappingSlotRead at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i slot hFind
      dsimp at hOk
      split at hOk
      · simp [Pure.pure, Except.pure] at hOk
        subst out
        exact bridgedExpr_sload_mappingSlot_lit slot hKey
      · simp [Pure.pure, Except.pure] at hOk
        subst out
        exact bridgedExpr_sload_mappingSlot_lit_add slot wordOffset hKey
    · simp at hOk

/-- ADT tag reads compile to `and(sload(baseSlot), 0xff)`. -/
private theorem bridgedExpr_adtTagRead_lit (baseSlot : Nat) :
    BridgedExpr (compileAdtTagRead (YulExpr.lit baseSlot)) := by
  unfold compileAdtTagRead
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_sload_lit baseSlot) (BridgedExpr.lit 0xFF)

/-- ADT field reads compile to `sload(add(baseSlot, fieldIndex + 1))`. -/
private theorem bridgedExpr_adtFieldRead_lit (baseSlot fieldIndex : Nat) :
    BridgedExpr (compileAdtFieldRead (YulExpr.lit baseSlot) fieldIndex) := by
  unfold compileAdtFieldRead
  exact bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (BridgedExpr.lit baseSlot) (BridgedExpr.lit (fieldIndex + 1)))

/-- Packed storage reads compile to `and(shr(offset, sload(slot)), mask)`,
    whose subexpressions are all native bridged builtins. -/
private theorem bridgedExpr_packed_sload_lit
    (slot offset mask : Nat) :
    BridgedExpr
      (YulExpr.call "and"
        [YulExpr.call "shr" [YulExpr.lit offset,
            YulExpr.call "sload" [YulExpr.lit slot]],
          YulExpr.lit mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact BridgedExpr.lit offset
    · exact bridgedExpr_sload_lit slot
  · exact BridgedExpr.lit mask

/-- Packed reads over an already-bridged slot word compile to
    `and(shr(offset, slotWord), mask)`, whose subexpressions are bridged. -/
private theorem bridgedExpr_packed_read
    {slotWord : YulExpr} (hSlotWord : BridgedExpr slotWord)
    (offset mask : Nat) :
    BridgedExpr
      (YulExpr.call "and"
        [YulExpr.call "shr" [YulExpr.lit offset, slotWord],
          YulExpr.lit mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact BridgedExpr.lit offset
    · exact hSlotWord
  · exact BridgedExpr.lit mask

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
  | arrayLength name =>
      intro out hOk
      simp [compileExpr, Pure.pure, Except.pure] at hOk
      subst out; exact BridgedExpr.ident s!"{name}_length"
  | storage fieldName =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · rename_i f slot hFind
          cases hPacked : f.packedBits with
          | none =>
              simp [hPacked, Pure.pure, Except.pure] at hOk
              subst out
              exact bridgedExpr_sload_lit slot
          | some packed =>
              simp [hPacked, Pure.pure, Except.pure] at hOk
              subst out
              exact bridgedExpr_packed_sload_lit slot packed.offset
                (packedMaskNat packed)
        · simp at hOk
  | storageAddr fieldName =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · rename_i f slot hFind
          cases hTy : f.ty with
          | address =>
              cases hPacked : f.packedBits with
              | none =>
                  simp [hTy, hPacked, Pure.pure, Except.pure] at hOk
                  subst out
                  exact bridgedExpr_sload_lit slot
              | some packed =>
                  simp [hTy, hPacked, Pure.pure, Except.pure] at hOk
                  subst out
                  exact bridgedExpr_packed_sload_lit slot packed.offset
                    (packedMaskNat packed)
          | uint256 | dynamicArray | mappingTyped | mappingStruct
            | mappingStruct2 | adt =>
              simp [hTy] at hOk
        · simp at hOk
  | storageArrayLength fieldName =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · rename_i f slot hFind
        cases hTy : f.ty with
        | dynamicArray elemTy =>
            simp [hTy, Pure.pure, Except.pure] at hOk
            subst out
            exact bridgedExpr_sload_lit slot
        | uint256 | address | mappingTyped | mappingStruct | mappingStruct2 | adt =>
            simp [hTy] at hOk
      · simp at hOk
  | adtTag adtName storageField =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · rename_i baseSlot hFind
        simp [Pure.pure, Except.pure] at hOk
        subst out
        exact bridgedExpr_adtTagRead_lit baseSlot
      · simp at hOk
  | adtField adtName variantName fieldName fieldIndex storageField =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · rename_i baseSlot hFind
        simp [Pure.pure, Except.pure] at hOk
        subst out
        exact bridgedExpr_adtFieldRead_lit baseSlot fieldIndex
      · simp at hOk
  | mapping fieldName hKey ihKey =>
      intro out hOk
      simp only [compileExpr, bind, Except.bind] at hOk
      cases hCompiledKey : compileExpr fields src _ with
      | error err =>
          rw [hCompiledKey] at hOk
          cases hOk
      | ok keyExpr =>
          rw [hCompiledKey] at hOk
          exact compileMappingSlotRead_bridged (ihKey hCompiledKey) hOk
  | mappingWord fieldName hKey wordOffset ihKey =>
      intro out hOk
      simp only [compileExpr, bind, Except.bind] at hOk
      cases hCompiledKey : compileExpr fields src _ with
      | error err =>
          rw [hCompiledKey] at hOk
          cases hOk
      | ok keyExpr =>
          rw [hCompiledKey] at hOk
          exact compileMappingSlotRead_bridged (ihKey hCompiledKey) hOk
  | mappingUint fieldName hKey ihKey =>
      intro out hOk
      simp only [compileExpr, bind, Except.bind] at hOk
      cases hCompiledKey : compileExpr fields src _ with
      | error err =>
          rw [hCompiledKey] at hOk
          cases hOk
      | ok keyExpr =>
          rw [hCompiledKey] at hOk
          exact compileMappingSlotRead_bridged (ihKey hCompiledKey) hOk
  | mapping2 fieldName hKey1 hKey2 ihKey1 ihKey2 =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · rename_i slot hFind
          simp only [bind, Except.bind] at hOk
          cases hCompiledKey1 : compileExpr fields src _ with
          | error err =>
              rw [hCompiledKey1] at hOk
              cases hOk
          | ok keyExpr1 =>
              rw [hCompiledKey1] at hOk
              cases hCompiledKey2 : compileExpr fields src _ with
              | error err =>
                  rw [hCompiledKey2] at hOk
                  cases hOk
              | ok keyExpr2 =>
                  rw [hCompiledKey2] at hOk
                  simp [Pure.pure, Except.pure] at hOk
                  subst out
                  exact bridgedExpr_sload_mappingSlot2_lit slot
                    (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2)
        · simp at hOk
  | mapping2Word fieldName hKey1 hKey2 wordOffset ihKey1 ihKey2 =>
      intro out hOk
      simp only [compileExpr] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · rename_i slot hFind
          simp only [bind, Except.bind] at hOk
          cases hCompiledKey1 : compileExpr fields src _ with
          | error err =>
              rw [hCompiledKey1] at hOk
              cases hOk
          | ok keyExpr1 =>
              rw [hCompiledKey1] at hOk
              cases hCompiledKey2 : compileExpr fields src _ with
              | error err =>
                  rw [hCompiledKey2] at hOk
                  cases hOk
              | ok keyExpr2 =>
                  rw [hCompiledKey2] at hOk
                  dsimp at hOk
                  split at hOk
                  · simp [Pure.pure, Except.pure] at hOk
                    subst out
                    exact bridgedExpr_sload_mappingSlot2_lit slot
                      (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2)
                  · simp [Pure.pure, Except.pure] at hOk
                    subst out
                    exact bridgedExpr_sload_mappingSlot2_lit_add slot wordOffset
                      (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2)
        · simp at hOk
  | structMember fieldName hKey memberName ihKey =>
      intro out hOk
      simp [compileExpr, bind, Except.bind] at hOk
      split at hOk
      · cases hOk
      · simp [Pure.pure, Except.pure] at hOk
        split at hOk
        · simp at hOk
        · split at hOk
          · simp at hOk
          · rename_i member hMember
            cases hPacked : member.packed with
            | none =>
                rw [hPacked] at hOk
                cases hCompiledKey : compileExpr fields src _ with
                | error err =>
                    rw [hCompiledKey] at hOk
                    cases hOk
                | ok keyExpr =>
                    rw [hCompiledKey] at hOk
                    simp at hOk
                    exact compileMappingSlotRead_bridged (ihKey hCompiledKey) hOk
            | some packed =>
                rw [hPacked] at hOk
                cases hCompiledKey : compileExpr fields src _ with
                | error err =>
                    rw [hCompiledKey] at hOk
                    cases hOk
                | ok keyExpr =>
                    rw [hCompiledKey] at hOk
                    simp at hOk
                    cases hSlotWord :
                        compileMappingSlotRead fields fieldName keyExpr
                          s!"structMember.{memberName}" member.wordOffset with
                    | error err =>
                        rw [hSlotWord] at hOk
                        cases hOk
                    | ok slotWord =>
                        rw [hSlotWord] at hOk
                        simp at hOk
                        subst out
                        exact bridgedExpr_packed_read
                          (compileMappingSlotRead_bridged
                            (ihKey hCompiledKey) hSlotWord)
                          packed.offset (packedMaskNat packed)
  | structMember2 fieldName hKey1 hKey2 memberName ihKey1 ihKey2 =>
      intro out hOk
      simp [compileExpr, bind, Except.bind] at hOk
      split at hOk
      · cases hOk
      · split at hOk
        · simp at hOk
        · split at hOk
          · simp at hOk
          · rename_i member hMember
            split at hOk
            · rename_i slot hFindSlot
              cases hCompiledKey1 : compileExpr fields src _ with
              | error err =>
                  rw [hCompiledKey1] at hOk
                  cases hOk
              | ok keyExpr1 =>
                  rw [hCompiledKey1] at hOk
                  cases hCompiledKey2 : compileExpr fields src _ with
                  | error err =>
                      rw [hCompiledKey2] at hOk
                      cases hOk
                  | ok keyExpr2 =>
                      rw [hCompiledKey2] at hOk
                      cases hPacked : member.packed with
                      | none =>
                          rw [hPacked] at hOk
                          simp at hOk
                          split at hOk
                          · simp [Pure.pure, Except.pure] at hOk
                            subst out
                            exact bridgedExpr_sload_mappingSlot2_lit slot
                              (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2)
                          · simp [Pure.pure, Except.pure] at hOk
                            subst out
                            exact bridgedExpr_sload_mappingSlot2_lit_add slot
                              member.wordOffset
                              (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2)
                      | some packed =>
                          rw [hPacked] at hOk
                          simp at hOk
                          split at hOk
                          · simp [Pure.pure, Except.pure] at hOk
                            subst out
                            exact bridgedExpr_packed_read
                              (bridgedExpr_sload_mappingSlot2_lit slot
                                (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2))
                              packed.offset (packedMaskNat packed)
                          · simp [Pure.pure, Except.pure] at hOk
                            subst out
                            exact bridgedExpr_packed_read
                              (bridgedExpr_sload_mappingSlot2_lit_add slot
                                member.wordOffset
                                (ihKey1 hCompiledKey1) (ihKey2 hCompiledKey2))
                              packed.offset (packedMaskNat packed)
            · simp at hOk
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
  | keccak256 _ _ ihOffset ihSize =>
      intro out hOk
      simp only [compileExpr] at hOk
      obtain ⟨co, cs, hO, hS, hEq⟩ := compileExpr_binaryShape_ok hOk
      subst hEq
      exact bridgedExpr_keccak256 co cs (ihOffset hO) (ihSize hS)
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
  | builtinExp hBase hExponent iha ihb =>
      rename_i base exponent
      intro out hOk
      simp only [compileExpr] at hOk
      cases hA : compileExpr fields src base with
      | error err =>
          simp [compileExprList, hA, bind, Except.bind] at hOk
      | ok ca =>
          cases hB : compileExpr fields src exponent with
          | error err =>
              simp [compileExprList, hA, hB, bind, Except.bind] at hOk
          | ok cb =>
              simp [compileExprList, hA, hB, builtinExpName, Pure.pure,
                Except.pure, bind, Except.bind] at hOk
              cases hOk
              exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
                (iha hA) (ihb hB)
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

/-- Convenience wrapper for the native syntactic `keccak256` source-expression
    closure when the offset and size subexpressions are compile-core. -/
theorem compileExpr_keccak256_bridgedSource_of_exprCompileCore
    (fields : List CompilationModel.Field) (src : DynamicDataSource)
    {offset size : Expr} {out : YulExpr}
    (hOffset : FunctionBody.ExprCompileCore offset)
    (hSize : FunctionBody.ExprCompileCore size)
    (hOk : compileExpr fields src (.keccak256 offset size) = .ok out) :
    BridgedExpr out :=
  compileExpr_bridgedSource fields src
    (bridgedSourceExpr_keccak256_of_exprCompileCore hOffset hSize)
    hOk

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
  | storage fieldName =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.storage fieldName) hOk
  | storageAddr fieldName =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.storageAddr fieldName) hOk
  | storageArrayLength fieldName =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.storageArrayLength fieldName) hOk
  | adtTag adtName storageField =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.adtTag adtName storageField) hOk
  | adtField adtName variantName fieldName fieldIndex storageField =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.adtField adtName variantName fieldName fieldIndex
          storageField) hOk
  | mapping fieldName hKey =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.mapping fieldName hKey) hOk
  | mappingWord fieldName hKey wordOffset =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.mappingWord fieldName hKey wordOffset) hOk
  | mappingUint fieldName hKey =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.mappingUint fieldName hKey) hOk
  | mapping2 fieldName hKey1 hKey2 =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.mapping2 fieldName hKey1 hKey2) hOk
  | mapping2Word fieldName hKey1 hKey2 wordOffset =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.mapping2Word fieldName hKey1 hKey2 wordOffset) hOk
  | structMember fieldName hKey memberName =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.structMember fieldName hKey memberName) hOk
  | structMember2 fieldName hKey1 hKey2 memberName =>
      exact compileRequireFailCond_default_bridgedSource
        (BridgedSourceExpr.structMember2 fieldName hKey1 hKey2 memberName) hOk
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
  | arrayLength name =>
      exact compileRequireFailCond_default_bridgedSource (.arrayLength name)
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
  | keccak256 hOffset hSize =>
      exact compileRequireFailCond_default_bridgedSource (.keccak256 hOffset hSize)
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
  | builtinExp hBase hExponent =>
      exact compileRequireFailCond_default_bridgedSource
        (.builtinExp hBase hExponent)
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
