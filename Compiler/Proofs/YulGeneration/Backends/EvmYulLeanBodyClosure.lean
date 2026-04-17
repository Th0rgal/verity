/-
  Body closure under `BridgedStmt` for compiler-emitted IR function prologues.

  This module begins the proof that compiler-emitted IR function and entrypoint
  bodies satisfy `BridgedStmt`, enabling `emitYul_runtimeCode_bridged`
  (`Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget`) to be used
  unconditionally for real programs.

  The first increment covers `Compiler.CompilationModel.genParamLoads` for
  parameter lists whose types are all primitive scalar ABI types
  (`uint256`/`int256`/`uint8`/`address`/`bool`/`bytes32`). This module also
  proves the static-load helper for fixed arrays and tuples whose leaves are
  those scalar ABI types. The emitted Yul is built from `let_` bindings whose
  right-hand sides are `calldataload` (optionally wrapped in `and` /
  `iszero`-`iszero`), all of which live in `bridgedBuiltins`.

  Dynamic parameters and constructor argument helpers are intentionally **out
  of scope** here — they need additional predicates covering absolute-offset
  bookkeeping and will be handled in follow-up files.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBodyClosure
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSourceExprClosure
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ParamLoading

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.YulGeneration

/-- Scalar ABI parameter types handled inline by `genScalarLoad`. These are
the `ParamType` constructors whose head word is consumed directly from
calldata without offset/length bookkeeping. -/
def IsScalarParamType : ParamType → Prop
  | .uint256 | .int256 | .uint8 | .address | .bool | .bytes32 => True
  | _ => False

/-- Static ABI parameter types whose leaves are all scalar words. This extends
`IsScalarParamType` with tuples and fixed arrays that can be decoded inline
without dynamic-offset bookkeeping. -/
inductive IsStaticScalarParamType : ParamType → Prop
  | scalar {ty : ParamType} (hScalar : IsScalarParamType ty) :
      IsStaticScalarParamType ty
  | fixedArray {elemTy : ParamType} {n : Nat}
      (hElem : IsStaticScalarParamType elemTy) :
      IsStaticScalarParamType (.fixedArray elemTy n)
  | tuple {elemTys : List ParamType}
      (hElems : ∀ ty ∈ elemTys, IsStaticScalarParamType ty) :
      IsStaticScalarParamType (.tuple elemTys)

theorem isDynamicParamType_false_of_static_scalar
    (ty : ParamType) (hStatic : IsStaticScalarParamType ty) :
    isDynamicParamType ty = false := by
  induction hStatic with
  | @scalar scalarTy hScalar =>
      cases scalarTy <;> simp [IsScalarParamType, isDynamicParamType.eq_1,
        isDynamicParamType.eq_2, isDynamicParamType.eq_3, isDynamicParamType.eq_4,
        isDynamicParamType.eq_5, isDynamicParamType.eq_6] at hScalar ⊢
  | fixedArray hElem ih =>
      rw [isDynamicParamType.eq_10]
      exact ih
  | tuple hElems hElems_ih =>
      rw [isDynamicParamType.eq_def]
      suffices hList :
          ∀ tys : List ParamType,
            (∀ ty ∈ tys, IsStaticScalarParamType ty) →
            (∀ ty ∈ tys, isDynamicParamType ty = false) →
            isDynamicParamTypeList tys = false by
        exact hList _ hElems hElems_ih
      intro tys
      induction tys with
      | nil =>
          intro _ _
          exact isDynamicParamTypeList.eq_1
      | cons elemTy rest ihRest =>
          intro hRestStatic hRestDynamic
          rw [isDynamicParamTypeList.eq_2]
          rw [hRestDynamic elemTy (by simp)]
          have hTailStatic : ∀ ty ∈ rest, IsStaticScalarParamType ty := by
            intro ty hMem
            exact hRestStatic ty (by simp [hMem])
          have hTailDynamic : ∀ ty ∈ rest, isDynamicParamType ty = false := by
            intro ty hMem
            exact hRestDynamic ty (by simp [hMem])
          rw [ihRest hTailStatic hTailDynamic]
          rfl

/-- `calldataload(lit n)` is a `BridgedExpr`: both `calldataload` and the
literal constructor are bridged. -/
private theorem bridgedExpr_calldataload_lit (offset : Nat) :
    BridgedExpr (YulExpr.call "calldataload" [YulExpr.lit offset]) := by
  refine BridgedExpr.call "calldataload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact BridgedExpr.lit offset

/-- `and(e, lit mask)` is a `BridgedExpr` whenever `e` is. -/
private theorem bridgedExpr_and_lit_mask
    (e : YulExpr) (hE : BridgedExpr e) (mask : Nat) :
    BridgedExpr (YulExpr.call "and" [e, YulExpr.lit mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact hE
  · exact BridgedExpr.lit mask

/-- `and(e, hex mask)` is a `BridgedExpr` whenever `e` is. -/
private theorem bridgedExpr_and_hex_mask
    (e : YulExpr) (hE : BridgedExpr e) (mask : Nat) :
    BridgedExpr (YulExpr.call "and" [e, YulExpr.hex mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact hE
  · exact BridgedExpr.hex mask

/-- `iszero(iszero(e))` is a `BridgedExpr` whenever `e` is. -/
private theorem bridgedExpr_iszero_iszero
    (e : YulExpr) (hE : BridgedExpr e) :
    BridgedExpr (YulExpr.call "iszero" [YulExpr.call "iszero" [e]]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro nested hNested
  simp only [List.mem_singleton] at hNested
  subst hNested
  exact hE

/-- `revert(0, 0)` as a straight-line (non-recursive) predicate witness. -/
private theorem bridgedStraightStmt_revert_zero :
    BridgedStraightStmt
      (YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])) :=
  BridgedStraightStmt.expr_revert (YulExpr.lit 0) (YulExpr.lit 0)

/-- `lt(calldatasize(), lit n)` as a `BridgedExpr`. Uses the same shape as
`bridgedExpr_calldatasize_lt` from `EvmYulLeanRetarget` but is re-exposed
here at the public level for downstream body-closure work. -/
private theorem bridgedExpr_lt_calldatasize (n : Nat) :
    BridgedExpr
      (YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit n]) := by
  refine BridgedExpr.call "lt" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · refine BridgedExpr.call "calldatasize" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro nested hNested
    cases hNested
  · exact BridgedExpr.lit n

/-- Every output of `genScalarLoad` for a scalar `ty` with the calldata
`loadWord` is a `BridgedStmt` — each emitted statement is a `let_` whose
right-hand side is built from bridged builtins. -/
theorem genScalarLoad_calldataload_bridged
    (name : String) (ty : ParamType) (offset : Nat)
    (hScalar : IsScalarParamType ty) :
    BridgedStmts
      (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos]) name ty offset) := by
  intro stmt hMem
  match ty, hScalar with
  | ParamType.uint256, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _ (bridgedExpr_calldataload_lit offset))
  | ParamType.int256, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _ (bridgedExpr_calldataload_lit offset))
  | ParamType.uint8, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _
          (bridgedExpr_and_lit_mask _ (bridgedExpr_calldataload_lit offset) 255))
  | ParamType.bytes32, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _ (bridgedExpr_calldataload_lit offset))
  | ParamType.address, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _
          (bridgedExpr_and_hex_mask _ (bridgedExpr_calldataload_lit offset) addressMask))
  | ParamType.bool, _ =>
      simp only [genScalarLoad, List.mem_singleton] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _
          (bridgedExpr_iszero_iszero _ (bridgedExpr_calldataload_lit offset)))

/-- `flatMap` preserves `BridgedStmts` when every generated chunk is bridged. -/
private theorem BridgedStmts_flatMap {α : Type} (xs : List α) (f : α → List YulStmt)
    (h : ∀ x ∈ xs, BridgedStmts (f x)) :
    BridgedStmts (xs.flatMap f) := by
  intro stmt hMem
  rcases List.mem_flatMap.mp hMem with ⟨x, hx, hStmt⟩
  exact h x hx stmt hStmt

private theorem BridgedStmts_append {xs ys : List YulStmt}
    (hXs : BridgedStmts xs) (hYs : BridgedStmts ys) :
    BridgedStmts (xs ++ ys) := by
  intro stmt hMem
  rcases List.mem_append.mp hMem with h | h
  · exact hXs stmt h
  · exact hYs stmt h

/-- Static scalar composites (`fixedArray`/`tuple` whose leaves are scalar ABI
words) generate only bridged calldata-load statements. -/
theorem genStaticTypeLoads_calldataload_bridged
    (name : String) (ty : ParamType) (offset : Nat)
    (hStatic : IsStaticScalarParamType ty) :
    BridgedStmts
      (genStaticTypeLoads (fun pos => YulExpr.call "calldataload" [pos])
        name ty offset) := by
  induction hStatic generalizing name offset with
  | @scalar ty hScalar =>
      cases ty <;> simp [IsScalarParamType, genStaticTypeLoads.eq_def] at hScalar ⊢
      all_goals
        exact genScalarLoad_calldataload_bridged name _ offset (by trivial)
  | @fixedArray elemTy n hElem ih =>
      rw [genStaticTypeLoads.eq_7]
      apply BridgedStmts_flatMap
      intro i hi
      exact ih (name := s!"{name}_{i}") (offset := offset + i * paramHeadSize _)
  | @tuple elemTys hElems hElems_ih =>
      rw [genStaticTypeLoads.eq_8]
      suffices hGo :
          ∀ (tys : List ParamType) (idx curOffset : Nat),
            (∀ ty ∈ tys, IsStaticScalarParamType ty) →
            (∀ ty ∈ tys,
              ∀ (name : String) (offset : Nat),
                BridgedStmts
                  (genStaticTypeLoads
                    (fun pos => YulExpr.call "calldataload" [pos])
                    name ty offset)) →
            BridgedStmts
              (genStaticTypeLoads.go
                (fun pos => YulExpr.call "calldataload" [pos])
                name tys idx curOffset) by
        exact hGo elemTys 0 offset hElems hElems_ih
      intro tys
      induction tys with
      | nil =>
          intro idx curOffset _ _
          rw [genStaticTypeLoads.go.eq_def]
          intro stmt hMem
          cases hMem
      | cons elemTy rest ihRest =>
          intro idx curOffset hRestStatic hRestIH
          rw [genStaticTypeLoads.go.eq_def]
          apply BridgedStmts_append
          · exact hRestIH elemTy (by simp) s!"{name}_{idx}" curOffset
          · have hTailStatic : ∀ ty ∈ rest, IsStaticScalarParamType ty := by
              intro ty hMem
              exact hRestStatic ty (by simp [hMem])
            have hTailIH :
                ∀ ty ∈ rest,
                  ∀ (name : String) (offset : Nat),
                    BridgedStmts
                      (genStaticTypeLoads
                        (fun pos => YulExpr.call "calldataload" [pos])
                        name ty offset) := by
              intro ty hMem
              exact hRestIH ty (by simp [hMem])
            exact ihRest (idx + 1) (curOffset + paramHeadSize elemTy)
              hTailStatic hTailIH

/-- Parameter lists whose types are all scalar. -/
def AllScalarParams (params : List Param) : Prop :=
  ∀ p ∈ params, IsScalarParamType p.ty

/-- Parameter lists whose types are static ABI composites with scalar leaves. -/
def AllStaticScalarParams (params : List Param) : Prop :=
  ∀ p ∈ params, IsStaticScalarParamType p.ty

/-- The fixed-array alias emitted for scalar-element arrays is a bridged `let`. -/
private theorem fixedArrayFirstAlias_bridged
    (name : String) (elemTy : ParamType) (n : Nat) :
    BridgedStmts
      (if n == 0 then []
       else
        if isScalarParamType elemTy then
          [YulStmt.let_ name (YulExpr.ident s!"{name}_0")]
        else
          []) := by
  by_cases hN : n == 0
  · intro stmt hMem
    simp [hN] at hMem
  · by_cases hScalar : isScalarParamType elemTy
    · intro stmt hMem
      simp [hN, hScalar] at hMem
      subst hMem
      exact BridgedStmt.straight _
        (BridgedStraightStmt.let_ name _ (BridgedExpr.ident s!"{name}_0"))
    · intro stmt hMem
      simp [hN, hScalar] at hMem

/-- For a scalar parameter type, `genParamLoadBodyFrom` on a cons cell decomposes
as `genScalarLoad ...` appended to the tail. This isolates the 6-way case
split on `ParamType` constructors from the surrounding induction. -/
private theorem genParamLoadBodyFrom_cons_scalar
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (param : Param) (rest : List Param) (headOffset : Nat)
    (hScalar : IsScalarParamType param.ty) :
    genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset (param :: rest) headOffset
    = genScalarLoad loadWord param.name param.ty headOffset ++
      genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset rest
        (headOffset + paramHeadSize param.ty) := by
  match hTy : param.ty, hScalar with
  | ParamType.uint256, _ | ParamType.int256, _ | ParamType.uint8, _
  | ParamType.address, _ | ParamType.bool, _ | ParamType.bytes32, _ =>
      simp [genParamLoadBodyFrom, hTy]

/-- For scalar-only parameter lists, `genParamLoadBodyFrom` with the calldata
loader produces only bridged statements. Each per-parameter stmt block is
`genScalarLoad ... param.name param.ty headOffset`, which we already know is
`BridgedStmts` by `genScalarLoad_calldataload_bridged`. -/
private theorem genParamLoadBodyFrom_calldataload_bridged
    (headSize baseOffset : Nat) (params : List Param) (headOffset : Nat)
    (hScalar : AllScalarParams params) :
    BridgedStmts
      (genParamLoadBodyFrom
        (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" [])
        headSize baseOffset params headOffset) := by
  induction params generalizing headOffset with
  | nil =>
      intro stmt hMem
      simp [genParamLoadBodyFrom] at hMem
  | cons param rest ih =>
      have hHead : IsScalarParamType param.ty := hScalar param (by simp)
      have hRest : AllScalarParams rest := by
        intro p hp
        exact hScalar p (by simp [hp])
      have hHere : BridgedStmts
          (genScalarLoad (fun pos => YulExpr.call "calldataload" [pos])
            param.name param.ty headOffset) :=
        genScalarLoad_calldataload_bridged param.name param.ty headOffset hHead
      have hTail : BridgedStmts
          (genParamLoadBodyFrom
            (fun pos => YulExpr.call "calldataload" [pos])
            (YulExpr.call "calldatasize" [])
            headSize baseOffset rest (headOffset + paramHeadSize param.ty)) :=
        ih (headOffset + paramHeadSize param.ty) hRest
      rw [genParamLoadBodyFrom_cons_scalar _ _ _ _ _ _ _ hHead]
      intro stmt hMem
      rcases List.mem_append.mp hMem with h | h
      · exact hHere stmt h
      · exact hTail stmt h

/-- For static scalar-composite parameter lists, `genParamLoadBodyFrom` with the
calldata loader emits only bridged statements. Scalar heads reuse
`genScalarLoad_calldataload_bridged`; tuple/fixed-array heads reuse the proved
`genStaticTypeLoads_calldataload_bridged` helper, plus the scalar fixed-array
alias when present. -/
private theorem genParamLoadBodyFrom_calldataload_static_scalar_bridged
    (headSize baseOffset : Nat) (params : List Param) (headOffset : Nat)
    (hStatic : AllStaticScalarParams params) :
    BridgedStmts
      (genParamLoadBodyFrom
        (fun pos => YulExpr.call "calldataload" [pos])
        (YulExpr.call "calldatasize" [])
        headSize baseOffset params headOffset) := by
  induction params generalizing headOffset with
  | nil =>
      intro stmt hMem
      simp [genParamLoadBodyFrom] at hMem
  | cons param rest ih =>
      rcases param with ⟨paramName, paramTy⟩
      have hHead : IsStaticScalarParamType paramTy :=
        hStatic { name := paramName, ty := paramTy } (by simp)
      have hRest : AllStaticScalarParams rest := by
        intro p hp
        exact hStatic p (by simp [hp])
      have hTail : BridgedStmts
          (genParamLoadBodyFrom
            (fun pos => YulExpr.call "calldataload" [pos])
            (YulExpr.call "calldatasize" [])
            headSize baseOffset rest (headOffset + paramHeadSize paramTy)) :=
        ih (headOffset + paramHeadSize paramTy) hRest
      cases hHead with
      | scalar hScalar =>
          rw [genParamLoadBodyFrom_cons_scalar _ _ _ _ _ _ _ hScalar]
          apply BridgedStmts_append
          · exact genScalarLoad_calldataload_bridged paramName paramTy headOffset hScalar
          · exact hTail
      | @fixedArray elemTy n hElem =>
          simp only [genParamLoadBodyFrom,
            isDynamicParamType_false_of_static_scalar _ (IsStaticScalarParamType.fixedArray hElem)]
          apply BridgedStmts_append
          · by_cases hN : n == 0
            · simp [hN]
              exact (genStaticTypeLoads_calldataload_bridged paramName
                (.fixedArray elemTy n) headOffset (IsStaticScalarParamType.fixedArray hElem))
            · simp [hN]
              apply BridgedStmts_append
              · exact (genStaticTypeLoads_calldataload_bridged paramName
                  (.fixedArray elemTy n) headOffset (IsStaticScalarParamType.fixedArray hElem))
              · simpa [hN] using fixedArrayFirstAlias_bridged paramName elemTy n
          · exact hTail
      | @tuple elemTys hElems =>
          simp only [genParamLoadBodyFrom,
            isDynamicParamType_false_of_static_scalar _ (IsStaticScalarParamType.tuple hElems)]
          apply BridgedStmts_append
          · exact genStaticTypeLoads_calldataload_bridged paramName (.tuple elemTys)
              headOffset (IsStaticScalarParamType.tuple hElems)
          · exact hTail

/-- `genParamLoads` produces only bridged statements when every parameter has
a scalar ABI type. The emitted prologue is a minimum-input-size guard
followed by one `let` per parameter. -/
theorem genParamLoads_scalar_bridged
    (params : List Param) (hScalar : AllScalarParams params) :
    BridgedStmts (genParamLoads params) := by
  unfold genParamLoads genParamLoadsFrom
  intro stmt hMem
  simp only [List.mem_cons] at hMem
  rcases hMem with rfl | hMem
  · -- the `minInputSizeCheck` is `if (lt(calldatasize(), lit N)) { revert(0,0) }`
    refine BridgedStmt.if_ _ _ (bridgedExpr_lt_calldatasize _) ?_
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact BridgedStmt.straight _ bridgedStraightStmt_revert_zero
  · exact genParamLoadBodyFrom_calldataload_bridged _ 4 params 4 hScalar stmt hMem

/-- `genParamLoads` produces only bridged statements when every parameter is a
static ABI value whose leaves are scalar words. This is the real prologue-level
closure theorem for fixed arrays and tuples of scalar ABI types. -/
theorem genParamLoads_static_scalar_bridged
    (params : List Param) (hStatic : AllStaticScalarParams params) :
    BridgedStmts (genParamLoads params) := by
  unfold genParamLoads genParamLoadsFrom
  intro stmt hMem
  simp only [List.mem_cons] at hMem
  rcases hMem with rfl | hMem
  · refine BridgedStmt.if_ _ _ (bridgedExpr_lt_calldatasize _) ?_
    intro s hs
    simp only [List.mem_singleton] at hs
    subst hs
    exact BridgedStmt.straight _ bridgedStraightStmt_revert_zero
  · exact genParamLoadBodyFrom_calldataload_static_scalar_bridged _ 4 params 4
      hStatic stmt hMem

/-! ## Source statement body closure: scalar leaf bindings

The runtime wrapper theorem is conditional on embedded IR bodies satisfying
`BridgedStmts`. The following small source-level fragment connects the scalar
leaf expression closure in `EvmYulLeanSourceExprClosure` to the two simplest
`compileStmt` forms: `letVar` and `assignVar`.
-/

/-- Source statements whose emitted Yul is a single value-binding statement
with a scalar leaf expression on the right-hand side. -/
inductive BridgedSourceBindingStmt : Stmt → Prop
  | letVar (name : String) (value : Expr)
      (hValue : BridgedSourceExprLeaf value) :
      BridgedSourceBindingStmt (.letVar name value)
  | assignVar (name : String) (value : Expr)
      (hValue : BridgedSourceExprLeaf value) :
      BridgedSourceBindingStmt (.assignVar name value)

def BridgedSourceBindingStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceBindingStmt stmt

/-- Source statements whose emitted Yul is a single value-binding statement
with a pure bridged source expression on the right-hand side. -/
inductive BridgedSourcePureBindingStmt : Stmt → Prop
  | letVar (name : String) (value : Expr)
      (hValue : BridgedSourceExpr value) :
      BridgedSourcePureBindingStmt (.letVar name value)
  | assignVar (name : String) (value : Expr)
      (hValue : BridgedSourceExpr value) :
      BridgedSourcePureBindingStmt (.assignVar name value)

def BridgedSourcePureBindingStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourcePureBindingStmt stmt

/-- A scalar-leaf `letVar`/`assignVar` source statement compiles to Yul that
satisfies `BridgedStmts`. -/
theorem compileStmt_binding_leaf_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceBindingStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | letVar name value hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource_leaf fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.let_ name valueExpr hBridged)
  | assignVar name value hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource_leaf fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.assign name valueExpr hBridged)

/-- Lists made only of scalar-leaf `letVar`/`assignVar` statements compile to
Yul lists satisfying `BridgedStmts`. This is the first direct body-closure
theorem over `compileStmtList`. -/
theorem compileStmtList_binding_leaf_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceBindingStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro stmt hMem
      cases hMem
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceBindingStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceBindingStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_binding_leaf_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- A pure-expression `letVar`/`assignVar` source statement compiles to Yul
that satisfies `BridgedStmts`. -/
theorem compileStmt_pure_binding_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourcePureBindingStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | letVar name value hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.let_ name valueExpr hBridged)
  | assignVar name value hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.assign name valueExpr hBridged)

/-- Lists made only of pure-expression `letVar`/`assignVar` statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_pure_binding_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourcePureBindingStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro stmt hMem
      cases hMem
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourcePureBindingStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourcePureBindingStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_pure_binding_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: pure bindings plus single-slot storage writes -/

/-- Source statements in the current storage body-closure fragment.

This fragment covers the common compiler bodies that compute values with pure
`letVar`/`assignVar` statements and write them to an unpacked single storage
slot via `setStorage`. The field-layout hypotheses deliberately exclude packed
fields and alias slots; those emit blocks with `sload`/masking/compat writes and
need their own closure lemmas. -/
inductive BridgedSourceStorageStmt (fields : List Field) : Stmt → Prop
  | pureBinding {stmt : Stmt} (hStmt : BridgedSourcePureBindingStmt stmt) :
      BridgedSourceStorageStmt fields stmt
  | setStorage (field : String) (value : Expr) (f : Field) (slot : Nat)
      (hValue : BridgedSourceExpr value)
      (hNotMapping : isMapping fields field = false)
      (hFind :
        findFieldWithResolvedSlot fields field =
          some ({ f with packedBits := none, aliasSlots := [] }, slot)) :
      BridgedSourceStorageStmt fields (.setStorage field value)

def BridgedSourceStorageStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStorageStmt fields stmt

/-- An unpacked single-slot `setStorage` source statement with a pure bridged
right-hand side compiles to a literal-slot `sstore`, hence satisfies
`BridgedStmts`. -/
theorem compileStmt_setStorage_singleSlot_pure_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (value : Expr) (f : Field) (slot : Nat)
    (hValue : BridgedSourceExpr value)
    (hNotMapping : isMapping fields field = false)
    (hFind :
      findFieldWithResolvedSlot fields field =
        some ({ f with packedBits := none, aliasSlots := [] }, slot)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames (.setStorage field value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorage at hOk
  simp [hNotMapping, hFind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err =>
      simp [hExpr] at hOk
  | ok valueExpr =>
      simp [hExpr] at hOk
      subst out
      have hBridged : BridgedExpr valueExpr :=
        compileExpr_bridgedSource fields dynamicSource hValue hExpr
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      exact BridgedStmt.straight _
        (BridgedStraightStmt.expr_sstore_lit slot valueExpr hBridged)

/-- Each statement in the storage fragment compiles to Yul satisfying
`BridgedStmts`. -/
theorem compileStmt_storage_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | pureBinding hPure =>
      exact compileStmt_pure_binding_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hPure hOk
  | setStorage field value f slot hValue hNotMapping hFind =>
      exact compileStmt_setStorage_singleSlot_pure_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field value f slot
        hValue hNotMapping hFind hOk

/-- Lists made of pure `letVar`/`assignVar` statements and unpacked single-slot
`setStorage` statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_storage_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro stmt hMem
      cases hMem
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStorageStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStorageStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_storage_fragment_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: `stop` and external `return`

Two more simple compiler-emitted source statement shapes whose Yul output is
a fixed-length list of `BridgedStraightStmts`:

* `Stmt.stop` emits `[expr (call "stop" [])]`, matching
  `BridgedStraightStmt.expr_stop`.
* `Stmt.return value` with `isInternal = false` emits
  `[expr (call "mstore" [lit 0, valueExpr]), expr (call "return" [lit 0, lit 32])]`,
  matching `BridgedStraightStmt.expr_mstore` and `BridgedStraightStmt.expr_return`,
  provided `valueExpr` is a `BridgedExpr` (discharged via `compileExpr_bridgedSource`).
-/

/-- Source statements `stop` or external `return value` whose RHS is a pure
`BridgedSourceExpr`. Both compile to fixed-shape lists of `BridgedStraightStmts`. -/
inductive BridgedSourceTerminatorStmt : Stmt → Prop
  | stop : BridgedSourceTerminatorStmt .stop
  | returnExternal (value : Expr) (hValue : BridgedSourceExpr value) :
      BridgedSourceTerminatorStmt (.return value)

def BridgedSourceTerminatorStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceTerminatorStmt stmt

/-- A `Stmt.stop` source statement compiles to a single-statement Yul list
satisfying `BridgedStmts`. -/
private theorem compileStmt_stop_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames .stop = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, Pure.pure, Except.pure] at hOk
  cases hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  exact BridgedStmt.straight _ BridgedStraightStmt.expr_stop

/-- A `Stmt.return value` source statement with a `BridgedSourceExpr` RHS and
`isInternal = false` compiles to a fixed two-statement Yul list satisfying
`BridgedStmts`. -/
private theorem compileStmt_return_external_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {value : Expr} (hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames (.return value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr] at hOk
  | ok valueExpr =>
      simp [hExpr, Pure.pure, Except.pure] at hOk
      subst out
      have hBridged : BridgedExpr valueExpr :=
        compileExpr_bridgedSource fields dynamicSource hValue hExpr
      intro yulStmt hMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
      rcases hMem with rfl | rfl
      · exact BridgedStmt.straight _
          (BridgedStraightStmt.expr_mstore (.lit 0) valueExpr (BridgedExpr.lit 0) hBridged)
      · exact BridgedStmt.straight _
          (BridgedStraightStmt.expr_return (.lit 0) (.lit 32)
            (BridgedExpr.lit 0) (BridgedExpr.lit 32))

/-- External (`isInternal = false`) `stop`/`return` source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmt_terminator_external_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceTerminatorStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | stop =>
      exact compileStmt_stop_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hOk
  | returnExternal value hValue =>
      exact compileStmt_return_external_bridged fields events errors dynamicSource
        internalRetNames inScopeNames hValue hOk

/-- Lists made only of external `stop`/`return` source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_terminator_external_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceTerminatorStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro stmt hMem
      cases hMem
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          false inScopeNames head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceTerminatorStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceTerminatorStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_terminator_external_bridged fields events errors dynamicSource
                  internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: `require`

Plain `Stmt.require cond message` compiles to a Yul `if` whose body is
`revertWithMessage message`. The theorem below keeps the condition side
explicit: callers only need to show that `compileRequireFailCond` emits a
`BridgedExpr` for their condition fragment.
-/

/-- The fixed `revertWithMessage` helper emits only bridged straight-line
statements (`mstore` literals/hex words followed by `revert`). -/
private theorem revertWithMessage_bridged (message : String) :
    BridgedStmts (revertWithMessage message) := by
  unfold revertWithMessage
  intro yulStmt hMem
  rcases List.mem_append.mp hMem with hPrefix | hRevert
  · rcases List.mem_append.mp hPrefix with hHeader | hData
    · simp only [List.mem_cons, List.mem_nil_iff] at hHeader
      rcases hHeader with rfl | rfl | rfl | hNil
      · exact BridgedStmt.straight _
          (BridgedStraightStmt.expr_mstore (YulExpr.lit 0)
            (YulExpr.hex errorStringSelectorWord)
            (BridgedExpr.lit 0) (BridgedExpr.hex errorStringSelectorWord))
      · exact BridgedStmt.straight _
          (BridgedStraightStmt.expr_mstore (YulExpr.lit 4)
            (YulExpr.lit 32) (BridgedExpr.lit 4) (BridgedExpr.lit 32))
      · exact BridgedStmt.straight _
          (BridgedStraightStmt.expr_mstore (YulExpr.lit 36)
            (YulExpr.lit (bytesFromString message).length)
            (BridgedExpr.lit 36) (BridgedExpr.lit (bytesFromString message).length))
      · cases hNil
    · simp only [List.mem_map] at hData
      rcases hData with ⟨chunkAndIdx, _hChunk, rfl⟩
      rcases chunkAndIdx with ⟨chunk, idx⟩
      exact BridgedStmt.straight _
        (BridgedStraightStmt.expr_mstore
          (YulExpr.lit (68 + idx * 32))
          (YulExpr.hex (wordFromBytes chunk))
          (BridgedExpr.lit (68 + idx * 32))
          (BridgedExpr.hex (wordFromBytes chunk)))
  · simp only [List.mem_singleton] at hRevert
    subst yulStmt
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_revert (YulExpr.lit 0)
        (YulExpr.lit (68 + ((bytesFromString message).length + 31) / 32 * 32)))

/-- Source `require` statements whose compiled failure condition is bridged. -/
inductive BridgedSourceRequireStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | require (cond : Expr) (message : String)
      (hFailCond :
        ∀ {failCond : YulExpr},
          compileRequireFailCond fields dynamicSource cond = .ok failCond →
          BridgedExpr failCond) :
      BridgedSourceRequireStmt fields dynamicSource (.require cond message)

def BridgedSourceRequireStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceRequireStmt fields dynamicSource stmt

/-- A plain `Stmt.require` whose compiled failure condition is bridged compiles
to a bridged Yul `if` around `revertWithMessage`. -/
theorem compileStmt_require_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    {cond : Expr} {message : String}
    (hFailCond :
      ∀ {failCond : YulExpr},
        compileRequireFailCond fields dynamicSource cond = .ok failCond →
        BridgedExpr failCond) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames (.require cond message) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hFail : compileRequireFailCond fields dynamicSource cond with
  | error err =>
      simp [hFail] at hOk
  | ok failCond =>
      simp [hFail, Pure.pure, Except.pure] at hOk
      subst out
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      exact BridgedStmt.if_ failCond (revertWithMessage message)
        (hFailCond hFail) (revertWithMessage_bridged message)

/-- Lists made only of plain `require` statements whose compiled failure
conditions are bridged compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_require_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceRequireStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro stmt hMem
      cases hMem
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceRequireStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceRequireStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              cases hHeadSource with
              | require cond message hFailCond =>
                  exact BridgedStmts_append
                    (compileStmt_require_bridged fields events errors dynamicSource
                      internalRetNames isInternal inScopeNames hFailCond hHead)
                    (ih (collectStmtNames (.require cond message) ++ inScopeNames)
                      hTailSource hTail)

end Compiler.Proofs.YulGeneration.Backends
