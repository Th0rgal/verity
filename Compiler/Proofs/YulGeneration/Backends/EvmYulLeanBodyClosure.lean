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
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ParamLoading

set_option linter.unusedSimpArgs false

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

/-- `iszero(ident name)` is a `BridgedExpr`. -/
private theorem bridgedExpr_iszero_ident (name : String) :
    BridgedExpr (YulExpr.call "iszero" [YulExpr.ident name]) := by
  refine BridgedExpr.call "iszero" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro nested hNested
  simp only [List.mem_singleton] at hNested
  subst hNested
  exact BridgedExpr.ident name

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
      simp [genParamLoadBodyFrom, genSingleParamLoad, hTy]

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
          simp [genParamLoadBodyFrom, genSingleParamLoad,
            isDynamicParamType_false_of_static_scalar _ (IsStaticScalarParamType.fixedArray hElem)]
          apply BridgedStmts_append
          · by_cases hN : n = 0
            · simpa only [if_pos hN] using
                (genStaticTypeLoads_calldataload_bridged paramName
                  (.fixedArray elemTy n) headOffset (IsStaticScalarParamType.fixedArray hElem))
            · simpa only [if_neg hN] using
                (BridgedStmts_append
                  (genStaticTypeLoads_calldataload_bridged paramName
                    (.fixedArray elemTy n) headOffset (IsStaticScalarParamType.fixedArray hElem))
                  (by simpa [hN] using fixedArrayFirstAlias_bridged paramName elemTy n))
          · exact hTail
      | @tuple elemTys hElems =>
          simp [genParamLoadBodyFrom, genSingleParamLoad,
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

private theorem genScalarLoad_noFuncDefs
    (loadWord : YulExpr → YulExpr) (name : String)
    (ty : ParamType) (offset : Nat) :
    Native.yulStmtsContainFuncDef
      (genScalarLoad loadWord name ty offset) = false := by
  cases ty <;> simp [genScalarLoad, Native.yulStmtContainsFuncDef]

private theorem genStaticTypeLoads_go_noFuncDefs
    (loadWord : YulExpr → YulExpr) (name : String)
    (tys : List ParamType) (idx curOffset : Nat)
    (hNoFunc :
      ∀ ty ∈ tys, ∀ (name : String) (offset : Nat),
        Native.yulStmtsContainFuncDef
          (genStaticTypeLoads loadWord name ty offset) = false) :
    Native.yulStmtsContainFuncDef
      (genStaticTypeLoads.go loadWord name tys idx curOffset) = false := by
  induction tys generalizing idx curOffset with
  | nil =>
      rw [genStaticTypeLoads.go.eq_def]
      simp
  | cons elemTy rest ih =>
      rw [genStaticTypeLoads.go.eq_def]
      have hHere := hNoFunc elemTy (by simp) s!"{name}_{idx}" curOffset
      have hTail :
          ∀ ty ∈ rest, ∀ (name : String) (offset : Nat),
            Native.yulStmtsContainFuncDef
              (genStaticTypeLoads loadWord name ty offset) = false := by
        intro ty hMem
        exact hNoFunc ty (by simp [hMem])
      simp [hHere, ih (idx + 1) (curOffset + paramHeadSize elemTy) hTail]

private theorem genStaticTypeLoads_noFuncDefs
    (loadWord : YulExpr → YulExpr) (name : String)
    (ty : ParamType) (offset : Nat)
    (hStatic : IsStaticScalarParamType ty) :
    Native.yulStmtsContainFuncDef
      (genStaticTypeLoads loadWord name ty offset) = false := by
  induction hStatic generalizing name offset with
  | @scalar ty hScalar =>
      cases ty <;> simp [IsScalarParamType, genStaticTypeLoads.eq_def] at hScalar ⊢
      all_goals
        exact genScalarLoad_noFuncDefs loadWord name _ offset
  | @fixedArray elemTy n hElem ih =>
      rw [genStaticTypeLoads.eq_7]
      exact Native.yulStmtsContainFuncDef_flatMap_false
        (List.range n)
        (fun i =>
          genStaticTypeLoads loadWord s!"{name}_{i}" elemTy
            (offset + i * paramHeadSize elemTy))
        (by
          intro i _hi
          exact ih s!"{name}_{i}" (offset + i * paramHeadSize elemTy))
  | @tuple elemTys hElems hElems_ih =>
      rw [genStaticTypeLoads.eq_8]
      exact genStaticTypeLoads_go_noFuncDefs loadWord name elemTys 0 offset
        hElems_ih

private theorem fixedArrayFirstAlias_noFuncDefs
    (name : String) (elemTy : ParamType) (n : Nat) :
    Native.yulStmtsContainFuncDef
      (if n == 0 then []
       else
        if isScalarParamType elemTy then
          [YulStmt.let_ name (YulExpr.ident s!"{name}_0")]
        else
          []) = false := by
  by_cases hN : n == 0
  · simp [hN]
  · by_cases hScalar : isScalarParamType elemTy
    · simp [hN, hScalar, Native.yulStmtContainsFuncDef]
    · simp [hN, hScalar]

private theorem genParamLoadBodyFrom_scalar_noFuncDefs
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      AllScalarParams params →
      Native.yulStmtsContainFuncDef
        (genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset
          params headOffset) = false := by
  intro params
  induction params with
  | nil =>
      intro headOffset _hScalar
      simp [genParamLoadBodyFrom]
  | cons param rest ih =>
      intro headOffset hScalar
      rcases param with ⟨paramName, paramTy⟩
      have hHead : IsScalarParamType paramTy :=
        hScalar ⟨paramName, paramTy⟩ (by simp)
      have hRest : AllScalarParams rest := by
        intro p hp
        exact hScalar p (by simp [hp])
      cases paramTy <;> simp [IsScalarParamType] at hHead
      all_goals
        simp [genParamLoadBodyFrom, genSingleParamLoad, genScalarLoad_noFuncDefs]
        exact ih _ hRest

/-- `genParamLoads` emits no Yul function declarations for scalar ABI
parameter lists. This is the native-fragment shape companion to
`genParamLoads_scalar_bridged`. -/
theorem genParamLoads_scalar_noFuncDefs
    (params : List Param) (hScalar : AllScalarParams params) :
    Native.yulStmtsContainFuncDef (genParamLoads params) = false := by
  unfold genParamLoads genParamLoadsFrom
  simp [Native.yulStmtContainsFuncDef,
    genParamLoadBodyFrom_scalar_noFuncDefs
      (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) _ 4 params 4 hScalar]

private theorem genSingleParamLoad_static_scalar_noFuncDefs
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) (name : String) (ty : ParamType)
    (headOffset : Nat) (hStatic : IsStaticScalarParamType ty) :
    Native.yulStmtsContainFuncDef
      (genSingleParamLoad loadWord sizeExpr headSize baseOffset name ty
        headOffset) = false := by
  cases hStatic with
  | scalar hScalar =>
      cases ty <;> simp [IsScalarParamType] at hScalar
      all_goals
        simp [genSingleParamLoad, genScalarLoad_noFuncDefs]
  | @fixedArray elemTy n hElem =>
      have hStaticLoads :
          Native.yulStmtsContainFuncDef
            (genStaticTypeLoads loadWord name (.fixedArray elemTy n)
              headOffset) = false :=
        genStaticTypeLoads_noFuncDefs loadWord name (.fixedArray elemTy n)
          headOffset (IsStaticScalarParamType.fixedArray hElem)
      have hAlias := fixedArrayFirstAlias_noFuncDefs name elemTy n
      by_cases hN : n == 0
      · simp [genSingleParamLoad,
          isDynamicParamType_false_of_static_scalar _
            (IsStaticScalarParamType.fixedArray hElem),
          hN, hStaticLoads]
      · simp [genSingleParamLoad,
          isDynamicParamType_false_of_static_scalar _
            (IsStaticScalarParamType.fixedArray hElem),
          hN, hStaticLoads]
        simpa [hN] using hAlias
  | @tuple elemTys hElems =>
      have hStaticLoads :
          Native.yulStmtsContainFuncDef
            (genStaticTypeLoads loadWord name (.tuple elemTys) headOffset) =
              false :=
        genStaticTypeLoads_noFuncDefs loadWord name (.tuple elemTys)
          headOffset (IsStaticScalarParamType.tuple hElems)
      simp [genSingleParamLoad,
        isDynamicParamType_false_of_static_scalar _
          (IsStaticScalarParamType.tuple hElems),
        hStaticLoads]

private theorem genParamLoadBodyFrom_static_scalar_noFuncDefs
    (loadWord : YulExpr → YulExpr) (sizeExpr : YulExpr)
    (headSize baseOffset : Nat) :
    ∀ (params : List Param) (headOffset : Nat),
      AllStaticScalarParams params →
      Native.yulStmtsContainFuncDef
        (genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset
          params headOffset) = false := by
  intro params
  induction params with
  | nil =>
      intro headOffset _hStatic
      simp [genParamLoadBodyFrom]
  | cons param rest ih =>
      intro headOffset hStatic
      rcases param with ⟨paramName, paramTy⟩
      have hHead : IsStaticScalarParamType paramTy :=
        hStatic ⟨paramName, paramTy⟩ (by simp)
      have hRest : AllStaticScalarParams rest := by
        intro p hp
        exact hStatic p (by simp [hp])
      have hTail :
          Native.yulStmtsContainFuncDef
            (genParamLoadBodyFrom loadWord sizeExpr headSize baseOffset
              rest (headOffset + paramHeadSize paramTy)) = false :=
        ih _ hRest
      simp [genParamLoadBodyFrom,
        genSingleParamLoad_static_scalar_noFuncDefs loadWord sizeExpr headSize
          baseOffset paramName paramTy headOffset hHead,
        hTail]

/-- `genParamLoads` emits no Yul function declarations for static ABI
parameter lists whose leaves are scalar words. This is the native-fragment
shape companion to `genParamLoads_static_scalar_bridged`. -/
theorem genParamLoads_static_scalar_noFuncDefs
    (params : List Param) (hStatic : AllStaticScalarParams params) :
    Native.yulStmtsContainFuncDef (genParamLoads params) = false := by
  unfold genParamLoads genParamLoadsFrom
  simp [Native.yulStmtContainsFuncDef,
    genParamLoadBodyFrom_static_scalar_noFuncDefs
      (fun pos => YulExpr.call "calldataload" [pos])
      (YulExpr.call "calldatasize" []) _ 4 params 4 hStatic]

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
          inScopeNames [] stmt = .ok out →
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

/-- Scalar-leaf binding statements compile to Yul lists with no nested
function declarations. -/
theorem compileStmt_binding_leaf_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceBindingStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | letVar name value _hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]
  | assignVar name value _hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

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
          inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
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

/-- Lists made only of scalar-leaf `letVar`/`assignVar` statements compile to
Yul lists with no nested function declarations. -/
theorem compileStmtList_binding_leaf_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceBindingStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      rfl
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
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
              simp [
                compileStmt_binding_leaf_noFuncDefs fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead,
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail]

/-- A pure-expression `letVar`/`assignVar` source statement compiles to Yul
that satisfies `BridgedStmts`. -/
theorem compileStmt_pure_binding_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourcePureBindingStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
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

/-- Pure-expression binding statements compile to Yul lists with no nested
function declarations. -/
theorem compileStmt_pure_binding_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourcePureBindingStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | letVar name value _hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]
  | assignVar name value _hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr] at hOk
      | ok valueExpr =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

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
          inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
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

/-- Lists made only of pure-expression `letVar`/`assignVar` statements compile
to Yul lists with no nested function declarations. -/
theorem compileStmtList_pure_binding_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String), BridgedSourcePureBindingStmts stmts →
      ∀ {out : List YulStmt}, compileStmtList fields events errors dynamicSource
        internalRetNames isInternal inScopeNames [] stmts = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      rfl
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourcePureBindingStmt head := hSource head (by simp)
              have hTailSource : BridgedSourcePureBindingStmts tail := by
                intro stmt hMem; exact hSource stmt (by simp [hMem])
              simp [
                compileStmt_pure_binding_noFuncDefs fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead,
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail]

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
          some ({ f with packedBits := none, aliasSlots := [] }, slot))
      (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields) :
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
        some ({ f with packedBits := none, aliasSlots := [] }, slot))
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStorage field value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorage at hOk
  simp [hNotMapping, hFind] at hOk
  cases hty : f.ty with
  | adt name maxFields =>
      exact False.elim (hNotAdt name maxFields hty)
  | uint256 | address | dynamicArray | mappingTyped | mappingStruct | mappingStruct2 =>
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr, hty] at hOk
      | ok valueExpr =>
          simp [hExpr, hty] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.expr_sstore_lit slot valueExpr hBridged)

/-- An unpacked single-slot `setStorage` source statement with a pure bridged
right-hand side compiles to a Yul list with no nested function declarations. -/
theorem compileStmt_setStorage_singleSlot_pure_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (value : Expr) (f : Field) (slot : Nat)
    (_hValue : BridgedSourceExpr value)
    (hNotMapping : isMapping fields field = false)
    (hFind :
      findFieldWithResolvedSlot fields field =
        some ({ f with packedBits := none, aliasSlots := [] }, slot))
    (hNotAdt : ∀ name maxFields, f.ty ≠ FieldType.adt name maxFields) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStorage field value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorage at hOk
  simp [hNotMapping, hFind] at hOk
  cases hty : f.ty with
  | adt name maxFields =>
      exact False.elim (hNotAdt name maxFields hty)
  | uint256 | address | dynamicArray | mappingTyped | mappingStruct | mappingStruct2 =>
      cases hExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hExpr, hty] at hOk
      | ok valueExpr =>
          simp [hExpr, hty] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

/-- Each statement in the storage fragment compiles to Yul satisfying
`BridgedStmts`. -/
theorem compileStmt_storage_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | pureBinding hPure =>
      exact compileStmt_pure_binding_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hPure hOk
  | setStorage field value f slot hValue hNotMapping hFind hNotAdt =>
      exact compileStmt_setStorage_singleSlot_pure_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field value f slot
        hValue hNotMapping hFind hNotAdt hOk

/-- Each statement in the storage fragment compiles to a Yul list with no nested
function declarations. -/
theorem compileStmt_storage_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | pureBinding hPure =>
      exact compileStmt_pure_binding_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hPure hOk
  | setStorage field value f slot hValue hNotMapping hFind hNotAdt =>
      exact compileStmt_setStorage_singleSlot_pure_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field value f slot
        hValue hNotMapping hFind hNotAdt hOk

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
          inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
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

private theorem compileStmtList_noFuncDefs_of_forall
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource)
    (internalRetNames : List String) (isInternal : Bool) (P : Stmt → Prop)
    (hCompile :
      ∀ (inScopeNames : List String) {stmt : Stmt} {out : List YulStmt},
        P stmt →
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      (∀ stmt ∈ stmts, P stmt) →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      rfl
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : P head := hSource head (by simp)
              have hTailSource : ∀ stmt ∈ tail, P stmt := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              simp [
                hCompile inScopeNames hHeadSource hHead,
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail]

/-- Storage-fragment statement lists compile with no nested function declarations. -/
theorem compileStmtList_storage_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource)
    (internalRetNames : List String) (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceStorageStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_storage_fragment_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: `stop` and external/internal `return`

Two more simple compiler-emitted source statement shapes whose Yul output is
a fixed-length list of `BridgedStraightStmts`:

* `Stmt.stop` emits `[expr (call "stop" [])]`, matching
  `BridgedStraightStmt.expr_stop`.
* `Stmt.return value` with `isInternal = false` emits
  `[expr (call "mstore" [lit 0, valueExpr]), expr (call "return" [lit 0, lit 32])]`,
  matching `BridgedStraightStmt.expr_mstore` and `BridgedStraightStmt.expr_return`,
  provided `valueExpr` is a `BridgedExpr` (discharged via `compileExpr_bridgedSource`).
* `Stmt.return value` with `isInternal = true` emits
  `[assign retName valueExpr, leave]`, matching `BridgedStraightStmt.assign`
  and `BridgedStraightStmt.leave`, when a return slot name is available.
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
        inScopeNames [] .stop = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, Pure.pure, Except.pure] at hOk
  cases hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  exact BridgedStmt.straight _ BridgedStraightStmt.expr_stop

private theorem compileStmt_stop_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] .stop = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, Pure.pure, Except.pure] at hOk
  cases hOk
  simp [Native.yulStmtContainsFuncDef]

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
        (isInternal := false) inScopeNames [] (.return value) = .ok out →
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

private theorem compileStmt_return_external_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) {value : Expr} (_hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.return value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr] at hOk
  | ok valueExpr =>
      simp [hExpr, Pure.pure, Except.pure] at hOk
      subst out
      simp [Native.yulStmtContainsFuncDef]

/-- External (`isInternal = false`) `stop`/`return` source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmt_terminator_external_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceTerminatorStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | stop =>
      exact compileStmt_stop_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hOk
  | returnExternal value hValue =>
      exact compileStmt_return_external_bridged fields events errors dynamicSource
        internalRetNames inScopeNames hValue hOk

/-- External (`isInternal = false`) `stop`/`return` source statements compile
to Yul lists with no nested function declarations. -/
theorem compileStmt_terminator_external_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceTerminatorStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | stop =>
      exact compileStmt_stop_noFuncDefs fields events errors dynamicSource
        internalRetNames false inScopeNames hOk
  | returnExternal value hValue =>
      exact compileStmt_return_external_noFuncDefs fields events errors dynamicSource
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
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) [] tail with
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

/-- External `stop`/`return` statement lists compile with no nested function
declarations. -/
theorem compileStmtList_terminator_external_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceTerminatorStmts stmts → ∀ {out : List YulStmt},
      compileStmtList fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] stmts = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk; subst out; rfl
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          false inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceTerminatorStmt head := hSource head (by simp)
              have hTailSource : BridgedSourceTerminatorStmts tail := by
                intro stmt hMem; exact hSource stmt (by simp [hMem])
              simp [
                compileStmt_terminator_external_noFuncDefs fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead,
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail]

/-! ### Internal return closure

Internal functions return by assigning the compiled value to the first generated
return slot and then executing `leave`. This closes the body fragment embedded
inside EVMYulLean runtime wrappers for internal-only functions.
-/

/-- Source internal `return value` statements whose RHS is a pure
`BridgedSourceExpr`. -/
inductive BridgedSourceInternalReturnStmt : Stmt → Prop
  | returnInternal (value : Expr) (hValue : BridgedSourceExpr value) :
      BridgedSourceInternalReturnStmt (.return value)

def BridgedSourceInternalReturnStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceInternalReturnStmt stmt

/-- An internal `Stmt.return value` source statement with a `BridgedSourceExpr`
RHS compiles to `[assign retName valueExpr, leave]`, a bridged straight-line
Yul fragment. The successful compile hypothesis rules out the missing-return
slot case. -/
theorem compileStmt_return_internal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {value : Expr} (hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.return value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr] at hOk
  | ok valueExpr =>
      cases internalRetNames with
      | nil =>
          simp [hExpr] at hOk
      | cons retName rest =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          have hBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hExpr
          intro yulStmt hMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
          rcases hMem with rfl | rfl
          · exact BridgedStmt.straight _
              (BridgedStraightStmt.assign retName valueExpr hBridged)
          · exact BridgedStmt.straight _ BridgedStraightStmt.leave

theorem compileStmt_return_internal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {value : Expr} (_hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.return value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr] at hOk
  | ok valueExpr =>
      cases internalRetNames with
      | nil =>
          simp [hExpr] at hOk
      | cons retName rest =>
          simp [hExpr, Pure.pure, Except.pure] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

/-- Internal (`isInternal = true`) `return` source statements compile to Yul
lists satisfying `BridgedStmts`. -/
theorem compileStmt_internal_return_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalReturnStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnInternal value hValue =>
      exact compileStmt_return_internal_bridged fields events errors dynamicSource
        internalRetNames inScopeNames hValue hOk

/-- Internal (`isInternal = true`) `return` source statements compile to Yul
lists with no nested function declarations. -/
theorem compileStmt_internal_return_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalReturnStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnInternal value hValue =>
      exact compileStmt_return_internal_noFuncDefs fields events errors dynamicSource
        internalRetNames inScopeNames hValue hOk

/-- Lists made only of internal `return` source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_return_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalReturnStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceInternalReturnStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceInternalReturnStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_return_bridged fields events errors dynamicSource
                  internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- Lists made only of internal `return` source statements compile with no
nested function declarations. -/
theorem compileStmtList_internal_return_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalReturnStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames true BridgedSourceInternalReturnStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_internal_return_noFuncDefs fields events errors dynamicSource
        internalRetNames inScopeNames hStmt hOk)

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

private theorem revertWithMessage_chunks_noFuncDefs
    (chunks : List (List UInt8 × Nat)) :
    Native.yulStmtsContainFuncDef
      (chunks.map
        (fun chunkAndIdx =>
          YulStmt.expr (YulExpr.call "mstore"
            [YulExpr.lit (68 + chunkAndIdx.2 * 32),
              YulExpr.hex (wordFromBytes chunkAndIdx.1)]))) = false := by
  induction chunks with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk chunk idx =>
          simp [Native.yulStmtContainsFuncDef, ih]

private theorem revertWithMessage_noFuncDefs (message : String) :
    Native.yulStmtsContainFuncDef (revertWithMessage message) = false := by
  unfold revertWithMessage
  simp [Native.yulStmtContainsFuncDef, revertWithMessage_chunks_noFuncDefs]

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
        inScopeNames [] (.require cond message) = .ok out →
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

theorem compileStmt_require_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    {cond : Expr} {message : String}
    (_hFailCond :
      ∀ {failCond : YulExpr},
        compileRequireFailCond fields dynamicSource cond = .ok failCond →
        BridgedExpr failCond) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.require cond message) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hFail : compileRequireFailCond fields dynamicSource cond with
  | error err =>
      simp [hFail] at hOk
  | ok failCond =>
      simp [hFail, Pure.pure, Except.pure] at hOk
      subst out
      simp [Native.yulStmtContainsFuncDef, revertWithMessage_noFuncDefs]

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
          inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
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

/-- Lists made only of plain `require` statements whose compiled failure
conditions are bridged compile with no nested function declarations. -/
theorem compileStmtList_require_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceRequireStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceRequireStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      match hStmt with
      | BridgedSourceRequireStmt.require cond message hFailCond =>
          compileStmt_require_noFuncDefs fields events errors dynamicSource
            internalRetNames isInternal inScopeNames hFailCond hOk)

/-! ## Source statement body closure: single-slot mapping writes

`Stmt.setMapping` and `Stmt.setMappingUint` both go through
`compileMappingSlotWrite`, which, for an unpacked single-slot mapping with
`wordOffset = 0`, emits a single
`sstore(mappingSlot(.lit slot, keyExpr), valueExpr)` statement. That exact
shape already matches `BridgedStraightStmt.expr_sstore_mapping`, so the
closure is a one-step composition over the bridged key/value expressions. -/

/-- Mapping-write source statements currently known to compile to
`BridgedStmts`: single-slot, wordOffset=0 writes to a declared mapping field
whose key/value expressions are pure `BridgedSourceExpr`s. `setMapping` and
`setMappingUint` share the same emission path; both are covered. -/
inductive BridgedSourceMappingWriteStmt (fields : List Field) : Stmt → Prop
  | setMapping (field : String) {slot : Nat} {key value : Expr}
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceMappingWriteStmt fields (.setMapping field key value)
  | setMappingUint (field : String) {slot : Nat} {key value : Expr}
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceMappingWriteStmt fields (.setMappingUint field key value)

def BridgedSourceMappingWriteStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWriteStmt fields stmt

/-- Shared helper: `compileMappingSlotWrite` on a single-slot mapping with
`wordOffset = 0` and pre-compiled bridged key/value expressions produces a
`BridgedStmts` list (one `sstore(mappingSlot(lit slot, key), value)`). -/
private theorem compileMappingSlotWrite_singleSlot_bridged
    (fields : List Field) (field : String) {slot : Nat}
    (keyExpr valueExpr : YulExpr) (label : String)
    (hKey : BridgedExpr keyExpr) (hValue : BridgedExpr valueExpr)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileMappingSlotWrite fields field keyExpr valueExpr label 0 = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp [compileMappingSlotWrite, hMapping, hSlots, Pure.pure, Except.pure] at hOk
  subst hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  exact BridgedStmt.straight _
    (BridgedStraightStmt.expr_sstore_mapping (.lit slot) keyExpr valueExpr
      (BridgedExpr.lit slot) hKey hValue)

/-- A single-slot `Stmt.setMapping` source write with a pure bridged key and
value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping field key value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_singleSlot_bridged fields field keyExpr
            valueExpr "setMapping"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

/-- A single-slot `Stmt.setMappingUint` source write with a pure bridged key
and value compiles to `BridgedStmts`. Emission path is identical to
`Stmt.setMapping`, so this reuses the same mapping-write helper. -/
theorem compileStmt_setMappingUint_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingUint field key value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_singleSlot_bridged fields field keyExpr
            valueExpr "setMappingUint"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

/-- Each statement in the mapping-write fragment compiles to Yul satisfying
`BridgedStmts`. -/
theorem compileStmt_mappingWrite_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWriteStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping field hKey hValue hMapping hSlots =>
      exact compileStmt_setMapping_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey hValue hMapping hSlots hOk
  | setMappingUint field hKey hValue hMapping hSlots =>
      exact compileStmt_setMappingUint_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey hValue hMapping hSlots hOk

/-- Lists of single-slot mapping-write source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWrite_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWriteStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingWriteStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingWriteStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWrite_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: mixed function-body fragments

The fragment-specific list theorems above are useful proof bricks, but real
compiler bodies interleave pure bindings, simple storage writes, guards, and
terminators. The following predicates compose those proven fragments into a
single mixed-body closure for external and internal functions.
-/

/-- External source-body statements currently known to compile to
`BridgedStmts`: pure bindings/single-slot storage writes, plain `require`, and
external `stop`/`return`. -/
inductive BridgedSourceExternalBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | storage {stmt : Stmt} (hStmt : BridgedSourceStorageStmt fields stmt) :
      BridgedSourceExternalBodyStmt fields dynamicSource stmt
  | require {stmt : Stmt} (hStmt : BridgedSourceRequireStmt fields dynamicSource stmt) :
      BridgedSourceExternalBodyStmt fields dynamicSource stmt
  | terminator {stmt : Stmt} (hStmt : BridgedSourceTerminatorStmt stmt) :
      BridgedSourceExternalBodyStmt fields dynamicSource stmt

def BridgedSourceExternalBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceExternalBodyStmt fields dynamicSource stmt

/-- Internal source-body statements currently known to compile to
`BridgedStmts`: pure bindings/single-slot storage writes, plain `require`,
internal `return`, and `stop`. -/
inductive BridgedSourceInternalBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | storage {stmt : Stmt} (hStmt : BridgedSourceStorageStmt fields stmt) :
      BridgedSourceInternalBodyStmt fields dynamicSource stmt
  | require {stmt : Stmt} (hStmt : BridgedSourceRequireStmt fields dynamicSource stmt) :
      BridgedSourceInternalBodyStmt fields dynamicSource stmt
  | returnInternal {stmt : Stmt} (hStmt : BridgedSourceInternalReturnStmt stmt) :
      BridgedSourceInternalBodyStmt fields dynamicSource stmt
  | stop : BridgedSourceInternalBodyStmt fields dynamicSource .stop

def BridgedSourceInternalBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceInternalBodyStmt fields dynamicSource stmt

/-- Each mixed external-body statement in the currently supported fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_external_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storage hStorage =>
      exact compileStmt_storage_fragment_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hStorage hOk
  | require hRequire =>
      cases hRequire with
      | require cond message hFailCond =>
          exact compileStmt_require_bridged fields events errors dynamicSource
            internalRetNames false inScopeNames hFailCond hOk
  | terminator hTerminator =>
      exact compileStmt_terminator_external_bridged fields events errors dynamicSource
        internalRetNames inScopeNames hTerminator hOk

theorem compileStmt_external_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storage hStorage =>
      exact compileStmt_storage_fragment_noFuncDefs fields events errors dynamicSource
        internalRetNames false inScopeNames hStorage hOk
  | require hRequire =>
      cases hRequire with
      | require cond message hFailCond =>
          exact compileStmt_require_noFuncDefs fields events errors dynamicSource
            internalRetNames false inScopeNames hFailCond hOk
  | terminator hTerminator =>
      exact compileStmt_terminator_external_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hTerminator hOk

/-- Mixed external source bodies made from the currently supported fragments
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_external_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_external_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames false (BridgedSourceExternalBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_external_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

/-- Each mixed internal-body statement in the currently supported fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_internal_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storage hStorage =>
      exact compileStmt_storage_fragment_bridged fields events errors dynamicSource
        internalRetNames true inScopeNames hStorage hOk
  | require hRequire =>
      cases hRequire with
      | require cond message hFailCond =>
          exact compileStmt_require_bridged fields events errors dynamicSource
            internalRetNames true inScopeNames hFailCond hOk
  | returnInternal hReturn =>
      exact compileStmt_internal_return_bridged fields events errors dynamicSource
        internalRetNames inScopeNames hReturn hOk
  | stop =>
      exact compileStmt_stop_bridged fields events errors dynamicSource
        internalRetNames true inScopeNames hOk

theorem compileStmt_internal_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storage hStorage =>
      exact compileStmt_storage_fragment_noFuncDefs fields events errors dynamicSource
        internalRetNames true inScopeNames hStorage hOk
  | require hRequire =>
      cases hRequire with
      | require cond message hFailCond =>
          exact compileStmt_require_noFuncDefs fields events errors dynamicSource
            internalRetNames true inScopeNames hFailCond hOk
  | returnInternal hReturn =>
      exact compileStmt_internal_return_noFuncDefs fields events errors dynamicSource
        internalRetNames inScopeNames hReturn hOk
  | stop =>
      exact compileStmt_stop_noFuncDefs fields events errors dynamicSource
        internalRetNames true inScopeNames hOk

/-- Mixed internal source bodies made from the currently supported fragments
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_internal_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames true (BridgedSourceInternalBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_internal_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: one-layer `ite` composition

The mixed body-fragment predicates above cover straight-line source bodies. Real
entrypoints often wrap those bodies in `Stmt.ite`. The next increment covers one
compiler-emitted `if` layer whose branches are already mixed external/internal
body fragments.
-/

/-- External source-body statements extended with one `Stmt.ite` layer whose
condition is a bridged source expression and whose branches are mixed external
body fragments. -/
inductive BridgedSourceExternalStructuredBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt} (hStmt : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
      BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceExternalBodyStmts fields dynamicSource thenBranch)
      (hElse : BridgedSourceExternalBodyStmts fields dynamicSource elseBranch) :
      BridgedSourceExternalStructuredBodyStmt fields dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceExternalStructuredBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt

/-- Internal source-body statements extended with one `Stmt.ite` layer whose
condition is a bridged source expression and whose branches are mixed internal
body fragments. -/
inductive BridgedSourceInternalStructuredBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt} (hStmt : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
      BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceInternalBodyStmts fields dynamicSource thenBranch)
      (hElse : BridgedSourceInternalBodyStmts fields dynamicSource elseBranch) :
      BridgedSourceInternalStructuredBodyStmt fields dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceInternalStructuredBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt

/-- A one-layer external `Stmt.ite` whose branches are mixed external body
fragments compiles to bridged Yul. Empty-else `ite` emits one Yul `if`; nonempty
else emits the compiler's cached-condition `block` with two Yul `if`s. -/
theorem compileStmt_ite_external_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceExternalBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_external_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_external_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- A one-layer internal `Stmt.ite` whose branches are mixed internal body
fragments compiles to bridged Yul. -/
theorem compileStmt_ite_internal_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceInternalBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_internal_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_internal_body_fragment_bridged fields events errors
                  dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

theorem compileStmt_ite_external_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (_hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceExternalBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err => simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err => simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hThenNoFunc :=
                compileStmtList_external_body_fragment_noFuncDefs fields events
                  errors dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseNoFunc :=
                compileStmtList_external_body_fragment_noFuncDefs fields events
                  errors dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

theorem compileStmt_ite_internal_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (_hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceInternalBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err => simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err => simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hThenNoFunc :=
                compileStmtList_internal_body_fragment_noFuncDefs fields events
                  errors dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseNoFunc :=
                compileStmtList_internal_body_fragment_noFuncDefs fields events
                  errors dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

/-- Each external structured-body statement in the currently supported
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_external_structured_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmt_external_structured_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- External structured source bodies made from mixed body fragments plus one
`Stmt.ite` layer compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_external_structured_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalStructuredBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalStructuredBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_structured_body_fragment_bridged fields events
                  errors dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_external_structured_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames false
    (BridgedSourceExternalStructuredBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_external_structured_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hStmt hOk)

/-- Each internal structured-body statement in the currently supported
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_internal_structured_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmt_internal_structured_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- Internal structured source bodies made from mixed body fragments plus one
`Stmt.ite` layer compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_structured_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalStructuredBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalStructuredBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_structured_body_fragment_bridged fields events
                  errors dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_internal_structured_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames true
    (BridgedSourceInternalStructuredBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_internal_structured_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: nested `ite` composition

The one-layer predicates above are useful for shallow source bodies. This
increment closes one additional nesting level: an outer `Stmt.ite` whose
branches may themselves contain one-layer structured body statements.
-/

/-- External source-body statements extended with an outer `Stmt.ite` whose
branches are already one-layer structured external body fragments. -/
inductive BridgedSourceExternalNestedBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | structured {stmt : Stmt}
      (hStmt : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
      BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceExternalStructuredBodyStmts fields dynamicSource thenBranch)
      (hElse : BridgedSourceExternalStructuredBodyStmts fields dynamicSource elseBranch) :
      BridgedSourceExternalNestedBodyStmt fields dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceExternalNestedBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt

/-- Internal source-body statements extended with an outer `Stmt.ite` whose
branches are already one-layer structured internal body fragments. -/
inductive BridgedSourceInternalNestedBodyStmt
    (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
  | structured {stmt : Stmt}
      (hStmt : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
      BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceInternalStructuredBodyStmts fields dynamicSource thenBranch)
      (hElse : BridgedSourceInternalStructuredBodyStmts fields dynamicSource elseBranch) :
      BridgedSourceInternalNestedBodyStmt fields dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceInternalNestedBodyStmts
    (fields : List Field) (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt

/-- An outer external `Stmt.ite` whose branches are one-layer structured
external body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_external_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalStructuredBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceExternalStructuredBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_external_structured_body_fragment_bridged fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_external_structured_body_fragment_bridged fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- An outer internal `Stmt.ite` whose branches are one-layer structured
internal body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_internal_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalStructuredBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceInternalStructuredBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_internal_structured_body_fragment_bridged fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_internal_structured_body_fragment_bridged fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

theorem compileStmt_ite_external_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (_hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalStructuredBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceExternalStructuredBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err => simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err => simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hThenNoFunc :=
                compileStmtList_external_structured_body_fragment_noFuncDefs fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseNoFunc :=
                compileStmtList_external_structured_body_fragment_noFuncDefs fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

theorem compileStmt_ite_internal_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (_hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalStructuredBodyStmts fields dynamicSource thenBranch)
    (hElse : BridgedSourceInternalStructuredBodyStmts fields dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err => simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err => simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hThenNoFunc :=
                compileStmtList_internal_structured_body_fragment_noFuncDefs fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseNoFunc :=
                compileStmtList_internal_structured_body_fragment_noFuncDefs fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty, Pure.pure,
                  Except.pure] at hOk
                subst out
                simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

theorem compileStmt_external_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_external_structured_body_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_nested_body_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmt_external_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_external_structured_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_nested_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmtList_external_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalNestedBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalNestedBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_nested_body_fragment_bridged fields events
                  errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_external_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames false
    (BridgedSourceExternalNestedBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_external_nested_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

theorem compileStmt_internal_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_internal_structured_body_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_nested_body_fragment_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmt_internal_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_internal_structured_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_nested_body_fragment_noFuncDefs fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

theorem compileStmtList_internal_nested_body_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalNestedBodyStmt fields dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalNestedBodyStmts fields dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_nested_body_fragment_bridged fields events
                  errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_internal_nested_body_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames true
    (BridgedSourceInternalNestedBodyStmt fields dynamicSource)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_internal_nested_body_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: recursive `ite` composition

The fixed-depth predicates above are useful proof milestones, but generated
entrypoint bodies can nest conditionals beyond a single manually enumerated
level. The following mutual predicates encode the supported mixed body fragment
closed recursively under `Stmt.ite`; the list predicate is inductive rather than
defined with `∀ stmt ∈ stmts` so Lean provides the induction hypotheses needed
for nested branch lists.
-/

mutual
  /-- External source-body statements made from the mixed body fragment and
  recursively nested `Stmt.ite` wrappers. -/
  inductive BridgedSourceExternalRecursiveBodyStmt
      (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
        BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceExternalRecursiveBodyStmts fields dynamicSource thenBranch)
        (hElse : BridgedSourceExternalRecursiveBodyStmts fields dynamicSource elseBranch) :
        BridgedSourceExternalRecursiveBodyStmt fields dynamicSource
          (.ite cond thenBranch elseBranch)

  /-- External source-body lists made from recursively bridged statements. -/
  inductive BridgedSourceExternalRecursiveBodyStmts
      (fields : List Field) (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceExternalRecursiveBodyStmts fields dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceExternalRecursiveBodyStmt fields dynamicSource head)
        (hTail : BridgedSourceExternalRecursiveBodyStmts fields dynamicSource tail) :
        BridgedSourceExternalRecursiveBodyStmts fields dynamicSource (head :: tail)
end

mutual
  /-- Internal source-body statements made from the mixed body fragment and
  recursively nested `Stmt.ite` wrappers. -/
  inductive BridgedSourceInternalRecursiveBodyStmt
      (fields : List Field) (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
        BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceInternalRecursiveBodyStmts fields dynamicSource thenBranch)
        (hElse : BridgedSourceInternalRecursiveBodyStmts fields dynamicSource elseBranch) :
        BridgedSourceInternalRecursiveBodyStmt fields dynamicSource
          (.ite cond thenBranch elseBranch)

  /-- Internal source-body lists made from recursively bridged statements. -/
  inductive BridgedSourceInternalRecursiveBodyStmts
      (fields : List Field) (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceInternalRecursiveBodyStmts fields dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceInternalRecursiveBodyStmt fields dynamicSource head)
        (hTail : BridgedSourceInternalRecursiveBodyStmts fields dynamicSource tail) :
        BridgedSourceInternalRecursiveBodyStmts fields dynamicSource (head :: tail)
end

mutual
  theorem compileStmt_external_recursive_body_fragment_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_external_body_fragment_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames false inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_external_recursive_body_fragment_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_external_recursive_body_fragment_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil

  theorem compileStmtList_external_recursive_body_fragment_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames false inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_external_recursive_body_fragment_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_external_recursive_body_fragment_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

mutual
  theorem compileStmt_external_recursive_body_fragment_noFuncDefs
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmt = .ok out →
          Native.yulStmtsContainFuncDef out = false := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_external_body_fragment_noFuncDefs fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch _ hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err => simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false inScopeNames [] thenBranch with
            | error err => simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames false inScopeNames [] elseBranch with
                | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hThenNoFunc :=
                      compileStmtList_external_recursive_body_fragment_noFuncDefs fields
                        events errors dynamicSource internalRetNames hThen inScopeNames
                        hThenCompile
                    have hElseNoFunc :=
                      compileStmtList_external_recursive_body_fragment_noFuncDefs fields
                        events errors dynamicSource internalRetNames hElse inScopeNames
                        hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

  theorem compileStmtList_external_recursive_body_fragment_noFuncDefs
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmts = .ok out →
          Native.yulStmtsContainFuncDef out = false := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        rfl
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames false inScopeNames [] head with
        | error err => simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
            | error err => simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                simp [
                  compileStmt_external_recursive_body_fragment_noFuncDefs fields events
                    errors dynamicSource internalRetNames inScopeNames hHead hHeadCompile,
                  compileStmtList_external_recursive_body_fragment_noFuncDefs fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile]
end

mutual
  theorem compileStmt_internal_recursive_body_fragment_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_internal_body_fragment_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames true inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_internal_recursive_body_fragment_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_internal_recursive_body_fragment_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil

  theorem compileStmtList_internal_recursive_body_fragment_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames true inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_internal_recursive_body_fragment_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_internal_recursive_body_fragment_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

mutual
  theorem compileStmt_internal_recursive_body_fragment_noFuncDefs
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmt = .ok out →
          Native.yulStmtsContainFuncDef out = false := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_internal_body_fragment_noFuncDefs fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch _ hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err => simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true inScopeNames [] thenBranch with
            | error err => simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames true inScopeNames [] elseBranch with
                | error err => simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hThenNoFunc :=
                      compileStmtList_internal_recursive_body_fragment_noFuncDefs fields
                        events errors dynamicSource internalRetNames hThen inScopeNames
                        hThenCompile
                    have hElseNoFunc :=
                      compileStmtList_internal_recursive_body_fragment_noFuncDefs fields
                        events errors dynamicSource internalRetNames hElse inScopeNames
                        hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      simp [Native.yulStmtContainsFuncDef, hThenNoFunc]
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      simp [Native.yulStmtContainsFuncDef, hThenNoFunc, hElseNoFunc]

  theorem compileStmtList_internal_recursive_body_fragment_noFuncDefs
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmts = .ok out →
          Native.yulStmtsContainFuncDef out = false := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        rfl
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames true inScopeNames [] head with
        | error err => simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
            | error err => simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                simp [
                  compileStmt_internal_recursive_body_fragment_noFuncDefs fields events
                    errors dynamicSource internalRetNames inScopeNames hHead hHeadCompile,
                  compileStmtList_internal_recursive_body_fragment_noFuncDefs fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile]
end

/-! ## Source statement body closure: direct memory writes (`mstore`/`tstore`)

The `Stmt.mstore` and `Stmt.tstore` source statements compile directly to a
single Yul `mstore`/`tstore` call whose arguments are the compiled offset and
value expressions. When both sides are pure bridged source expressions, the
emitted statement satisfies `BridgedStraightStmt` via `expr_mstore` / `expr_tstore`.
-/

/-- Direct memory/transient-memory write source statements whose offset and
value are pure bridged source expressions. -/
inductive BridgedSourceMemoryWriteStmt : Stmt → Prop
  | mstore (offset value : Expr)
      (hOffset : BridgedSourceExpr offset) (hValue : BridgedSourceExpr value) :
      BridgedSourceMemoryWriteStmt (.mstore offset value)
  | tstore (offset value : Expr)
      (hOffset : BridgedSourceExpr offset) (hValue : BridgedSourceExpr value) :
      BridgedSourceMemoryWriteStmt (.tstore offset value)

def BridgedSourceMemoryWriteStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMemoryWriteStmt stmt

/-- A direct `mstore`/`tstore` source statement whose offset and value are
bridged source expressions compiles to a single-statement Yul list satisfying
`BridgedStmts`. -/
theorem compileStmt_memoryWrite_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMemoryWriteStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | mstore offset value hOffset hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hOExpr : compileExpr fields dynamicSource offset with
      | error err => simp [hOExpr] at hOk
      | ok offsetExpr =>
          simp [hOExpr] at hOk
          cases hVExpr : compileExpr fields dynamicSource value with
          | error err => simp [hVExpr] at hOk
          | ok valueExpr =>
              simp [hVExpr, Pure.pure, Except.pure] at hOk
              subst out
              have hBO : BridgedExpr offsetExpr :=
                compileExpr_bridgedSource fields dynamicSource hOffset hOExpr
              have hBV : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hVExpr
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_mstore offsetExpr valueExpr hBO hBV)
  | tstore offset value hOffset hValue =>
      simp only [compileStmt, bind, Except.bind] at hOk
      cases hOExpr : compileExpr fields dynamicSource offset with
      | error err => simp [hOExpr] at hOk
      | ok offsetExpr =>
          simp [hOExpr] at hOk
          cases hVExpr : compileExpr fields dynamicSource value with
          | error err => simp [hVExpr] at hOk
          | ok valueExpr =>
              simp [hVExpr, Pure.pure, Except.pure] at hOk
              subst out
              have hBO : BridgedExpr offsetExpr :=
                compileExpr_bridgedSource fields dynamicSource hOffset hOExpr
              have hBV : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hVExpr
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_tstore offsetExpr valueExpr hBO hBV)

/-- Lists made only of direct `mstore`/`tstore` source statements with bridged
source arguments compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_memoryWrite_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMemoryWriteStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMemoryWriteStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMemoryWriteStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_memoryWrite_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: bounded `forEach` loops

The `Stmt.forEach varName count body` source statement compiles to a single
`YulStmt.for_` whose init, cond, and post are fixed shapes built from literal
`0` / `1` and the compiled `count` expression. Given a bridged source `count`
and a forward hypothesis that the body's compiled Yul is `BridgedStmts`, the
forEach statement itself is `BridgedStmts`.
-/

/-- A `Stmt.forEach varName count body` source statement compiles to a Yul
`.for_` wrapping the body's compiled output. When `count` is bridged and the
body's `compileStmtList` output is bridged, the whole forEach is
`BridgedStmts`. -/
theorem compileStmt_forEach_with_bridged_body
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (varName : String) (count : Expr) (body : List Stmt)
    (hCount : BridgedSourceExpr count)
    (hBody : ∀ {out : List YulStmt},
      compileStmtList fields events errors dynamicSource internalRetNames
        isInternal (varName :: inScopeNames) [] body = .ok out →
      BridgedStmts out) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.forEach varName count body) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCExpr : compileExpr fields dynamicSource count with
  | error err => simp [hCExpr] at hOk
  | ok countExpr =>
      simp [hCExpr] at hOk
      cases hBodyOk : compileStmtList fields events errors dynamicSource
          internalRetNames isInternal (varName :: inScopeNames) [] body with
      | error err => simp [hBodyOk] at hOk
      | ok bodyOut =>
          simp [hBodyOk, Pure.pure, Except.pure] at hOk
          subst out
          have hBC : BridgedExpr countExpr :=
            compileExpr_bridgedSource fields dynamicSource hCount hCExpr
          have hBBody : BridgedStmts bodyOut := hBody hBodyOk
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          refine BridgedStmt.for_ _ _ _ _ ?_ ?_ ?_ ?_
          · -- init: [YulStmt.let_ varName (YulExpr.lit 0)]
            intro stmt hMemInit
            simp only [List.mem_singleton] at hMemInit
            subst stmt
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ varName (.lit 0) (BridgedExpr.lit 0))
          · -- cond: lt(ident varName, countExpr)
            refine BridgedExpr.call "lt" _ (Or.inl (by simp [bridgedBuiltins])) ?_
            intro arg hMemArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemArg
            rcases hMemArg with rfl | rfl
            · exact BridgedExpr.ident varName
            · exact hBC
          · -- post: [YulStmt.assign varName (add(ident varName, lit 1))]
            intro stmt hMemPost
            simp only [List.mem_singleton] at hMemPost
            subst stmt
            refine BridgedStmt.straight _
              (BridgedStraightStmt.assign varName _ ?_)
            refine BridgedExpr.call "add" _ (Or.inl (by simp [bridgedBuiltins])) ?_
            intro arg hMemArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemArg
            rcases hMemArg with rfl | rfl
            · exact BridgedExpr.ident varName
            · exact BridgedExpr.lit 1
          · -- body
            exact hBBody

/-! ## Source statement body closure: zero-argument custom errors

`Stmt.revertError errorName []` compiles via `revertWithCustomError` to a
single Yul `.block` containing `mload` (frame pointer load), signature-word
`mstore`s, `keccak256` of the signature, `shl`/`shr` selector extraction,
a `mstore` of the selector, `let __err_tail = 0`, and a final `revert`.
Every statement inside the block satisfies `BridgedStraightStmt`, so the
block satisfies `BridgedStmt`.

`Stmt.requireError cond errorName []` additionally wraps the block inside a
Yul `if_` whose condition is the compiled fail-cond expression.

Closure for custom errors with arguments requires additional reasoning about
`attachOffsets`, `encodeStaticCustomErrorArg`, and per-parameter ABI
encoding, which is out of scope for this increment.
-/

/-- Every element of the signature-bytes store list has shape
`expr (mstore [add [ident "__err_ptr", lit], hex])` and is therefore
`BridgedStmt`. -/
private theorem sigStores_bridged (sigBytes : List UInt8) :
    ∀ s ∈ (chunkBytes32 sigBytes).zipIdx.map
        (fun (chunk, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
            YulExpr.hex (wordFromBytes chunk)])),
      BridgedStmt s := by
  intro s hMem
  simp only [List.mem_map] at hMem
  rcases hMem with ⟨chunkAndIdx, _hChunk, rfl⟩
  rcases chunkAndIdx with ⟨chunk, idx⟩
  refine BridgedStmt.straight _ (BridgedStraightStmt.expr_mstore _ _ ?_ ?_)
  · refine BridgedExpr.call "add" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hArg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
    rcases hArg with rfl | rfl
    · exact BridgedExpr.ident "__err_ptr"
    · exact BridgedExpr.lit (idx * 32)
  · exact BridgedExpr.hex (wordFromBytes chunk)

/-- A zero-argument custom error reverts via a `.block` whose body is made
entirely of bridged straight-line statements. -/
private theorem revertWithCustomError_zero_bridged
    (dynamicSource : DynamicDataSource) (errorDef : ErrorDef)
    (hParams : errorDef.params = []) :
    ∀ {out : List YulStmt},
      revertWithCustomError dynamicSource errorDef [] [] = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hNil : (revertWithCustomError dynamicSource errorDef [] []) = .ok
      [YulStmt.block
        ([YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
          ((chunkBytes32 (bytesFromString (errorSignature errorDef))).zipIdx.map
            (fun (chunk, idx) =>
              YulStmt.expr (YulExpr.call "mstore" [
                YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
                YulExpr.hex (wordFromBytes chunk)]))) ++
          [YulStmt.let_ "__err_hash"
              (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr",
                YulExpr.lit (bytesFromString (errorSignature errorDef)).length]),
            YulStmt.let_ "__err_selector"
              (YulExpr.call "shl" [YulExpr.lit selectorShift,
                YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.ident "__err_hash"]]),
            YulStmt.expr (YulExpr.call "mstore"
              [YulExpr.lit 0, YulExpr.ident "__err_selector"]),
            YulStmt.let_ "__err_tail" (YulExpr.lit 0)] ++
          [YulStmt.expr (YulExpr.call "revert"
            [YulExpr.lit 0,
              YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]])])] := by
    unfold revertWithCustomError
    simp [hParams]
    rfl
  rw [hNil] at hOk
  injection hOk with hOk
  subst out
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  refine BridgedStmt.block _ ?_
  intro inner hInner
  -- The block body: [storePtr] ++ sigStores ++ [hashStmt, selectorStmt,
  -- selectorStore, tailInit] ++ [revertStmt]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hInner
  rcases hInner with ((hStore | hSig) | hMid) | hRevert
  · -- storePtr: let __err_ptr = mload(freeMemoryPointer)
    subst hStore
    refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
    refine BridgedExpr.call "mload" _
      (Or.inr (Or.inr (Or.inl rfl))) ?_
    intro arg hArg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
    rcases hArg with rfl
    exact BridgedExpr.lit freeMemoryPointer
  · -- sigStores element
    exact sigStores_bridged _ inner hSig
  · -- middle four: hashStmt | selectorStmt | selectorStore | tailInit
    rcases hMid with rfl | rfl | rfl | rfl
    · -- hashStmt: let __err_hash = keccak256(ident "__err_ptr", lit sigBytes.length)
      refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
      refine BridgedExpr.call "keccak256" _
        (Or.inr (Or.inr (Or.inr rfl))) ?_
      intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with rfl | rfl
      · exact BridgedExpr.ident "__err_ptr"
      · exact BridgedExpr.lit _
    · -- selectorStmt: let __err_selector = shl(selectorShift, shr(selectorShift, ident))
      refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
      refine BridgedExpr.call "shl" _
        (Or.inl (by simp [bridgedBuiltins])) ?_
      intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with rfl | rfl
      · exact BridgedExpr.lit selectorShift
      · refine BridgedExpr.call "shr" _
          (Or.inl (by simp [bridgedBuiltins])) ?_
        intro arg2 hArg2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg2
        rcases hArg2 with rfl | rfl
        · exact BridgedExpr.lit selectorShift
        · exact BridgedExpr.ident "__err_hash"
    · -- selectorStore: mstore(lit 0, ident "__err_selector")
      refine BridgedStmt.straight _ (BridgedStraightStmt.expr_mstore _ _ ?_ ?_)
      · exact BridgedExpr.lit 0
      · exact BridgedExpr.ident "__err_selector"
    · -- tailInit: let __err_tail = lit 0
      refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
      exact BridgedExpr.lit _
  · -- revertStmt: expr revert(lit 0, add [lit 4, ident "__err_tail"])
    subst hRevert
    exact BridgedStmt.straight _ (BridgedStraightStmt.expr_revert _ _)

/-- Source custom-error statements with zero parameters whose call-site looks
up a defined `ErrorDef` with no parameters. -/
inductive BridgedSourceCustomErrorStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | revertError (errorName : String)
      (errorDef : ErrorDef)
      (hLookup : errors.find? (·.name == errorName) = some errorDef)
      (hZeroParams : errorDef.params = []) :
      BridgedSourceCustomErrorStmt fields errors dynamicSource
        (.revertError errorName [])
  | requireError (cond : Expr) (errorName : String)
      (errorDef : ErrorDef)
      (hLookup : errors.find? (·.name == errorName) = some errorDef)
      (hZeroParams : errorDef.params = [])
      (hFailCond : ∀ {failCond : YulExpr},
        compileRequireFailCond fields dynamicSource cond = .ok failCond →
        BridgedExpr failCond) :
      BridgedSourceCustomErrorStmt fields errors dynamicSource
        (.requireError cond errorName [])

def BridgedSourceCustomErrorStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceCustomErrorStmt fields errors dynamicSource stmt

/-- A zero-arg `Stmt.revertError` compiles to a bridged Yul statement list. -/
theorem compileStmt_revertError_zero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    {errorName : String} {errorDef : ErrorDef}
    (hLookup : errors.find? (·.name == errorName) = some errorDef)
    (hZeroParams : errorDef.params = []) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.revertError errorName []) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind, hLookup, compileExprList,
    Pure.pure, Except.pure] at hOk
  exact revertWithCustomError_zero_bridged dynamicSource errorDef hZeroParams hOk

/-- A zero-arg `Stmt.requireError` compiles to a bridged Yul statement list
when its failure condition is bridged. -/
theorem compileStmt_requireError_zero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    {cond : Expr} {errorName : String} {errorDef : ErrorDef}
    (hLookup : errors.find? (·.name == errorName) = some errorDef)
    (hZeroParams : errorDef.params = [])
    (hFailCond : ∀ {failCond : YulExpr},
      compileRequireFailCond fields dynamicSource cond = .ok failCond →
      BridgedExpr failCond) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.requireError cond errorName []) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hFail : compileRequireFailCond fields dynamicSource cond with
  | error err => simp [hFail] at hOk
  | ok failCond =>
      simp [hFail, hLookup, compileExprList, Pure.pure, Except.pure] at hOk
      cases hRevert : revertWithCustomError dynamicSource errorDef [] [] with
      | error err => simp [hRevert] at hOk
      | ok revertStmts =>
          simp [hRevert] at hOk
          subst out
          have hBRevert : BridgedStmts revertStmts :=
            revertWithCustomError_zero_bridged dynamicSource errorDef hZeroParams hRevert
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.if_ failCond revertStmts
            (hFailCond hFail) hBRevert

/-- Zero-arg custom-error statements compile to bridged Yul statement lists. -/
theorem compileStmt_customError_zero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    {stmt : Stmt}
    (hStmt : BridgedSourceCustomErrorStmt fields errors dynamicSource stmt) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] stmt = .ok out →
      BridgedStmts out := by
  cases hStmt with
  | revertError errorName errorDef hLookup hZeroParams =>
      exact compileStmt_revertError_zero_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hLookup hZeroParams
  | requireError cond errorName errorDef hLookup hZeroParams hFailCond =>
      exact compileStmt_requireError_zero_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hLookup hZeroParams hFailCond

/-- A list made entirely of zero-arg custom-error source statements compiles
to a Yul list satisfying `BridgedStmts`. -/
theorem compileStmtList_customError_zero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceCustomErrorStmts fields errors dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceCustomErrorStmt fields errors dynamicSource head :=
                hSource head (by simp)
              have hBHead : BridgedStmts headOut :=
                compileStmt_customError_zero_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead
              have hTailSource : BridgedSourceCustomErrorStmts fields errors dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              have hBTail : BridgedStmts tailOut :=
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail
              intro stmt hMem
              simp only [List.mem_append] at hMem
              rcases hMem with h | h
              · exact hBHead stmt h
              · exact hBTail stmt h

/-!
## Mixed body with zero-arg custom errors

Extended body predicates that compose the existing mixed-body fragment
(`BridgedSourceExternalBodyStmt` / `BridgedSourceInternalBodyStmt`) with
zero-argument `revertError`/`requireError` calls. Pure addition — the
original predicates remain untouched so existing callers are unaffected.
-/

/-- External body statement predicate extended to admit zero-arg custom
errors, direct `mstore`/`tstore` memory writes, and single-slot mapping
writes alongside the existing `storage`/`require`/`terminator` cases. -/
inductive BridgedSourceExternalBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
      BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | customError {stmt : Stmt}
      (hStmt : BridgedSourceCustomErrorStmt fields errors dynamicSource stmt) :
      BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | memoryWrite {stmt : Stmt} (hStmt : BridgedSourceMemoryWriteStmt stmt) :
      BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | mappingWrite {stmt : Stmt} (hStmt : BridgedSourceMappingWriteStmt fields stmt) :
      BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt

def BridgedSourceExternalBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Internal body statement predicate extended to admit zero-arg custom
errors, direct `mstore`/`tstore` memory writes, and single-slot mapping
writes alongside the existing `storage`/`require`/`returnInternal`/`stop` cases. -/
inductive BridgedSourceInternalBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
      BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | customError {stmt : Stmt}
      (hStmt : BridgedSourceCustomErrorStmt fields errors dynamicSource stmt) :
      BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | memoryWrite {stmt : Stmt} (hStmt : BridgedSourceMemoryWriteStmt stmt) :
      BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt
  | mappingWrite {stmt : Stmt} (hStmt : BridgedSourceMappingWriteStmt fields stmt) :
      BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt

def BridgedSourceInternalBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Each statement in the extended external body fragment compiles to
`BridgedStmts`. -/
theorem compileStmt_external_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | customError hCustom =>
      exact compileStmt_customError_zero_bridged fields events errors
        dynamicSource internalRetNames false inScopeNames hCustom hOk
  | memoryWrite hMem =>
      exact compileStmt_memoryWrite_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hMem hOk
  | mappingWrite hMap =>
      exact compileStmt_mappingWrite_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hMap hOk

/-- Each statement in the extended internal body fragment compiles to
`BridgedStmts`. -/
theorem compileStmt_internal_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_fragment_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | customError hCustom =>
      exact compileStmt_customError_zero_bridged fields events errors
        dynamicSource internalRetNames true inScopeNames hCustom hOk
  | memoryWrite hMem =>
      exact compileStmt_memoryWrite_bridged fields events errors dynamicSource
        internalRetNames true inScopeNames hMem hOk
  | mappingWrite hMap =>
      exact compileStmt_mappingWrite_bridged fields events errors dynamicSource
        internalRetNames true inScopeNames hMap hOk

/-- Mixed external source bodies (storage/require/terminator + zero-arg
custom errors) compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_external_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro _ hMem
      exact (List.not_mem_nil hMem).elim
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          false inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hBHead : BridgedStmts headOut :=
                compileStmt_external_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead
              have hTailSource :
                  BridgedSourceExternalBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              have hBTail : BridgedStmts tailOut :=
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail
              intro stmt hMem
              simp only [List.mem_append] at hMem
              rcases hMem with h | h
              · exact hBHead stmt h
              · exact hBTail stmt h

/-- Mixed internal source bodies (storage/require/returnInternal/stop +
zero-arg custom errors) compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro _ hMem
      exact (List.not_mem_nil hMem).elim
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          true inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hBHead : BridgedStmts headOut :=
                compileStmt_internal_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead
              have hTailSource :
                  BridgedSourceInternalBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              have hBTail : BridgedStmts tailOut :=
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail
              intro stmt hMem
              simp only [List.mem_append] at hMem
              rcases hMem with h | h
              · exact hBHead stmt h
              · exact hBTail stmt h

/-- A one-layer external `Stmt.ite` whose branches are mixed external
with-errors body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_external_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalBodyWithErrorsStmts fields errors
      dynamicSource thenBranch)
    (hElse : BridgedSourceExternalBodyWithErrorsStmts fields errors
      dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_external_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_external_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- A one-layer internal `Stmt.ite` whose branches are mixed internal
with-errors body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_internal_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalBodyWithErrorsStmts fields errors
      dynamicSource thenBranch)
    (hElse : BridgedSourceInternalBodyWithErrorsStmts fields errors
      dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_internal_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames thenBranch inScopeNames hThen
                  hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_internal_body_with_errors_bridged fields events errors
                  dynamicSource internalRetNames elseBranch inScopeNames hElse
                  hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- External with-errors body statements extended with one `Stmt.ite` layer
whose condition is a bridged source expression and whose branches are mixed
external with-errors body fragments. -/
inductive BridgedSourceExternalStructuredBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
      BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceExternalBodyWithErrorsStmts fields errors
        dynamicSource thenBranch)
      (hElse : BridgedSourceExternalBodyWithErrorsStmts fields errors
        dynamicSource elseBranch) :
      BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceExternalStructuredBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Internal with-errors body statements extended with one `Stmt.ite` layer
whose condition is a bridged source expression and whose branches are mixed
internal with-errors body fragments. -/
inductive BridgedSourceInternalStructuredBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
      BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceInternalBodyWithErrorsStmts fields errors
        dynamicSource thenBranch)
      (hElse : BridgedSourceInternalBodyWithErrorsStmts fields errors
        dynamicSource elseBranch) :
      BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceInternalStructuredBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Each external with-errors structured-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_external_structured_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- External structured with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_external_structured_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- Each internal with-errors structured-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_internal_structured_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- Internal structured with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_structured_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ### Nested with-errors body closure (two `Stmt.ite` layers)

The structured with-errors predicate above covers one `Stmt.ite` layer around
plain with-errors body fragments. This increment adds one further nesting
level: an outer `Stmt.ite` whose branches are already-proven structured
with-errors lists.
-/

/-- External with-errors body statements extended with an outer `Stmt.ite`
whose branches are already one-layer structured with-errors body fragments. -/
inductive BridgedSourceExternalNestedBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | structured {stmt : Stmt}
      (hStmt : BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
        dynamicSource stmt) :
      BridgedSourceExternalNestedBodyWithErrorsStmt fields errors dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource thenBranch)
      (hElse : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource elseBranch) :
      BridgedSourceExternalNestedBodyWithErrorsStmt fields errors dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceExternalNestedBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Internal with-errors body statements extended with an outer `Stmt.ite`
whose branches are already one-layer structured with-errors body fragments. -/
inductive BridgedSourceInternalNestedBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | structured {stmt : Stmt}
      (hStmt : BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
        dynamicSource stmt) :
      BridgedSourceInternalNestedBodyWithErrorsStmt fields errors dynamicSource stmt
  | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
      (hCond : BridgedSourceExpr cond)
      (hThen : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource thenBranch)
      (hElse : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
        dynamicSource elseBranch) :
      BridgedSourceInternalNestedBodyWithErrorsStmt fields errors dynamicSource
        (.ite cond thenBranch elseBranch)

def BridgedSourceInternalNestedBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors dynamicSource stmt

/-- An outer external `Stmt.ite` whose branches are one-layer structured
with-errors body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_external_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource thenBranch)
    (hElse : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames false inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames false inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_external_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_external_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- An outer internal `Stmt.ite` whose branches are one-layer structured
with-errors body fragments compiles to bridged Yul. -/
theorem compileStmt_ite_internal_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String)
    {cond : Expr} {thenBranch elseBranch : List Stmt}
    (hCond : BridgedSourceExpr cond)
    (hThen : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource thenBranch)
    (hElse : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource elseBranch) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.ite cond thenBranch elseBranch) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hCondExpr : compileExpr fields dynamicSource cond with
  | error err =>
      simp [hCondExpr] at hOk
  | ok condExpr =>
      cases hThenCompile : compileStmtList fields events errors dynamicSource
          internalRetNames true inScopeNames [] thenBranch with
      | error err =>
          simp [hCondExpr, hThenCompile] at hOk
      | ok thenOut =>
          cases hElseCompile : compileStmtList fields events errors dynamicSource
              internalRetNames true inScopeNames [] elseBranch with
          | error err =>
              simp [hCondExpr, hThenCompile, hElseCompile] at hOk
          | ok elseOut =>
              have hCondBridged : BridgedExpr condExpr :=
                compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
              have hThenBridged : BridgedStmts thenOut :=
                compileStmtList_internal_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames thenBranch
                  inScopeNames hThen hThenCompile
              have hElseBridged : BridgedStmts elseOut :=
                compileStmtList_internal_structured_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames elseBranch
                  inScopeNames hElse hElseCompile
              by_cases hEmpty : elseBranch.isEmpty
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
              · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                  Pure.pure, Except.pure] at hOk
                subst out
                intro yulStmt hMem
                simp only [List.mem_singleton] at hMem
                subst yulStmt
                refine BridgedStmt.block _ ?_
                intro blockStmt hBlockMem
                simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                rcases hBlockMem with rfl | rfl | rfl | hNil
                · exact BridgedStmt.straight _
                    (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                · exact BridgedStmt.if_ _ elseOut
                    (bridgedExpr_iszero_ident _) hElseBridged
                · cases hNil

/-- Each external with-errors nested-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_external_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_external_structured_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_external_nested_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- External nested with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_external_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_nested_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- Each internal with-errors nested-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_internal_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | structured hStructured =>
      exact compileStmt_internal_structured_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hStructured hOk
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact compileStmt_ite_internal_nested_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames inScopeNames hCond hThen hElse hOk

/-- Internal nested with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_nested_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_nested_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ### `forEach`-wrapped with-errors body closure

Extends with-errors body closure under one outer `Stmt.forEach` layer whose
body is itself a with-errors body list. Mirrors the `ite`-structured pattern
but reuses `compileStmt_forEach_with_bridged_body` as the per-statement
building block so the outer `Stmt.forEach` compile shape (a Yul `.for_` with
init/cond/post scaffolding) is handled once.
-/

/-- External with-errors body statements extended with one outer
`Stmt.forEach varName count body` whose body is itself a with-errors body
list. -/
inductive BridgedSourceExternalForEachBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
      BridgedSourceExternalForEachBodyWithErrorsStmt fields errors dynamicSource stmt
  | forEach (varName : String) (count : Expr) (body : List Stmt)
      (hCount : BridgedSourceExpr count)
      (hBody : BridgedSourceExternalBodyWithErrorsStmts fields errors
        dynamicSource body) :
      BridgedSourceExternalForEachBodyWithErrorsStmt fields errors dynamicSource
        (.forEach varName count body)

def BridgedSourceExternalForEachBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceExternalForEachBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Internal with-errors body statements extended with one outer
`Stmt.forEach varName count body` whose body is itself a with-errors body
list. -/
inductive BridgedSourceInternalForEachBodyWithErrorsStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
      BridgedSourceInternalForEachBodyWithErrorsStmt fields errors dynamicSource stmt
  | forEach (varName : String) (count : Expr) (body : List Stmt)
      (hCount : BridgedSourceExpr count)
      (hBody : BridgedSourceInternalBodyWithErrorsStmts fields errors
        dynamicSource body) :
      BridgedSourceInternalForEachBodyWithErrorsStmt fields errors dynamicSource
        (.forEach varName count body)

def BridgedSourceInternalForEachBodyWithErrorsStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceInternalForEachBodyWithErrorsStmt fields errors dynamicSource stmt

/-- Each external with-errors forEach-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_external_forEach_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceExternalForEachBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | forEach varName count body hCount hBody =>
      refine compileStmt_forEach_with_bridged_body fields events errors
        dynamicSource internalRetNames false inScopeNames varName count body
        hCount ?_ hOk
      intro bodyOut hBodyOk
      exact compileStmtList_external_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames body (varName :: inScopeNames)
        hBody hBodyOk

/-- External forEach-wrapped with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_external_forEach_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalForEachBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalForEachBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceExternalForEachBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_external_forEach_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- Each internal with-errors forEach-body statement compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_internal_forEach_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceInternalForEachBodyWithErrorsStmt fields errors
        dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | forEach varName count body hCount hBody =>
      refine compileStmt_forEach_with_bridged_body fields events errors
        dynamicSource internalRetNames true inScopeNames varName count body
        hCount ?_ hOk
      intro bodyOut hBodyOk
      exact compileStmtList_internal_body_with_errors_bridged fields events
        errors dynamicSource internalRetNames body (varName :: inScopeNames)
        hBody hBodyOk

/-- Internal forEach-wrapped with-errors source bodies compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_forEach_body_with_errors_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalForEachBodyWithErrorsStmts fields errors
        dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalForEachBodyWithErrorsStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceInternalForEachBodyWithErrorsStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_internal_forEach_body_with_errors_bridged fields
                  events errors dynamicSource internalRetNames inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ### Recursive with-errors body closure

Mutual stmt/list predicates that close with-errors body fragments under
arbitrarily deep `Stmt.ite` nesting as well as `Stmt.forEach` wrappers (both
constructors recurse back through the paired list predicate, so nesting
depth and interleaving of `ite`/`forEach` layers is unconstrained). The list
predicate is inductive rather than a `∀ stmt ∈ stmts` alias so Lean provides
the induction hypotheses needed for nested branch lists.
-/

mutual
  /-- External with-errors body statements made from the mixed with-errors
  fragment and recursively nested `Stmt.ite` wrappers. -/
  inductive BridgedSourceExternalRecursiveBodyWithErrorsStmt
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceExternalBodyWithErrorsStmt fields errors
          dynamicSource stmt) :
        BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource thenBranch)
        (hElse : BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource elseBranch) :
        BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource (.ite cond thenBranch elseBranch)
    | forEach (varName : String) (count : Expr) (body : List Stmt)
        (hCount : BridgedSourceExpr count)
        (hBody : BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource body) :
        BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource (.forEach varName count body)

  /-- External with-errors body lists made from recursively bridged
  with-errors statements. -/
  inductive BridgedSourceExternalRecursiveBodyWithErrorsStmts
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
        dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head)
        (hTail : BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource tail) :
        BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource (head :: tail)
end

mutual
  /-- Internal with-errors body statements made from the mixed with-errors
  fragment and recursively nested `Stmt.ite` wrappers. -/
  inductive BridgedSourceInternalRecursiveBodyWithErrorsStmt
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceInternalBodyWithErrorsStmt fields errors
          dynamicSource stmt) :
        BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource thenBranch)
        (hElse : BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource elseBranch) :
        BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource (.ite cond thenBranch elseBranch)
    | forEach (varName : String) (count : Expr) (body : List Stmt)
        (hCount : BridgedSourceExpr count)
        (hBody : BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource body) :
        BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource (.forEach varName count body)

  /-- Internal with-errors body lists made from recursively bridged
  with-errors statements. -/
  inductive BridgedSourceInternalRecursiveBodyWithErrorsStmts
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
        dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head)
        (hTail : BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource tail) :
        BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource (head :: tail)
end

mutual
  theorem compileStmt_external_recursive_body_with_errors_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_external_body_with_errors_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames false inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_external_recursive_body_with_errors_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_external_recursive_body_with_errors_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil
    | forEach varName count body hCount hBody =>
        refine compileStmt_forEach_with_bridged_body fields events errors
          dynamicSource internalRetNames false inScopeNames varName count body
          hCount ?_ hOk
        intro bodyOut hBodyOk
        exact compileStmtList_external_recursive_body_with_errors_bridged fields
          events errors dynamicSource internalRetNames hBody
          (varName :: inScopeNames) hBodyOk

  theorem compileStmtList_external_recursive_body_with_errors_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames false inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_external_recursive_body_with_errors_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_external_recursive_body_with_errors_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

mutual
  theorem compileStmt_internal_recursive_body_with_errors_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_internal_body_with_errors_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames true inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_internal_recursive_body_with_errors_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_internal_recursive_body_with_errors_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil
    | forEach varName count body hCount hBody =>
        refine compileStmt_forEach_with_bridged_body fields events errors
          dynamicSource internalRetNames true inScopeNames varName count body
          hCount ?_ hOk
        intro bodyOut hBodyOk
        exact compileStmtList_internal_recursive_body_with_errors_bridged fields
          events errors dynamicSource internalRetNames hBody
          (varName :: inScopeNames) hBodyOk

  theorem compileStmtList_internal_recursive_body_with_errors_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
          dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames true inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_internal_recursive_body_with_errors_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_internal_recursive_body_with_errors_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

/-! ### Lifting flat with-errors aliases into the recursive inductive

Clients that produce a flat `∀ stmt ∈ stmts, BridgedSource*BodyWithErrorsStmt …`
witness (the alias form) can lift it into the inductive recursive predicate
via the `base` constructor applied pointwise, without manually threading
`nil`/`cons`. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      refine .cons (.base (h head (by simp))) (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      refine .cons (.base (h head (by simp))) (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

/-! ### Lifting flat plain-body aliases into the recursive inductive

Symmetric counterparts of the with-errors lift lemmas for the non-with-errors
recursive predicate. Callers with a flat
`∀ stmt ∈ stmts, BridgedSource*BodyStmt …` witness reach the inductive
`BridgedSource*RecursiveBodyStmts …` via pointwise `base`/`cons`/`nil`. -/

theorem BridgedSourceExternalRecursiveBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      refine .cons (.base (h head (by simp))) (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      refine .cons (.base (h head (by simp))) (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

/-! ### Lifting flat body aliases into the structured (one-`ite`-layer) inductive

Callers with a flat `∀ stmt ∈ stmts, BridgedSource*BodyStmt …` witness reach the
structured-body alias (`BridgedSource*StructuredBodyStmts`) via pointwise `.base`
wrapping — no `ite` layer needs to be introduced. Symmetric counterparts cover
the with-errors variants. -/

theorem BridgedSourceExternalStructuredBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

theorem BridgedSourceInternalStructuredBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

theorem BridgedSourceExternalStructuredBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

theorem BridgedSourceInternalStructuredBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

/-! ### Lifting flat body aliases into the nested (two-`ite`-layer) inductive

Each nested inductive exposes a `.structured` constructor that accepts the
one-layer structured predicate; composing it with `.base` yields a pointwise
lift from the flat body alias without introducing any `ite` wrapping. Covers
plain and with-errors variants. -/

theorem BridgedSourceExternalNestedBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .structured (.base (h stmt hMem))

theorem BridgedSourceInternalNestedBodyStmts_of_alias
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .structured (.base (h stmt hMem))

theorem BridgedSourceExternalNestedBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (.base (h stmt hMem))

theorem BridgedSourceInternalNestedBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (.base (h stmt hMem))

/-! ### Lifting flat with-errors aliases into the forEach-wrapped inductive

The forEach-wrapped with-errors inductives expose a `.base` constructor taking
the underlying with-errors body predicate directly, so the lift is a pointwise
`.base` wrap — no `forEach` layer need be introduced. -/

theorem BridgedSourceExternalForEachBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceExternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

theorem BridgedSourceInternalForEachBodyWithErrorsStmts_of_alias
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts) :
    BridgedSourceInternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

/-! ### Lifting plain body aliases into the with-errors body predicate

The with-errors body inductive exposes a `.base` constructor that accepts the
plain body predicate unchanged, so a caller holding a flat plain-body witness
(no custom-error, memory-write, or mapping-write cases) gets a with-errors
witness via pointwise `.base` wrapping. Composed with the already-landed
with-errors structured/nested/forEach/recursive lifts, this closes the
"plain body → any with-errors wrapper" convenience chain. -/

theorem BridgedSourceExternalBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalBodyWithErrorsStmts fields errors dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

theorem BridgedSourceInternalBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalBodyWithErrorsStmts fields errors dynamicSource stmts :=
  fun stmt hMem => .base (h stmt hMem)

/-! ### Direct plain→with-errors wrapper lifts

Compositions of `*BodyWithErrorsStmts_of_plain` with the existing with-errors
wrapper lifts. Callers holding a plain-body witness reach structured, nested,
or forEach-wrapped with-errors aliases in one pointwise step. -/

theorem BridgedSourceExternalStructuredBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (.base (h stmt hMem))

theorem BridgedSourceInternalStructuredBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (.base (h stmt hMem))

theorem BridgedSourceExternalNestedBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (.base (.base (h stmt hMem)))

theorem BridgedSourceInternalNestedBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (.base (.base (h stmt hMem)))

theorem BridgedSourceExternalForEachBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (.base (h stmt hMem))

theorem BridgedSourceInternalForEachBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .base (.base (h stmt hMem))

/-! ### Direct plain→recursive with-errors lifts

Callers holding a plain-body witness reach the recursive with-errors
inductive (closed under arbitrary `Stmt.ite` / `Stmt.forEach` nesting) by
chaining `*BodyWithErrorsStmts_of_plain` with
`*RecursiveBodyWithErrorsStmts_of_alias`. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias
    (BridgedSourceExternalBodyWithErrorsStmts_of_plain h)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias
    (BridgedSourceInternalBodyWithErrorsStmts_of_plain h)

/-! ### Lifting structured aliases into the nested (two-`ite`-layer) inductive

Each nested inductive exposes a `.structured` constructor accepting the
structured stmt unchanged, so a caller holding a structured witness reaches
the nested alias via pointwise `.structured` wrapping — no outer `ite` layer
needs to be introduced. Covers plain and with-errors variants. -/

theorem BridgedSourceExternalNestedBodyStmts_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .structured (h stmt hMem)

theorem BridgedSourceInternalNestedBodyStmts_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts :=
  fun stmt hMem => .structured (h stmt hMem)

theorem BridgedSourceExternalNestedBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (h stmt hMem)

theorem BridgedSourceInternalNestedBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem => .structured (h stmt hMem)

/-! ### Lifting structured aliases into the recursive inductive

Each structured stmt is either a plain body stmt (admitted via `.base`) or a
one-layer `Stmt.ite` whose branches are plain body-stmt lists. The recursive
inductive accepts both shapes: `.base` reuses the plain body stmt unchanged,
and `.ite` takes recursive-stmt lists for the branches — reachable from the
plain body-stmt-list branches via `*RecursiveBodyStmts_of_alias`. Covers plain
and with-errors variants. -/

theorem BridgedSourceExternalRecursiveBodyStmts_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceExternalRecursiveBodyStmt fields dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceExternalRecursiveBodyStmts_of_alias hThen)
              (BridgedSourceExternalRecursiveBodyStmts_of_alias hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyStmts_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceInternalRecursiveBodyStmt fields dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceInternalRecursiveBodyStmts_of_alias hThen)
              (BridgedSourceInternalRecursiveBodyStmts_of_alias hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hThen)
              (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hThen)
              (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

/-! ### Lifting nested aliases into the recursive inductive

Each nested stmt is either a structured stmt (admitted via `.structured`) or
an outer `Stmt.ite` layer whose branches are structured body-stmt lists. The
recursive inductive admits both shapes: the inner structured stmt is unfolded
via the same `match` used in the structured→recursive lift, and the outer
`.ite` reaches recursive-stmt lists via the just-landed
`*RecursiveBodyStmts_of_structured`. Covers plain and with-errors variants. -/

theorem BridgedSourceExternalRecursiveBodyStmts_of_nested
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceExternalRecursiveBodyStmt fields dynamicSource head := by
        match h head (by simp) with
        | .structured hStructured =>
            match hStructured with
            | .base hStmt => exact .base hStmt
            | .ite cond thenBranch elseBranch hCond hThen hElse =>
                exact .ite cond thenBranch elseBranch hCond
                  (BridgedSourceExternalRecursiveBodyStmts_of_alias hThen)
                  (BridgedSourceExternalRecursiveBodyStmts_of_alias hElse)
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceExternalRecursiveBodyStmts_of_structured hThen)
              (BridgedSourceExternalRecursiveBodyStmts_of_structured hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyStmts_of_nested
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceInternalRecursiveBodyStmt fields dynamicSource head := by
        match h head (by simp) with
        | .structured hStructured =>
            match hStructured with
            | .base hStmt => exact .base hStmt
            | .ite cond thenBranch elseBranch hCond hThen hElse =>
                exact .ite cond thenBranch elseBranch hCond
                  (BridgedSourceInternalRecursiveBodyStmts_of_alias hThen)
                  (BridgedSourceInternalRecursiveBodyStmts_of_alias hElse)
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceInternalRecursiveBodyStmts_of_structured hThen)
              (BridgedSourceInternalRecursiveBodyStmts_of_structured hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .structured hStructured =>
            match hStructured with
            | .base hStmt => exact .base hStmt
            | .ite cond thenBranch elseBranch hCond hThen hElse =>
                exact .ite cond thenBranch elseBranch hCond
                  (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hThen)
                  (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hElse)
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured hThen)
              (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .structured hStructured =>
            match hStructured with
            | .base hStmt => exact .base hStmt
            | .ite cond thenBranch elseBranch hCond hThen hElse =>
                exact .ite cond thenBranch elseBranch hCond
                  (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hThen)
                  (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hElse)
        | .ite cond thenBranch elseBranch hCond hThen hElse =>
            exact .ite cond thenBranch elseBranch hCond
              (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured hThen)
              (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured hElse)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

/-! ### Lifting forEach-wrapped with-errors aliases into the recursive inductive

Each forEach-with-errors stmt is either a plain with-errors body stmt (admitted
via `.base`) or an outer `Stmt.forEach varName count body` whose body is a
with-errors body-stmt list. The recursive with-errors inductive accepts both
shapes: `.base` reuses the plain with-errors body stmt unchanged, and
`.forEach` takes a recursive with-errors body-stmt list — reachable from the
plain with-errors body-stmt-list body via
`*RecursiveBodyWithErrorsStmts_of_alias`. Covers external and internal
variants. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_forEach
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .forEach varName count body hCount hBody =>
            exact .forEach varName count body hCount
              (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hBody)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_forEach
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalForEachBodyWithErrorsStmts fields errors
      dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  induction stmts with
  | nil => exact .nil
  | cons head tail ih =>
      have hHead : BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
          dynamicSource head := by
        match h head (by simp) with
        | .base hStmt => exact .base hStmt
        | .forEach varName count body hCount hBody =>
            exact .forEach varName count body hCount
              (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hBody)
      refine .cons hHead (ih ?_)
      intro stmt hMem
      exact h stmt (by simp [hMem])

/-! ### Lifting plain recursive witnesses into the with-errors recursive inductive

The with-errors body-stmt predicate admits the plain body-stmt predicate via
`.base`, so every plain recursive witness reinterprets into the with-errors
recursive inductive by reusing the same `.ite`/`.cons`/`.nil` structure while
wrapping each leaf through `.base (.base hStmt)`. Defined mutually over
stmt/list to follow the mutual plain inductive; recursion on sub-proofs is
structural. -/

mutual
theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  cases h with
  | base hStmt => exact .base (.base hStmt)
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_recursive hThen)
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_recursive hElse)

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_recursive
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalRecursiveBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  cases h with
  | nil => exact .nil
  | cons hHead hTail =>
      exact .cons
        (BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_recursive hHead)
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_recursive hTail)
end

mutual
theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  cases h with
  | base hStmt => exact .base (.base hStmt)
  | ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_recursive hThen)
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_recursive hElse)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_recursive
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalRecursiveBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts := by
  cases h with
  | nil => exact .nil
  | cons hHead hTail =>
      exact .cons
        (BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_recursive hHead)
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_recursive hTail)
end

/-! ### Lifting structured plain witnesses into structured with-errors

Callers holding a `BridgedSource*StructuredBodyStmt{,s}` witness (one-layer
`Stmt.ite` over plain body-stmt lists) reach the with-errors counterpart at
the same structural level in one step: `.base` delegates to the body-level
`*BodyWithErrorsStmt.base` ctor; `.ite` rewraps each branch list through the
existing `*BodyWithErrorsStmts_of_plain` alias lift. -/

theorem BridgedSourceExternalStructuredBodyWithErrorsStmt_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base (.base hStmt)
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalBodyWithErrorsStmts_of_plain hThen)
        (BridgedSourceExternalBodyWithErrorsStmts_of_plain hElse)

theorem BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem =>
    BridgedSourceExternalStructuredBodyWithErrorsStmt_of_structured (h stmt hMem)

theorem BridgedSourceInternalStructuredBodyWithErrorsStmt_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base (.base hStmt)
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalBodyWithErrorsStmts_of_plain hThen)
        (BridgedSourceInternalBodyWithErrorsStmts_of_plain hElse)

theorem BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalStructuredBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem =>
    BridgedSourceInternalStructuredBodyWithErrorsStmt_of_structured (h stmt hMem)

/-! ### Lifting nested plain witnesses into nested with-errors

Two-layer analog of the structured plain→with-errors lift. `.structured`
delegates to the just-landed structured plain→with-errors stmt lift; `.ite`
rewraps each branch list via the structured plain→with-errors list lift. -/

theorem BridgedSourceExternalNestedBodyWithErrorsStmt_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hStruct =>
      exact .structured
        (BridgedSourceExternalStructuredBodyWithErrorsStmt_of_structured hStruct)
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured hElse)

theorem BridgedSourceExternalNestedBodyWithErrorsStmts_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem =>
    BridgedSourceExternalNestedBodyWithErrorsStmt_of_nested (h stmt hMem)

theorem BridgedSourceInternalNestedBodyWithErrorsStmt_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hStruct =>
      exact .structured
        (BridgedSourceInternalStructuredBodyWithErrorsStmt_of_structured hStruct)
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured hElse)

theorem BridgedSourceInternalNestedBodyWithErrorsStmts_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  fun stmt hMem =>
    BridgedSourceInternalNestedBodyWithErrorsStmt_of_nested (h stmt hMem)

/-! ### Lifting plain structured/nested witnesses into the with-errors recursive predicate

Convenience compositions so callers holding a plain structured or nested
witness reach the recursive with-errors inductive in one step. Each lift
chains the matching plain→with-errors structural bridge with the existing
structured→recursive-with-errors or nested→recursive-with-errors lift. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured
    (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured h)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured
    (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured h)

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_nested
    (BridgedSourceExternalNestedBodyWithErrorsStmts_of_nested h)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalNestedBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_nested
    (BridgedSourceInternalNestedBodyWithErrorsStmts_of_nested h)

/-! ### Lifting plain structured witnesses into the nested with-errors predicate

Convenience compositions so callers holding a plain structured witness reach
the nested with-errors alias in one step. Chains the plain→with-errors
structural bridge with the existing structured→nested with-errors lift. -/

theorem BridgedSourceExternalNestedBodyWithErrorsStmts_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceExternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceExternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceExternalNestedBodyWithErrorsStmts_of_structured
    (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured h)

theorem BridgedSourceInternalNestedBodyWithErrorsStmts_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmts : List Stmt}
    (h : BridgedSourceInternalStructuredBodyStmts fields dynamicSource stmts) :
    BridgedSourceInternalNestedBodyWithErrorsStmts fields errors
      dynamicSource stmts :=
  BridgedSourceInternalNestedBodyWithErrorsStmts_of_structured
    (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured h)

/-! ### Stmt-level structured → recursive lifts

Single-stmt counterparts of the list-level `*RecursiveBody{,WithErrors}Stmts_of_structured`
lifts. A structured stmt is either a plain body stmt (admitted via `.base`) or
a one-layer `Stmt.ite` whose branches are plain/with-errors body-stmt lists,
and the recursive inductive admits both shapes: `.base` reuses the body stmt
unchanged while `.ite` lifts each branch list through
`*RecursiveBody{,WithErrors}Stmts_of_alias`. Covers plain and with-errors
variants. -/

theorem BridgedSourceExternalRecursiveBodyStmt_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalRecursiveBodyStmts_of_alias hThen)
        (BridgedSourceExternalRecursiveBodyStmts_of_alias hElse)

theorem BridgedSourceInternalRecursiveBodyStmt_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalRecursiveBodyStmts_of_alias hThen)
        (BridgedSourceInternalRecursiveBodyStmts_of_alias hElse)

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hThen)
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hElse)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hThen)
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hElse)

/-! ### Stmt-level nested → recursive lifts

Single-stmt counterparts of the list-level `*RecursiveBody{,WithErrors}Stmts_of_nested`
lifts. A nested stmt is either a structured stmt (admitted via the just-landed
`*RecursiveBodyStmt_of_structured`) or a two-layer `Stmt.ite` whose branches
are structured-stmt lists, which we lift through
`*RecursiveBody{,WithErrors}Stmts_of_structured`. Covers plain and
with-errors variants. -/

theorem BridgedSourceExternalRecursiveBodyStmt_of_nested
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt := by
  match h with
  | .structured hStructured =>
      exact BridgedSourceExternalRecursiveBodyStmt_of_structured hStructured
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalRecursiveBodyStmts_of_structured hThen)
        (BridgedSourceExternalRecursiveBodyStmts_of_structured hElse)

theorem BridgedSourceInternalRecursiveBodyStmt_of_nested
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt := by
  match h with
  | .structured hStructured =>
      exact BridgedSourceInternalRecursiveBodyStmt_of_structured hStructured
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalRecursiveBodyStmts_of_structured hThen)
        (BridgedSourceInternalRecursiveBodyStmts_of_structured hElse)

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hStructured =>
      exact BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_structured hStructured
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_structured hElse)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hStructured =>
      exact BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_structured hStructured
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_structured hElse)

/-! ### Stmt-level forEach-with-errors → recursive-with-errors lifts

Single-stmt counterparts of the list-level
`*RecursiveBodyWithErrorsStmts_of_forEach` lifts. A forEach-with-errors stmt
is either a plain with-errors body stmt (admitted via `.base`) or an outer
`Stmt.forEach varName count body` whose body is a plain with-errors body-stmt
list, lifted through `*RecursiveBodyWithErrorsStmts_of_alias`. Covers
external and internal variants. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_forEach
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .forEach varName count body hCount hBody =>
      exact .forEach varName count body hCount
        (BridgedSourceExternalRecursiveBodyWithErrorsStmts_of_alias hBody)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_forEach
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .base hStmt => exact .base hStmt
  | .forEach varName count body hCount hBody =>
      exact .forEach varName count body hCount
        (BridgedSourceInternalRecursiveBodyWithErrorsStmts_of_alias hBody)

/-! ### Stmt-level plain structured/nested → recursive-with-errors lifts

Single-stmt counterparts of the list-level
`*RecursiveBodyWithErrorsStmts_of_plain_{structured,nested}` lifts (landed in
`9a3c6266`). Composed from two existing stmt-level lifts: first reinterpret
the plain structured/nested witness as a plain recursive one via
`*RecursiveBodyStmt_of_structured` / `_of_nested`, then bridge into the
with-errors recursive inductive via `*RecursiveBodyWithErrorsStmt_of_plain_recursive`.
Covers external/internal variants. -/

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    (BridgedSourceExternalRecursiveBodyStmt_of_structured h)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    (BridgedSourceInternalRecursiveBodyStmt_of_structured h)

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    (BridgedSourceExternalRecursiveBodyStmt_of_nested h)

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_plain_recursive
    (BridgedSourceInternalRecursiveBodyStmt_of_nested h)

/-! ### Stmt-level plain structured → nested with-errors lifts

Single-stmt counterparts of the list-level
`*NestedBodyWithErrorsStmts_of_plain_structured` lifts. Chains the
plain→with-errors structured stmt bridge with the `.structured` constructor
of the nested with-errors inductive. -/

theorem BridgedSourceExternalNestedBodyWithErrorsStmt_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (BridgedSourceExternalStructuredBodyWithErrorsStmt_of_structured h)

theorem BridgedSourceInternalNestedBodyWithErrorsStmt_of_plain_structured
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (BridgedSourceInternalStructuredBodyWithErrorsStmt_of_structured h)

/-! ### Stmt-level plain nested → nested with-errors lifts

Single-stmt counterparts mapping a plain nested witness directly into the
nested with-errors inductive. The `.structured` branch delegates to the
stmt-level `_of_plain_structured` lift; the `.ite` branch reuses the nested
with-errors `.ite` constructor after lifting the structured body-stmt lists
via `BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured`. -/

theorem BridgedSourceExternalNestedBodyWithErrorsStmt_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hS =>
      exact BridgedSourceExternalNestedBodyWithErrorsStmt_of_plain_structured hS
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceExternalStructuredBodyWithErrorsStmts_of_structured hElse)

theorem BridgedSourceInternalNestedBodyWithErrorsStmt_of_plain_nested
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt := by
  match h with
  | .structured hS =>
      exact BridgedSourceInternalNestedBodyWithErrorsStmt_of_plain_structured hS
  | .ite cond thenBranch elseBranch hCond hThen hElse =>
      exact .ite cond thenBranch elseBranch hCond
        (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured hThen)
        (BridgedSourceInternalStructuredBodyWithErrorsStmts_of_structured hElse)

/-! ### Stmt-level direct plain→with-errors wrapper lifts

Stmt-level counterparts of the list-level `*_of_plain` lifts (landed in
commit `4e1fd204` for the wrappers and `d29b8248` for the base with-errors
alias). A plain body stmt is admitted into the with-errors inductive via
`.base`; structured/nested/forEach with-errors wrappers then stack on top
as further one-step constructor applications, mirroring the list-level
shapes `fun stmt hMem => .base (.base (h stmt hMem))` etc. -/

theorem BridgedSourceExternalBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt :=
  .base h

theorem BridgedSourceExternalStructuredBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base (.base h)

theorem BridgedSourceInternalStructuredBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base (.base h)

theorem BridgedSourceExternalNestedBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (.base (.base h))

theorem BridgedSourceInternalNestedBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (.base (.base h))

theorem BridgedSourceExternalForEachBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base (.base h)

theorem BridgedSourceInternalForEachBodyWithErrorsStmt_of_plain
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base (.base h)

/-! ### Stmt-level plain→structured/nested/recursive lifts (plain space)

Stmt-level counterparts of the list-level `*_of_alias` lifts in the plain
(non-with-errors) space. A plain body stmt admits into the structured,
nested, and recursive inductives via direct `.base` / `.structured (.base _)`
applications — mirroring the list-level shapes
`fun stmt hMem => .base (h stmt hMem)` etc. The `of_structured` nested lift
reuses the structured witness unchanged under the nested `.structured`
constructor. -/

theorem BridgedSourceExternalStructuredBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalStructuredBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt :=
  .base h

theorem BridgedSourceExternalNestedBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt :=
  .structured (.base h)

theorem BridgedSourceInternalNestedBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt :=
  .structured (.base h)

theorem BridgedSourceExternalNestedBodyStmt_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalNestedBodyStmt fields dynamicSource stmt :=
  .structured h

theorem BridgedSourceInternalNestedBodyStmt_of_structured
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalStructuredBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalNestedBodyStmt fields dynamicSource stmt :=
  .structured h

theorem BridgedSourceExternalRecursiveBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyStmt fields dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalRecursiveBodyStmt_of_base
    {fields : List Field} {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyStmt fields dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyStmt fields dynamicSource stmt :=
  .base h

/-! ### Stmt-level `_of_base` lifts for with-errors wrappers

Symmetric counterparts of the plain `*BodyStmt_of_base` lifts for the
with-errors family. Each wrapper inductive exposes a `.base`/`.structured`
constructor accepting an unchanged `BodyWithErrorsStmt`, reached via either
direct `.base` or `.structured (.base …)` composition. Covers structured,
nested, forEach, and recursive external/internal variants. -/

theorem BridgedSourceExternalStructuredBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceExternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalStructuredBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceInternalStructuredBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

theorem BridgedSourceExternalNestedBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceExternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (.base h)

theorem BridgedSourceInternalNestedBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceInternalNestedBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .structured (.base h)

theorem BridgedSourceExternalForEachBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceExternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalForEachBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceInternalForEachBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

theorem BridgedSourceExternalRecursiveBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceExternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceExternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

theorem BridgedSourceInternalRecursiveBodyWithErrorsStmt_of_base
    {fields : List Field} {errors : List ErrorDef}
    {dynamicSource : DynamicDataSource} {stmt : Stmt}
    (h : BridgedSourceInternalBodyWithErrorsStmt fields errors dynamicSource stmt) :
    BridgedSourceInternalRecursiveBodyWithErrorsStmt fields errors
      dynamicSource stmt :=
  .base h

/-! ## Source statement body closure: direct `rawLog` emissions

`Stmt.rawLog topics dataOffset dataSize` compiles (when `topics.length ≤ 4`)
to a single `YulStmt.expr (YulExpr.call s!"log{topics.length}" args)` where
`args = [offsetExpr, sizeExpr] ++ topicExprs`. Given bridged source
hypotheses on all three components, every argument is `BridgedExpr`
(topics via `compileExprList_bridgedSource`; offset/size via
`compileExpr_bridgedSource`), `s!"log{topics.length}"` is an
`isYulLogName`, and the emitted statement satisfies `BridgedStraightStmt`
via `expr_log`.
-/

inductive BridgedSourceRawLogStmt : Stmt → Prop
  | rawLog (topics : List Expr) (dataOffset dataSize : Expr)
      (hTopics : ∀ t ∈ topics, BridgedSourceExpr t)
      (hOffset : BridgedSourceExpr dataOffset)
      (hSize : BridgedSourceExpr dataSize) :
      BridgedSourceRawLogStmt (.rawLog topics dataOffset dataSize)

def BridgedSourceRawLogStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceRawLogStmt stmt

/-- A direct `rawLog` source statement with bridged topics/offset/size
compiles to a single-statement Yul list satisfying `BridgedStmts`. -/
theorem compileStmt_rawLog_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceRawLogStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | rawLog topics dataOffset dataSize hTopics hOffset hSize =>
      simp only [compileStmt] at hOk
      by_cases hLen : topics.length > 4
      · exfalso
        simp only [if_pos hLen, bind, Except.bind] at hOk
        exact Except.noConfusion hOk
      · simp only [if_neg hLen, bind, Except.bind,
                   Pure.pure, Except.pure] at hOk
        cases hTopicsExpr : compileExprList fields dynamicSource topics with
        | error err => simp [hTopicsExpr] at hOk
        | ok topicExprs =>
            simp only [hTopicsExpr] at hOk
            cases hOffsetExpr : compileExpr fields dynamicSource dataOffset with
            | error err => simp [hOffsetExpr] at hOk
            | ok offsetExpr =>
                simp only [hOffsetExpr] at hOk
                cases hSizeExpr : compileExpr fields dynamicSource dataSize with
                | error err => simp [hSizeExpr] at hOk
                | ok sizeExpr =>
                    simp only [hSizeExpr, Except.ok.injEq] at hOk
                    subst out
                    have hTopicsAll : ∀ t ∈ topicExprs, BridgedExpr t :=
                      compileExprList_bridgedSource fields dynamicSource hTopics hTopicsExpr
                    have hOffsetBridged : BridgedExpr offsetExpr :=
                      compileExpr_bridgedSource fields dynamicSource hOffset hOffsetExpr
                    have hSizeBridged : BridgedExpr sizeExpr :=
                      compileExpr_bridgedSource fields dynamicSource hSize hSizeExpr
                    have hLenLe : topics.length ≤ 4 := Nat.le_of_not_lt hLen
                    have hLogName :
                        Compiler.Proofs.IRGeneration.isYulLogName
                          s!"log{topics.length}" = true := by
                      have hn : topics.length ≤ 4 := hLenLe
                      generalize hEq : topics.length = n at hn
                      have hDisj : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
                        omega
                      rcases hDisj with rfl | rfl | rfl | rfl | rfl <;> decide
                    have hArgs : ∀ arg ∈ [offsetExpr, sizeExpr] ++ topicExprs,
                        BridgedExpr arg := by
                      intro arg hMem
                      rcases List.mem_append.mp hMem with hPrefix | hTail
                      · simp only [List.mem_cons, List.not_mem_nil, or_false]
                          at hPrefix
                        rcases hPrefix with h | h
                        · subst h; exact hOffsetBridged
                        · subst h; exact hSizeBridged
                      · exact hTopicsAll arg hTail
                    exact BridgedStmts_singleton
                      (BridgedStmt.straight _
                        (BridgedStraightStmt.expr_log _ _ hLogName hArgs))

/-- Direct `rawLog` source statements compile without nested function
declarations. -/
theorem compileStmt_rawLog_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceRawLogStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | rawLog topics dataOffset dataSize hTopics hOffset hSize =>
      simp only [compileStmt] at hOk
      by_cases hLen : topics.length > 4
      · simp only [if_pos hLen, bind, Except.bind] at hOk
        exact Except.noConfusion hOk
      · simp only [if_neg hLen, bind, Except.bind,
          Pure.pure, Except.pure] at hOk
        cases hTopicsExpr : compileExprList fields dynamicSource topics with
        | error err => simp [hTopicsExpr] at hOk
        | ok topicExprs =>
            simp only [hTopicsExpr] at hOk
            cases hOffsetExpr : compileExpr fields dynamicSource dataOffset with
            | error err => simp [hOffsetExpr] at hOk
            | ok offsetExpr =>
                simp only [hOffsetExpr] at hOk
                cases hSizeExpr : compileExpr fields dynamicSource dataSize with
                | error err => simp [hSizeExpr] at hOk
                | ok sizeExpr =>
                    simp [hSizeExpr, Native.yulStmtContainsFuncDef] at hOk
                    subst out
                    simp [Native.yulStmtContainsFuncDef]

/-- Lists made only of direct `rawLog` source statements with bridged
arguments compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_rawLog_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceRawLogStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceRawLogStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceRawLogStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_rawLog_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-- Lists made only of direct `rawLog` source statements with bridged
arguments compile without nested function declarations. -/
theorem compileStmtList_rawLog_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceRawLogStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal BridgedSourceRawLogStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_rawLog_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-!
## Mixed body with raw log

Alias-lift of `BridgedSourceRawLogStmt` into the existing with-errors body
predicates. Pure addition — defined here at the file tail so it can refer
to both `BridgedSourceExternalBodyWithErrorsStmt` (defined earlier) and
`BridgedSourceRawLogStmt` (defined above).
-/

/-- External body statement predicate extended to admit direct `rawLog`
source statements with bridged topics/offset/size alongside every case
already admitted by `BridgedSourceExternalBodyWithErrorsStmt`. -/
inductive BridgedSourceExternalBodyWithRawLogStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceExternalBodyWithErrorsStmt fields errors
        dynamicSource stmt) :
      BridgedSourceExternalBodyWithRawLogStmt fields errors dynamicSource stmt
  | rawLog {stmt : Stmt} (hStmt : BridgedSourceRawLogStmt stmt) :
      BridgedSourceExternalBodyWithRawLogStmt fields errors dynamicSource stmt

def BridgedSourceExternalBodyWithRawLogStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceExternalBodyWithRawLogStmt fields errors dynamicSource stmt

/-- Internal body statement predicate extended to admit direct `rawLog`
source statements with bridged topics/offset/size alongside every case
already admitted by `BridgedSourceInternalBodyWithErrorsStmt`. -/
inductive BridgedSourceInternalBodyWithRawLogStmt
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) : Stmt → Prop
  | base {stmt : Stmt}
      (hStmt : BridgedSourceInternalBodyWithErrorsStmt fields errors
        dynamicSource stmt) :
      BridgedSourceInternalBodyWithRawLogStmt fields errors dynamicSource stmt
  | rawLog {stmt : Stmt} (hStmt : BridgedSourceRawLogStmt stmt) :
      BridgedSourceInternalBodyWithRawLogStmt fields errors dynamicSource stmt

def BridgedSourceInternalBodyWithRawLogStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceInternalBodyWithRawLogStmt fields errors dynamicSource stmt

/-- Each statement in the raw-log-extended external body fragment compiles
to `BridgedStmts`. -/
theorem compileStmt_external_body_with_raw_log_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceExternalBodyWithRawLogStmt fields errors dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_external_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | rawLog hRaw =>
      exact compileStmt_rawLog_bridged fields events errors dynamicSource
        internalRetNames false inScopeNames hRaw hOk

/-- Each statement in the raw-log-extended internal body fragment compiles
to `BridgedStmts`. -/
theorem compileStmt_internal_body_with_raw_log_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceInternalBodyWithRawLogStmt fields errors dynamicSource stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | base hBase =>
      exact compileStmt_internal_body_with_errors_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hBase hOk
  | rawLog hRaw =>
      exact compileStmt_rawLog_bridged fields events errors dynamicSource
        internalRetNames true inScopeNames hRaw hOk

/-- Mixed external source bodies (with-errors fragments + direct `rawLog`)
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_external_body_with_raw_log_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceExternalBodyWithRawLogStmts fields errors dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro _ hMem
      exact (List.not_mem_nil hMem).elim
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          false inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceExternalBodyWithRawLogStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hBHead : BridgedStmts headOut :=
                compileStmt_external_body_with_raw_log_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead
              have hTailSource :
                  BridgedSourceExternalBodyWithRawLogStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              have hBTail : BridgedStmts tailOut :=
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail
              intro stmt hMem
              simp only [List.mem_append] at hMem
              rcases hMem with h | h
              · exact hBHead stmt h
              · exact hBTail stmt h

/-- Mixed internal source bodies (with-errors fragments + direct `rawLog`)
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_internal_body_with_raw_log_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceInternalBodyWithRawLogStmts fields errors dynamicSource stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts
  induction stmts with
  | nil =>
      intro inScopeNames _ out hOk
      simp [compileStmtList, Pure.pure, Except.pure] at hOk
      subst out
      intro _ hMem
      exact (List.not_mem_nil hMem).elim
  | cons head tail ih =>
      intro inScopeNames hSource out hOk
      simp only [compileStmtList, bind, Except.bind] at hOk
      cases hHead : compileStmt fields events errors dynamicSource internalRetNames
          true inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceInternalBodyWithRawLogStmt fields errors
                    dynamicSource head :=
                hSource head (by simp)
              have hBHead : BridgedStmts headOut :=
                compileStmt_internal_body_with_raw_log_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead
              have hTailSource :
                  BridgedSourceInternalBodyWithRawLogStmts fields errors
                    dynamicSource tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              have hBTail : BridgedStmts tailOut :=
                ih (collectStmtNames head ++ inScopeNames) hTailSource hTail
              intro stmt hMem
              simp only [List.mem_append] at hMem
              rcases hMem with h | h
              · exact hBHead stmt h
              · exact hBTail stmt h

/-!
## Recursive mixed body with raw log

Mutual inductive that recursively nests `Stmt.ite` / `Stmt.forEach`
wrappers around the raw-log-extended leaf fragment
(`BridgedSourceExternalBodyWithRawLogStmt` / `...InternalBody...`).
Parallel to the existing `BridgedSourceExternalRecursiveBodyWithErrorsStmt`
predicate but substitutes the raw-log-extended leaf. Defined at the file
tail because the leaf predicate is itself defined at the tail.
-/

mutual
  /-- External with-raw-log body statements made from the raw-log-extended
  fragment and recursively nested `Stmt.ite` / `Stmt.forEach` wrappers. -/
  inductive BridgedSourceExternalRecursiveBodyWithRawLogStmt
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceExternalBodyWithRawLogStmt fields errors
          dynamicSource stmt) :
        BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource thenBranch)
        (hElse : BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource elseBranch) :
        BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource (.ite cond thenBranch elseBranch)
    | forEach (varName : String) (count : Expr) (body : List Stmt)
        (hCount : BridgedSourceExpr count)
        (hBody : BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource body) :
        BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource (.forEach varName count body)

  /-- External with-raw-log body lists made from recursively bridged
  with-raw-log statements. -/
  inductive BridgedSourceExternalRecursiveBodyWithRawLogStmts
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
        dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource head)
        (hTail : BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource tail) :
        BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource (head :: tail)
end

mutual
  /-- Internal with-raw-log body statements made from the raw-log-extended
  fragment and recursively nested `Stmt.ite` / `Stmt.forEach` wrappers. -/
  inductive BridgedSourceInternalRecursiveBodyWithRawLogStmt
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : Stmt → Prop
    | base {stmt : Stmt}
        (hStmt : BridgedSourceInternalBodyWithRawLogStmt fields errors
          dynamicSource stmt) :
        BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource stmt
    | ite (cond : Expr) (thenBranch elseBranch : List Stmt)
        (hCond : BridgedSourceExpr cond)
        (hThen : BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource thenBranch)
        (hElse : BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource elseBranch) :
        BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource (.ite cond thenBranch elseBranch)
    | forEach (varName : String) (count : Expr) (body : List Stmt)
        (hCount : BridgedSourceExpr count)
        (hBody : BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource body) :
        BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource (.forEach varName count body)

  /-- Internal with-raw-log body lists made from recursively bridged
  with-raw-log statements. -/
  inductive BridgedSourceInternalRecursiveBodyWithRawLogStmts
      (fields : List Field) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) : List Stmt → Prop
    | nil : BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
        dynamicSource []
    | cons {head : Stmt} {tail : List Stmt}
        (hHead : BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource head)
        (hTail : BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource tail) :
        BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource (head :: tail)
end

mutual
  theorem compileStmt_external_recursive_body_with_raw_log_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceExternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_external_body_with_raw_log_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames false inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_external_recursive_body_with_raw_log_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_external_recursive_body_with_raw_log_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil
    | forEach varName count body hCount hBody =>
        refine compileStmt_forEach_with_bridged_body fields events errors
          dynamicSource internalRetNames false inScopeNames varName count body
          hCount ?_ hOk
        intro bodyOut hBodyOk
        exact compileStmtList_external_recursive_body_with_raw_log_bridged fields
          events errors dynamicSource internalRetNames hBody
          (varName :: inScopeNames) hBodyOk

  theorem compileStmtList_external_recursive_body_with_raw_log_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceExternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := false) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames false inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_external_recursive_body_with_raw_log_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_external_recursive_body_with_raw_log_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

mutual
  theorem compileStmt_internal_recursive_body_with_raw_log_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String)
      (inScopeNames : List String) :
      ∀ {stmt : Stmt},
        BridgedSourceInternalRecursiveBodyWithRawLogStmt fields errors
          dynamicSource stmt →
        ∀ {out : List YulStmt},
          compileStmt fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmt = .ok out →
          BridgedStmts out := by
    intro stmt hStmt out hOk
    cases hStmt with
    | base hBase =>
        exact compileStmt_internal_body_with_raw_log_bridged fields events errors
          dynamicSource internalRetNames inScopeNames hBase hOk
    | ite cond thenBranch elseBranch hCond hThen hElse =>
        simp only [compileStmt, bind, Except.bind] at hOk
        cases hCondExpr : compileExpr fields dynamicSource cond with
        | error err =>
            simp [hCondExpr] at hOk
        | ok condExpr =>
            cases hThenCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true inScopeNames [] thenBranch with
            | error err =>
                simp [hCondExpr, hThenCompile] at hOk
            | ok thenOut =>
                cases hElseCompile : compileStmtList fields events errors dynamicSource
                    internalRetNames true inScopeNames [] elseBranch with
                | error err =>
                    simp [hCondExpr, hThenCompile, hElseCompile] at hOk
                | ok elseOut =>
                    have hCondBridged : BridgedExpr condExpr :=
                      compileExpr_bridgedSource fields dynamicSource hCond hCondExpr
                    have hThenBridged : BridgedStmts thenOut :=
                      compileStmtList_internal_recursive_body_with_raw_log_bridged fields
                        events errors dynamicSource internalRetNames hThen
                        inScopeNames hThenCompile
                    have hElseBridged : BridgedStmts elseOut :=
                      compileStmtList_internal_recursive_body_with_raw_log_bridged fields
                        events errors dynamicSource internalRetNames hElse
                        inScopeNames hElseCompile
                    by_cases hEmpty : elseBranch.isEmpty
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      exact BridgedStmt.if_ condExpr thenOut hCondBridged hThenBridged
                    · simp [hCondExpr, hThenCompile, hElseCompile, hEmpty,
                        Pure.pure, Except.pure] at hOk
                      subst out
                      intro yulStmt hMem
                      simp only [List.mem_singleton] at hMem
                      subst yulStmt
                      refine BridgedStmt.block _ ?_
                      intro blockStmt hBlockMem
                      simp only [List.mem_cons, List.mem_nil_iff] at hBlockMem
                      rcases hBlockMem with rfl | rfl | rfl | hNil
                      · exact BridgedStmt.straight _
                          (BridgedStraightStmt.let_ _ condExpr hCondBridged)
                      · exact BridgedStmt.if_ _ thenOut (BridgedExpr.ident _) hThenBridged
                      · exact BridgedStmt.if_ _ elseOut
                          (bridgedExpr_iszero_ident _) hElseBridged
                      · cases hNil
    | forEach varName count body hCount hBody =>
        refine compileStmt_forEach_with_bridged_body fields events errors
          dynamicSource internalRetNames true inScopeNames varName count body
          hCount ?_ hOk
        intro bodyOut hBodyOk
        exact compileStmtList_internal_recursive_body_with_raw_log_bridged fields
          events errors dynamicSource internalRetNames hBody
          (varName :: inScopeNames) hBodyOk

  theorem compileStmtList_internal_recursive_body_with_raw_log_bridged
      (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
      (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
      ∀ {stmts : List Stmt},
        BridgedSourceInternalRecursiveBodyWithRawLogStmts fields errors
          dynamicSource stmts →
        ∀ (inScopeNames : List String) {out : List YulStmt},
          compileStmtList fields events errors dynamicSource internalRetNames
            (isInternal := true) inScopeNames [] stmts = .ok out →
          BridgedStmts out := by
    intro stmts hSource inScopeNames out hOk
    cases hSource with
    | nil =>
        simp [compileStmtList, Pure.pure, Except.pure] at hOk
        subst out
        intro stmt hMem
        cases hMem
    | @cons head tail hHead hTail =>
        simp only [compileStmtList, bind, Except.bind] at hOk
        cases hHeadCompile : compileStmt fields events errors dynamicSource
            internalRetNames true inScopeNames [] head with
        | error err =>
            simp [hHeadCompile] at hOk
        | ok headOut =>
            simp [hHeadCompile] at hOk
            cases hTailCompile : compileStmtList fields events errors dynamicSource
                internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
            | error err =>
                simp [hTailCompile] at hOk
            | ok tailOut =>
                simp [hTailCompile, Pure.pure, Except.pure] at hOk
                subst out
                exact BridgedStmts_append
                  (compileStmt_internal_recursive_body_with_raw_log_bridged fields events
                    errors dynamicSource internalRetNames inScopeNames hHead
                    hHeadCompile)
                  (compileStmtList_internal_recursive_body_with_raw_log_bridged fields
                    events errors dynamicSource internalRetNames hTail
                    (collectStmtNames head ++ inScopeNames) hTailCompile)
end

/-! ## Source statement body closure: single-slot double-mapping writes

`Stmt.setMapping2` goes through `compileSetMapping2`, which for a declared
`isMapping2` field with a single write slot emits a single
`sstore(mappingSlot(mappingSlot(lit slot, key1), key2), value)` statement.
This matches `BridgedStraightStmt.expr_sstore_mapping` with the inner
`mappingSlot(lit slot, key1)` as the `baseExpr` argument. The inner
`BridgedExpr` witness is constructed manually via the public
`BridgedExpr.call` ctor since `"mappingSlot" ∈ bridgedBuiltins`. -/

/-- Double-mapping-write source statements currently known to compile to
`BridgedStmts`: single-slot writes to a declared `isMapping2` field whose
key1/key2/value expressions are pure `BridgedSourceExpr`s. -/
inductive BridgedSourceMappingWrite2Stmt (fields : List Field) : Stmt → Prop
  | setMapping2 (field : String) {slot : Nat} {key1 key2 value : Expr}
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceMappingWrite2Stmt fields (.setMapping2 field key1 key2 value)

def BridgedSourceMappingWrite2Stmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWrite2Stmt fields stmt

/-- A single-slot `Stmt.setMapping2` source write with pure bridged key1/
key2/value expressions compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key1 key2 value : Expr}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2 field key1 key2 value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetMapping2 at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err => simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              have hInnerBridged : BridgedExpr
                  (Compiler.Yul.YulExpr.call "mappingSlot"
                    [Compiler.Yul.YulExpr.lit slot, key1Expr]) := by
                apply BridgedExpr.call
                · exact Or.inl (by decide)
                · intro arg hArg
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                  rcases hArg with hArg | hArg
                  · subst hArg; exact BridgedExpr.lit slot
                  · subst hArg; exact hBridgedKey1
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_sstore_mapping _ key2Expr valueExpr
                  hInnerBridged hBridgedKey2 hBridgedValue)

/-- Each statement in the double-mapping-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWrite2_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWrite2Stmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2 field hKey1 hKey2 hValue hMapping2 hSlots =>
      exact compileStmt_setMapping2_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey1 hKey2 hValue hMapping2 hSlots hOk

/-- Lists of single-slot double-mapping-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWrite2_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWrite2Stmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err =>
          simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource internalRetNames
              isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err =>
              simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingWrite2Stmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingWrite2Stmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWrite2_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setStorageAddr`

`Stmt.setStorageAddr` goes through `compileSetStorage ... requireAddressField := true`.
For an address-typed, unpacked, single-slot field the emitted shape is a
single `sstore(lit slot, and(valueExpr, hex addressMask))`. Closure reuses
`BridgedStraightStmt.expr_sstore_lit` with the masked value as a
bridged `BridgedExpr.call "and"`. -/

/-- Address-typed, single-slot setStorageAddr source statements with a pure
bridged right-hand side. -/
inductive BridgedSourceStorageAddrStmt (fields : List Field) : Stmt → Prop
  | setStorageAddr (field : String) (value : Expr) (f : Field) (slot : Nat)
      (hValue : BridgedSourceExpr value)
      (hNotMapping : isMapping fields field = false)
      (hAddrTy : f.ty = FieldType.address)
      (hFind :
        findFieldWithResolvedSlot fields field =
          some ({ f with packedBits := none, aliasSlots := [] }, slot)) :
      BridgedSourceStorageAddrStmt fields (.setStorageAddr field value)

def BridgedSourceStorageAddrStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStorageAddrStmt fields stmt

/-- An address-typed, unpacked single-slot `setStorageAddr` source statement
with a pure bridged right-hand side compiles to a literal-slot
`sstore(lit slot, and(value, hex addressMask))`, hence satisfies
`BridgedStmts`. -/
theorem compileStmt_setStorageAddr_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (value : Expr) (f : Field) (slot : Nat)
    (hValue : BridgedSourceExpr value)
    (hNotMapping : isMapping fields field = false)
    (hAddrTy : f.ty = FieldType.address)
    (hFind :
      findFieldWithResolvedSlot fields field =
        some ({ f with packedBits := none, aliasSlots := [] }, slot)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStorageAddr field value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorage at hOk
  simp [hNotMapping, hFind, hAddrTy] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr] at hOk
  | ok valueExpr =>
      simp [hExpr] at hOk
      subst out
      have hBridged : BridgedExpr valueExpr :=
        compileExpr_bridgedSource fields dynamicSource hValue hExpr
      have hMasked : BridgedExpr
          (Compiler.Yul.YulExpr.call "and"
            [valueExpr, Compiler.Yul.YulExpr.hex Compiler.Constants.addressMask]) := by
        apply BridgedExpr.call
        · exact Or.inl (by decide)
        · intro arg hArg
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
          rcases hArg with hArg | hArg
          · subst hArg; exact hBridged
          · subst hArg; exact BridgedExpr.hex _
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      exact BridgedStmt.straight _
        (BridgedStraightStmt.expr_sstore_lit slot _ hMasked)

/-- Each statement in the setStorageAddr fragment compiles to Yul satisfying
`BridgedStmts`. -/
theorem compileStmt_storageAddr_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageAddrStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStorageAddr field value f slot hValue hNotMapping hAddrTy hFind =>
      exact compileStmt_setStorageAddr_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field value f slot
        hValue hNotMapping hAddrTy hFind hOk

/-- Lists of single-slot `setStorageAddr` source statements compile to Yul
lists satisfying `BridgedStmts`. -/
theorem compileStmtList_storageAddr_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageAddrStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStorageAddrStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStorageAddrStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_storageAddr_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setStructMember`

`Stmt.setStructMember` goes through `compileSetStructMember`, which
delegates to `compileMappingSlotWrite` for unpacked members on a
single-slot mapping field. For `member.wordOffset = 0` the emitted
shape is `sstore(mappingSlot(lit slot, keyExpr), valueExpr)` — the
same shape as single-slot `setMapping`, so the proof reuses
`compileMappingSlotWrite_singleSlot_bridged`. -/

/-- Unpacked, wordOffset=0 setStructMember on a single-slot mappingStruct
field with a pure bridged key and value. -/
inductive BridgedSourceStructMemberStmt (fields : List Field) : Stmt → Prop
  | setStructMember (field : String) {slot : Nat} {key value : Expr}
      (memberName : String) (members : List StructMember) (member : StructMember)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hNotMapping2 : isMapping2 fields field = false)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hWordOffset : member.wordOffset = 0)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceStructMemberStmt fields
        (.setStructMember field key memberName value)

def BridgedSourceStructMemberStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMemberStmt fields stmt

/-- A single-slot, unpacked, wordOffset=0 `Stmt.setStructMember` source
write with a pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setStructMember_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key value : Expr}
    (memberName : String) (members : List StructMember) (member : StructMember)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember field key memberName value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, compileSetStructMember, hNotMapping2, hMembers,
    hFindMember, hUnpacked, hWordOffset, bind, Except.bind,
    Bool.false_eq_true, if_false] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr, pure, Pure.pure, Except.pure] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
          exact compileMappingSlotWrite_singleSlot_bridged fields field keyExpr
            valueExpr s!"setStructMember.{memberName}"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

/-- Each statement in the struct-member-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_structMember_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMemberStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember field memberName members member hKey hValue hNotMapping2
      hMembers hFindMember hUnpacked hWordOffset hMapping hSlots =>
      exact compileStmt_setStructMember_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field memberName
        members member hKey hValue hNotMapping2 hMembers hFindMember hUnpacked
        hWordOffset hMapping hSlots hOk

/-- Lists of single-slot struct-member-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMember_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMemberStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStructMemberStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStructMemberStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMember_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setStructMember2`

`Stmt.setStructMember2` goes through `compileSetStructMember2`. For an
unpacked, wordOffset=0 member of a single-slot `mappingStruct2` field,
the emitted shape is
  `sstore(mappingSlot(mappingSlot(lit slot, key1Expr), key2Expr), valueExpr)`
— identical to single-slot `setMapping2`. Closure mirrors
`compileStmt_setMapping2_singleSlot_bridged` with the added struct
member hypotheses. -/

/-- Unpacked, wordOffset=0 setStructMember2 on a single-slot
mappingStruct2 field with pure bridged key1/key2/value. -/
inductive BridgedSourceStructMember2Stmt (fields : List Field) : Stmt → Prop
  | setStructMember2 (field : String) {slot : Nat} {key1 key2 value : Expr}
      (memberName : String) (members : List StructMember) (member : StructMember)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hWordOffset : member.wordOffset = 0)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceStructMember2Stmt fields
        (.setStructMember2 field key1 key2 memberName value)

def BridgedSourceStructMember2Stmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMember2Stmt fields stmt

/-- A single-slot, unpacked, wordOffset=0 `Stmt.setStructMember2` source
write with pure bridged key1/key2/value expressions compiles to
`BridgedStmts`. -/
theorem compileStmt_setStructMember2_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key1 key2 value : Expr}
    (memberName : String) (members : List StructMember) (member : StructMember)
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember2 field key1 key2 memberName value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStructMember2 at hOk
  simp [hMapping2, hMembers, hFindMember, hUnpacked, hWordOffset, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err => simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              have hInnerBridged : BridgedExpr
                  (Compiler.Yul.YulExpr.call "mappingSlot"
                    [Compiler.Yul.YulExpr.lit slot, key1Expr]) := by
                apply BridgedExpr.call
                · exact Or.inl (by decide)
                · intro arg hArg
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                  rcases hArg with hArg | hArg
                  · subst hArg; exact BridgedExpr.lit slot
                  · subst hArg; exact hBridgedKey1
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_sstore_mapping _ key2Expr valueExpr
                  hInnerBridged hBridgedKey2 hBridgedValue)

/-- Each statement in the struct-member2-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_structMember2_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMember2Stmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember2 field memberName members member hKey1 hKey2 hValue hMapping2
      hMembers hFindMember hUnpacked hWordOffset hSlots =>
      exact compileStmt_setStructMember2_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field memberName
        members member hKey1 hKey2 hValue hMapping2 hMembers hFindMember hUnpacked
        hWordOffset hSlots hOk

/-- Lists of single-slot struct-member2-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMember2_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMember2Stmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStructMember2Stmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStructMember2Stmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMember2_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMappingWord`
(wordOffset=0)

`Stmt.setMappingWord field key wordOffset value` routes through
`compileMappingSlotWrite fields field keyExpr valueExpr "setMappingWord"
wordOffset`. When `wordOffset = 0`, the emitted shape collapses to
`sstore(mappingSlot(lit slot, keyExpr), valueExpr)` — identical to the
single-slot `setMapping` case — so the closure reuses
`compileMappingSlotWrite_singleSlot_bridged`. -/

/-- A single-slot `Stmt.setMappingWord field key 0 value` source write
with a pure bridged key and value at `wordOffset = 0`. -/
inductive BridgedSourceMappingWordStmt (fields : List Field) : Stmt → Prop
  | setMappingWord (field : String) {slot : Nat} {key value : Expr}
      (wordOffset : Nat)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hWordOffset : wordOffset = 0) :
      BridgedSourceMappingWordStmt fields
        (.setMappingWord field key wordOffset value)

def BridgedSourceMappingWordStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWordStmt fields stmt

/-- A single-slot `Stmt.setMappingWord` source write at `wordOffset = 0`
with pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingWord_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key value : Expr} (wordOffset : Nat)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingWord field key wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_singleSlot_bridged fields field keyExpr
            valueExpr "setMappingWord"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

/-- Each statement in the mappingWord-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWord_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWordStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingWord field wordOffset hKey hValue hMapping hSlots hWordOffset =>
      exact compileStmt_setMappingWord_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field wordOffset
        hKey hValue hMapping hSlots hWordOffset hOk

/-- Lists of single-slot mappingWord-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWord_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWordStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingWordStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingWordStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWord_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMapping2Word`
(wordOffset=0)

`Stmt.setMapping2Word field key1 key2 wordOffset value` routes through
`compileSetMapping2Word`. For a declared `isMapping2` field with a single
write slot and `wordOffset = 0`, the emitted shape collapses to
`sstore(mappingSlot(mappingSlot(lit slot, key1Expr), key2Expr),
valueExpr)` — identical to single-slot `setMapping2`. Closure mirrors
`compileStmt_setMapping2_singleSlot_bridged`. -/

/-- A single-slot `Stmt.setMapping2Word field key1 key2 0 value` source
write with pure bridged key1/key2/value at `wordOffset = 0`. -/
inductive BridgedSourceMapping2WordStmt (fields : List Field) : Stmt → Prop
  | setMapping2Word (field : String) {slot : Nat} {key1 key2 value : Expr}
      (wordOffset : Nat)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hWordOffset : wordOffset = 0) :
      BridgedSourceMapping2WordStmt fields
        (.setMapping2Word field key1 key2 wordOffset value)

def BridgedSourceMapping2WordStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMapping2WordStmt fields stmt

/-- A single-slot `Stmt.setMapping2Word` source write at `wordOffset = 0`
with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2Word_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key1 key2 value : Expr} (wordOffset : Nat)
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2Word field key1 key2 wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt] at hOk
  unfold compileSetMapping2Word at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err => simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              have hInnerBridged : BridgedExpr
                  (Compiler.Yul.YulExpr.call "mappingSlot"
                    [Compiler.Yul.YulExpr.lit slot, key1Expr]) := by
                apply BridgedExpr.call
                · exact Or.inl (by decide)
                · intro arg hArg
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                  rcases hArg with hArg | hArg
                  · subst hArg; exact BridgedExpr.lit slot
                  · subst hArg; exact hBridgedKey1
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_sstore_mapping _ key2Expr valueExpr
                  hInnerBridged hBridgedKey2 hBridgedValue)

/-- Each statement in the mapping2Word-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mapping2Word_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMapping2WordStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2Word field wordOffset hKey1 hKey2 hValue hMapping2 hSlots hWordOffset =>
      exact compileStmt_setMapping2Word_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field wordOffset
        hKey1 hKey2 hValue hMapping2 hSlots hWordOffset hOk

/-- Lists of single-slot mapping2Word-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mapping2Word_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMapping2WordStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMapping2WordStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMapping2WordStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mapping2Word_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: external `returnValues []`

`Stmt.returnValues []` with `isInternal = false` compiles to
`[expr (call "return" [lit 0, lit 0])]`, matching
`BridgedStraightStmt.expr_return` with two `BridgedExpr.lit` arguments.
No recursion into `compileExprList` is required because the values list
is empty, so this is a fixed-shape single-statement emission. -/

/-- An external `Stmt.returnValues []` source statement. -/
inductive BridgedSourceReturnValuesEmptyStmt : Stmt → Prop
  | returnValuesEmpty : BridgedSourceReturnValuesEmptyStmt (.returnValues [])

def BridgedSourceReturnValuesEmptyStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceReturnValuesEmptyStmt stmt

/-- An external `Stmt.returnValues []` compiles to a single-statement Yul
list satisfying `BridgedStmts`. -/
private theorem compileStmt_returnValuesEmpty_external_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.returnValues []) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp [compileStmt, Pure.pure, Except.pure] at hOk
  subst hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  exact BridgedStmt.straight _
    (BridgedStraightStmt.expr_return (.lit 0) (.lit 0)
      (BridgedExpr.lit 0) (BridgedExpr.lit 0))

private theorem compileStmt_returnValuesEmpty_external_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.returnValues []) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp [compileStmt, Pure.pure, Except.pure, Native.yulStmtContainsFuncDef]
    at hOk
  subst out
  simp [Native.yulStmtContainsFuncDef]

/-- Each statement in the empty-returnValues external fragment compiles to
Yul satisfying `BridgedStmts`. -/
theorem compileStmt_returnValuesEmpty_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesEmptyStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesEmpty =>
      exact compileStmt_returnValuesEmpty_external_bridged fields events errors
        dynamicSource internalRetNames inScopeNames hOk

theorem compileStmt_returnValuesEmpty_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesEmptyStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesEmpty =>
      exact compileStmt_returnValuesEmpty_external_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hOk

/-- Lists of external empty-returnValues source statements compile to Yul
lists satisfying `BridgedStmts`. -/
theorem compileStmtList_returnValuesEmpty_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesEmptyStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceReturnValuesEmptyStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceReturnValuesEmptyStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_returnValuesEmpty_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_returnValuesEmpty_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesEmptyStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames false BridgedSourceReturnValuesEmptyStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_returnValuesEmpty_noFuncDefs fields events errors dynamicSource
        internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: internal `returnValues []`

`Stmt.returnValues []` with `isInternal = true` and `internalRetNames = []`
compiles to `[leave]`, matching `BridgedStraightStmt.leave`. The
`internalRetNames.zip compiled` term evaluates to `[]`, leaving
`[] ++ [YulStmt.leave] = [YulStmt.leave]` as the emitted list. -/

/-- An internal zero-arity `Stmt.returnValues []` source statement. -/
inductive BridgedSourceReturnValuesEmptyInternalStmt : Stmt → Prop
  | returnValuesEmptyInternal :
      BridgedSourceReturnValuesEmptyInternalStmt (.returnValues [])

def BridgedSourceReturnValuesEmptyInternalStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceReturnValuesEmptyInternalStmt stmt

/-- An internal zero-arity `Stmt.returnValues []` (with empty
`internalRetNames`) compiles to a single-statement Yul list satisfying
`BridgedStmts`. -/
private theorem compileStmt_returnValuesEmpty_internal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource (internalRetNames := [])
        (isInternal := true) inScopeNames [] (.returnValues []) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp [compileStmt, compileExprList, bind, Except.bind, Pure.pure, Except.pure] at hOk
  subst hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  exact BridgedStmt.straight _ BridgedStraightStmt.leave

private theorem compileStmt_returnValuesEmpty_internal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (inScopeNames : List String) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource (internalRetNames := [])
        (isInternal := true) inScopeNames [] (.returnValues []) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp [compileStmt, compileExprList, bind, Except.bind, Pure.pure,
    Except.pure, Native.yulStmtContainsFuncDef] at hOk
  subst out
  simp [Native.yulStmtContainsFuncDef]

/-- Each statement in the empty-returnValues internal fragment compiles to
Yul satisfying `BridgedStmts`. -/
theorem compileStmt_returnValuesEmpty_internal_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesEmptyInternalStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource (internalRetNames := [])
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesEmptyInternal =>
      exact compileStmt_returnValuesEmpty_internal_bridged fields events errors
        dynamicSource inScopeNames hOk

theorem compileStmt_returnValuesEmpty_internal_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesEmptyInternalStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource (internalRetNames := [])
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesEmptyInternal =>
      exact compileStmt_returnValuesEmpty_internal_noFuncDefs fields events errors
        dynamicSource inScopeNames hOk

/-- Lists of internal empty-returnValues source statements compile to Yul
lists satisfying `BridgedStmts`. -/
theorem compileStmtList_returnValuesEmpty_internal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesEmptyInternalStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource (internalRetNames := [])
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
      cases hHead : compileStmt fields events errors dynamicSource []
          true inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              [] true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceReturnValuesEmptyInternalStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceReturnValuesEmptyInternalStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_returnValuesEmpty_internal_fragment_bridged fields events
                  errors dynamicSource inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_returnValuesEmpty_internal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesEmptyInternalStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource (internalRetNames := [])
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    [] true BridgedSourceReturnValuesEmptyInternalStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_returnValuesEmpty_internal_fragment_noFuncDefs fields events
        errors dynamicSource inScopeNames hStmt hOk)

/-! ## Source statement body closure: internal non-empty `returnValues`

`Stmt.returnValues values` with `isInternal = true` and
`values.length = internalRetNames.length` compiles to
`(internalRetNames.zip compiled).map (fun p => .assign p.1 p.2) ++ [leave]`,
where `compiled` is the `compileExprList` output over the bridged source
expressions. Each zip-derived assign is bridged via
`BridgedStraightStmt.assign` (its value is `BridgedExpr` by
`compileExprList_bridgedSource`), and the trailing `.leave` is
`BridgedStraightStmt.leave`. Close the whole list with `BridgedStmts_snoc`. -/

/-- An internal `Stmt.returnValues values` source statement whose every
element is a `BridgedSourceExpr` and whose arity matches `internalRetNames`. -/
inductive BridgedSourceReturnValuesInternalStmt
    (internalRetNames : List String) : Stmt → Prop
  | returnValuesInternal (values : List Expr)
      (hValues : ∀ v ∈ values, BridgedSourceExpr v)
      (hLen : values.length = internalRetNames.length) :
      BridgedSourceReturnValuesInternalStmt internalRetNames (.returnValues values)

def BridgedSourceReturnValuesInternalStmts
    (internalRetNames : List String) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceReturnValuesInternalStmt internalRetNames stmt

/-- Every element of `(names.zip compiled).map (fun p => .assign p.1 p.2)`
is a `BridgedStmt` when each `compiled` element is `BridgedExpr`. Used by
`compileStmt_returnValuesInternal_bridged` to close the prefix of the
compiled internal-return body. -/
private theorem zip_assigns_bridgedStmts (names : List String) :
    ∀ (compiled : List YulExpr), (∀ e ∈ compiled, BridgedExpr e) →
      BridgedStmts
        ((names.zip compiled).map (fun p => YulStmt.assign p.1 p.2)) := by
  induction names with
  | nil =>
      intro compiled _
      intro stmt hMem
      simp at hMem
  | cons n ns ih =>
      intro compiled hCompiled
      cases compiled with
      | nil =>
          intro stmt hMem
          simp at hMem
      | cons c cs =>
          have hC : BridgedExpr c := hCompiled c (by simp)
          have hCs : ∀ e ∈ cs, BridgedExpr e := by
            intro e hMem
            exact hCompiled e (by simp [hMem])
          intro stmt hMem
          simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hMem
          cases hMem with
          | inl h =>
              subst h
              exact BridgedStmt.straight _
                (BridgedStraightStmt.assign n c hC)
          | inr h =>
              exact ih cs hCs stmt h

private theorem zip_assigns_noFuncDefs (names : List String) :
    ∀ (compiled : List YulExpr),
      Native.yulStmtsContainFuncDef
        ((names.zip compiled).map (fun p => YulStmt.assign p.1 p.2)) = false := by
  induction names with
  | nil =>
      intro compiled
      simp [Native.yulStmtsContainFuncDef]
  | cons n ns ih =>
      intro compiled
      cases compiled with
      | nil =>
          simp [Native.yulStmtsContainFuncDef]
      | cons c cs =>
          simp [Native.yulStmtContainsFuncDef, ih cs]

/-- An internal non-empty `Stmt.returnValues values` with matching arity and
bridged source value expressions compiles to a Yul list satisfying
`BridgedStmts`. -/
private theorem compileStmt_returnValuesInternal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) (values : List Expr)
    (hValues : ∀ v ∈ values, BridgedSourceExpr v)
    (hLen : values.length = internalRetNames.length) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.returnValues values) = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hLenFalse : (values.length != internalRetNames.length) = false := by
    simp [hLen]
  simp only [compileStmt, hLenFalse, bind, Except.bind,
    Pure.pure, Except.pure] at hOk
  cases hCompiled : compileExprList fields dynamicSource values with
  | error err => simp [hCompiled] at hOk
  | ok compiled =>
      simp [hCompiled] at hOk
      subst hOk
      have hAllBridged : ∀ e ∈ compiled, BridgedExpr e :=
        compileExprList_bridgedSource fields dynamicSource hValues hCompiled
      exact BridgedStmts_snoc
        (zip_assigns_bridgedStmts internalRetNames compiled hAllBridged)
        (BridgedStmt.straight _ BridgedStraightStmt.leave)

private theorem compileStmt_returnValuesInternal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) (values : List Expr)
    (hLen : values.length = internalRetNames.length) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := true) inScopeNames [] (.returnValues values) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  have hLenFalse : (values.length != internalRetNames.length) = false := by
    simp [hLen]
  simp only [compileStmt, hLenFalse, bind, Except.bind,
    Pure.pure, Except.pure] at hOk
  cases hCompiled : compileExprList fields dynamicSource values with
  | error err => simp [hCompiled] at hOk
  | ok compiled =>
      simp [hCompiled, Native.yulStmtContainsFuncDef] at hOk
      subst out
      simp [Native.yulStmtContainsFuncDef,
        zip_assigns_noFuncDefs internalRetNames compiled]

/-- Each statement in the internal-non-empty-`returnValues` fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_returnValuesInternal_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceReturnValuesInternalStmt internalRetNames stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesInternal values hValues hLen =>
      exact compileStmt_returnValuesInternal_bridged fields events errors
        dynamicSource internalRetNames inScopeNames values hValues hLen hOk

theorem compileStmt_returnValuesInternal_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceReturnValuesInternalStmt internalRetNames stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesInternal values hValues hLen =>
      exact compileStmt_returnValuesInternal_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames values hLen hOk

/-- Lists of internal non-empty `returnValues` source statements (all sharing
the same `internalRetNames` arity) compile to Yul lists satisfying
`BridgedStmts`. -/
theorem compileStmtList_returnValuesInternal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesInternalStmts internalRetNames stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
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
          true inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames true (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceReturnValuesInternalStmt internalRetNames head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceReturnValuesInternalStmts internalRetNames tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_returnValuesInternal_fragment_bridged fields events errors
                  dynamicSource internalRetNames inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_returnValuesInternal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesInternalStmts internalRetNames stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := true) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames true (BridgedSourceReturnValuesInternalStmt internalRetNames)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_returnValuesInternal_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: external general `returnValues`

`Stmt.returnValues values` with `isInternal = false` compiles to:
- `[expr (call "return" [lit 0, lit 0])]` when `values = []`;
- `stores ++ [expr (call "return" [lit 0, lit (values.length * 32)])]` when
  `values ≠ []`, where `stores = compiled.zipIdx.map (fun (v, idx) =>
  expr (call "mstore" [lit (idx * 32), v]))` and `compiled` is
  `compileExprList fields dynamicSource values`.

Both cases satisfy `BridgedStmts`: the trailing `return` terminator is
`BridgedStraightStmt.expr_return` with two `BridgedExpr.lit` arguments;
each zip-indexed `mstore` is `BridgedStraightStmt.expr_mstore` with a
literal offset and the bridged value expression from
`compileExprList_bridgedSource`. Close via `BridgedStmts_snoc`. -/

/-- An external `Stmt.returnValues values` source statement whose every
element is a `BridgedSourceExpr`. Subsumes the empty-values form covered
by `BridgedSourceReturnValuesEmptyStmt`. -/
inductive BridgedSourceReturnValuesExternalStmt : Stmt → Prop
  | returnValuesExternal (values : List Expr)
      (hValues : ∀ v ∈ values, BridgedSourceExpr v) :
      BridgedSourceReturnValuesExternalStmt (.returnValues values)

def BridgedSourceReturnValuesExternalStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceReturnValuesExternalStmt stmt

/-- Every element of `compiled.zipIdx.map (fun (v, idx) =>
YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), v]))` is a
`BridgedStmt` when each `compiled` element is `BridgedExpr`. Proved by
induction on `compiled` with the `zipIdx` starting offset generalized. -/
private theorem zipIdx_mstores_bridgedStmts :
    ∀ (compiled : List YulExpr) (startIdx : Nat),
      (∀ e ∈ compiled, BridgedExpr e) →
      BridgedStmts
        ((compiled.zipIdx startIdx).map (fun p =>
          YulStmt.expr (YulExpr.call "mstore"
            [YulExpr.lit (p.2 * 32), p.1]))) := by
  intro compiled
  induction compiled with
  | nil =>
      intro _ _
      intro stmt hMem
      simp at hMem
  | cons c cs ih =>
      intro startIdx hCompiled
      have hC : BridgedExpr c := hCompiled c (by simp)
      have hCs : ∀ e ∈ cs, BridgedExpr e := by
        intro e hMem
        exact hCompiled e (by simp [hMem])
      intro stmt hMem
      simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at hMem
      cases hMem with
      | inl h =>
          subst h
          exact BridgedStmt.straight _
            (BridgedStraightStmt.expr_mstore (.lit (startIdx * 32)) c
              (BridgedExpr.lit (startIdx * 32)) hC)
      | inr h =>
          exact ih (startIdx + 1) hCs stmt h

private theorem zipIdx_mstores_noFuncDefs :
    ∀ (compiled : List YulExpr) (startIdx : Nat),
      Native.yulStmtsContainFuncDef
        ((compiled.zipIdx startIdx).map (fun p =>
          YulStmt.expr (YulExpr.call "mstore"
            [YulExpr.lit (p.2 * 32), p.1]))) = false := by
  intro compiled
  induction compiled with
  | nil =>
      intro startIdx
      simp [Native.yulStmtsContainFuncDef]
  | cons c cs ih =>
      intro startIdx
      simp [List.zipIdx_cons, Native.yulStmtContainsFuncDef, ih (startIdx + 1)]

/-- An external `Stmt.returnValues values` (for any `values`) with bridged
source value expressions compiles to a Yul list satisfying `BridgedStmts`. -/
private theorem compileStmt_returnValuesExternal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) (values : List Expr)
    (hValues : ∀ v ∈ values, BridgedSourceExpr v) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.returnValues values) = .ok out →
      BridgedStmts out := by
  intro out hOk
  by_cases hValuesNil : values = []
  · subst hValuesNil
    simp [compileStmt, Pure.pure, Except.pure] at hOk
    subst hOk
    intro yulStmt hMem
    simp only [List.mem_singleton] at hMem
    subst yulStmt
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_return (.lit 0) (.lit 0)
        (BridgedExpr.lit 0) (BridgedExpr.lit 0))
  · have hEmptyFalse : values.isEmpty = false := by
      simp [hValuesNil]
    simp only [compileStmt, hEmptyFalse, bind, Except.bind,
      Pure.pure, Except.pure] at hOk
    cases hCompiled : compileExprList fields dynamicSource values with
    | error err => simp [hCompiled] at hOk
    | ok compiled =>
        simp [hCompiled] at hOk
        subst hOk
        have hAllBridged : ∀ e ∈ compiled, BridgedExpr e :=
          compileExprList_bridgedSource fields dynamicSource hValues hCompiled
        exact BridgedStmts_snoc
          (zipIdx_mstores_bridgedStmts compiled 0 hAllBridged)
          (BridgedStmt.straight _
            (BridgedStraightStmt.expr_return (.lit 0) (.lit (values.length * 32))
              (BridgedExpr.lit 0) (BridgedExpr.lit (values.length * 32))))

private theorem compileStmt_returnValuesExternal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) (values : List Expr) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        (isInternal := false) inScopeNames [] (.returnValues values) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  by_cases hValuesNil : values = []
  · subst hValuesNil
    simp [compileStmt, Pure.pure, Except.pure, Native.yulStmtContainsFuncDef]
      at hOk
    subst out
    simp [Native.yulStmtContainsFuncDef]
  · have hEmptyFalse : values.isEmpty = false := by
      simp [hValuesNil]
    simp only [compileStmt, hEmptyFalse, bind, Except.bind,
      Pure.pure, Except.pure] at hOk
    cases hCompiled : compileExprList fields dynamicSource values with
    | error err => simp [hCompiled] at hOk
    | ok compiled =>
        simp [hCompiled, Native.yulStmtContainsFuncDef] at hOk
        subst out
        simp [Native.yulStmtContainsFuncDef, zipIdx_mstores_noFuncDefs compiled 0]

/-- Each statement in the external-`returnValues` fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_returnValuesExternal_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesExternalStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesExternal values hValues =>
      exact compileStmt_returnValuesExternal_bridged fields events errors
        dynamicSource internalRetNames inScopeNames values hValues hOk

theorem compileStmt_returnValuesExternal_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceReturnValuesExternalStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | returnValuesExternal values hValues =>
      exact compileStmt_returnValuesExternal_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames values hOk

/-- Lists of external `returnValues` source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_returnValuesExternal_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesExternalStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
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
          false inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames false (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceReturnValuesExternalStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceReturnValuesExternalStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_returnValuesExternal_fragment_bridged fields events
                  errors dynamicSource internalRetNames inScopeNames hHeadSource
                  hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_returnValuesExternal_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceReturnValuesExternalStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          (isInternal := false) inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames false BridgedSourceReturnValuesExternalStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_returnValuesExternal_fragment_noFuncDefs fields events errors
        dynamicSource internalRetNames inScopeNames hStmt hOk)

/-! ## Source statement body closure: mstore / tstore

`Stmt.mstore offset value` compiles to
`[expr (call "mstore" [compiledOffset, compiledValue])]`, where each
sub-expression comes from `compileExpr fields dynamicSource`. Both
compiled sub-expressions are `BridgedExpr` via `compileExpr_bridgedSource`
when the source expressions are `BridgedSourceExpr`, so the emitted
singleton matches `BridgedStraightStmt.expr_mstore`. Fully symmetric path
for `Stmt.tstore` closed by `BridgedStraightStmt.expr_tstore`. -/

inductive BridgedSourceMstoreStmt : Stmt → Prop
  | mstore (offset value : Expr)
      (hOffset : BridgedSourceExpr offset)
      (hValue : BridgedSourceExpr value) :
      BridgedSourceMstoreStmt (.mstore offset value)

def BridgedSourceMstoreStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMstoreStmt stmt

private theorem compileStmt_mstore_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (offset value : Expr)
    (hOffset : BridgedSourceExpr offset) (hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        isInternal inScopeNames [] (.mstore offset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind, Pure.pure, Except.pure] at hOk
  cases hO : compileExpr fields dynamicSource offset with
  | error err => simp [hO] at hOk
  | ok compiledOffset =>
      simp [hO] at hOk
      cases hV : compileExpr fields dynamicSource value with
      | error err => simp [hV] at hOk
      | ok compiledValue =>
          simp [hV] at hOk
          subst hOk
          have hBO : BridgedExpr compiledOffset :=
            compileExpr_bridgedSource fields dynamicSource hOffset hO
          have hBV : BridgedExpr compiledValue :=
            compileExpr_bridgedSource fields dynamicSource hValue hV
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.expr_mstore compiledOffset compiledValue hBO hBV)

private theorem compileStmt_mstore_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (offset value : Expr) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        isInternal inScopeNames [] (.mstore offset value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind, Pure.pure, Except.pure] at hOk
  cases hO : compileExpr fields dynamicSource offset with
  | error err => simp [hO] at hOk
  | ok compiledOffset =>
      simp [hO] at hOk
      cases hV : compileExpr fields dynamicSource value with
      | error err => simp [hV] at hOk
      | ok compiledValue =>
          simp [hV, Native.yulStmtContainsFuncDef] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

theorem compileStmt_mstore_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMstoreStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | mstore offset value hOffset hValue =>
      exact compileStmt_mstore_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames offset value hOffset hValue hOk

theorem compileStmt_mstore_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMstoreStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | mstore offset value hOffset hValue =>
      exact compileStmt_mstore_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames offset value hOk

theorem compileStmtList_mstore_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMstoreStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMstoreStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMstoreStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mstore_fragment_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mstore_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMstoreStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal BridgedSourceMstoreStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mstore_fragment_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

inductive BridgedSourceTstoreStmt : Stmt → Prop
  | tstore (offset value : Expr)
      (hOffset : BridgedSourceExpr offset)
      (hValue : BridgedSourceExpr value) :
      BridgedSourceTstoreStmt (.tstore offset value)

def BridgedSourceTstoreStmts (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceTstoreStmt stmt

private theorem compileStmt_tstore_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (offset value : Expr)
    (hOffset : BridgedSourceExpr offset) (hValue : BridgedSourceExpr value) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        isInternal inScopeNames [] (.tstore offset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind, Pure.pure, Except.pure] at hOk
  cases hO : compileExpr fields dynamicSource offset with
  | error err => simp [hO] at hOk
  | ok compiledOffset =>
      simp [hO] at hOk
      cases hV : compileExpr fields dynamicSource value with
      | error err => simp [hV] at hOk
      | ok compiledValue =>
          simp [hV] at hOk
          subst hOk
          have hBO : BridgedExpr compiledOffset :=
            compileExpr_bridgedSource fields dynamicSource hOffset hO
          have hBV : BridgedExpr compiledValue :=
            compileExpr_bridgedSource fields dynamicSource hValue hV
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          exact BridgedStmt.straight _
            (BridgedStraightStmt.expr_tstore compiledOffset compiledValue hBO hBV)

private theorem compileStmt_tstore_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (offset value : Expr) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames
        isInternal inScopeNames [] (.tstore offset value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind, Pure.pure, Except.pure] at hOk
  cases hO : compileExpr fields dynamicSource offset with
  | error err => simp [hO] at hOk
  | ok compiledOffset =>
      simp [hO] at hOk
      cases hV : compileExpr fields dynamicSource value with
      | error err => simp [hV] at hOk
      | ok compiledValue =>
          simp [hV, Native.yulStmtContainsFuncDef] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef]

theorem compileStmt_tstore_fragment_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceTstoreStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | tstore offset value hOffset hValue =>
      exact compileStmt_tstore_bridged fields events errors dynamicSource
        internalRetNames isInternal inScopeNames offset value hOffset hValue hOk

theorem compileStmt_tstore_fragment_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceTstoreStmt stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | tstore offset value hOffset hValue =>
      exact compileStmt_tstore_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames offset value hOk

theorem compileStmtList_tstore_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceTstoreStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceTstoreStmt head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceTstoreStmts tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_tstore_fragment_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_tstore_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceTstoreStmts stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal BridgedSourceTstoreStmt
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_tstore_fragment_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: `storageArrayPush`

`Stmt.storageArrayPush field value` compiles via `compileStorageArrayPush`
to a singleton list containing one `.block` with five straight-line
statements:

```
let __array_len := sload(lit slot)
mstore(lit 0, lit slot)
let __array_base := keccak256(lit 0, lit 32)
sstore(add(ident __array_base, ident __array_len), valueExpr)
sstore(lit slot, add(ident __array_len, lit 1))
```

Each maps to an existing `BridgedStraightStmt` ctor; the `.call "add"`
slot in the penultimate write is covered by the `expr_sstore_add` ctor
introduced in `ef43c3d9`. The value expression is closed via
`compileExpr_bridgedSource` on `BridgedSourceExpr value`. -/

inductive BridgedSourceStorageArrayPushStmt (fields : List Field) : Stmt → Prop
  | storageArrayPush (field : String) (value : Expr) (f : Field) (slot : Nat)
      (elemType : StorageArrayElemType)
      (hValue : BridgedSourceExpr value)
      (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
      (hDynArr : f.ty = .dynamicArray elemType) :
      BridgedSourceStorageArrayPushStmt fields (.storageArrayPush field value)

def BridgedSourceStorageArrayPushStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStorageArrayPushStmt fields stmt

theorem compileStmt_storageArrayPush_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (value : Expr) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hValue : BridgedSourceExpr value)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.storageArrayPush field value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileStorageArrayPush at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr, Pure.pure, Except.pure] at hOk
  | ok valueExpr =>
      simp [hExpr, Pure.pure, Except.pure] at hOk
      subst out
      have hValBridged : BridgedExpr valueExpr :=
        compileExpr_bridgedSource fields dynamicSource hValue hExpr
      -- Build BridgedExpr witnesses for the three ad-hoc composite exprs.
      have hSload : BridgedExpr
          (Compiler.Yul.YulExpr.call "sload"
            [Compiler.Yul.YulExpr.lit slot]) := by
        refine BridgedExpr.call "sload" _ (Or.inl ?_) ?_
        · simp [bridgedBuiltins]
        · intro arg hMem
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact BridgedExpr.lit _
          · cases hMem
      have hAddLen1 : BridgedExpr
          (Compiler.Yul.YulExpr.call "add"
            [Compiler.Yul.YulExpr.ident "__array_len",
              Compiler.Yul.YulExpr.lit 1]) := by
        refine BridgedExpr.call "add" _ (Or.inl ?_) ?_
        · simp [bridgedBuiltins]
        · intro arg hMem
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact BridgedExpr.ident _
          · rcases List.mem_cons.mp hMem with rfl | hMem
            · exact BridgedExpr.lit _
            · cases hMem
      intro yulStmt hMem
      simp only [List.mem_singleton] at hMem
      subst yulStmt
      -- Prove the single `.block [...]` wrapper is bridged via its body list.
      apply bridgedStmt_block_of_bridgedStraightStmts
      intro s hMemBlock
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemBlock
      rcases hMemBlock with rfl | rfl | rfl | rfl | rfl
      · exact BridgedStraightStmt.let_ "__array_len" _ hSload
      · exact BridgedStraightStmt.expr_mstore _ _
          (BridgedExpr.lit 0) (BridgedExpr.lit slot)
      · exact bridgedStraightStmt_let_keccak256 "__array_base" _ _
          (BridgedExpr.lit 0) (BridgedExpr.lit 32)
      · exact BridgedStraightStmt.expr_sstore_add _ _ _
          (BridgedExpr.ident "__array_base")
          (BridgedExpr.ident "__array_len") hValBridged
      · exact BridgedStraightStmt.expr_sstore_lit slot _ hAddLen1

private theorem compileStmt_storageArrayPush_singleSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (value : Expr) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.storageArrayPush field value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileStorageArrayPush at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind] at hOk
  cases hExpr : compileExpr fields dynamicSource value with
  | error err => simp [hExpr, Pure.pure, Except.pure] at hOk
  | ok valueExpr =>
      simp [hExpr, Pure.pure, Except.pure] at hOk
      subst out
      simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]

/-- Each statement in the storageArrayPush fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_storageArrayPush_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageArrayPushStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storageArrayPush field value f slot elemType hValue hFind hDynArr =>
      exact compileStmt_storageArrayPush_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field value f slot
        elemType hValue hFind hDynArr hOk

theorem compileStmt_storageArrayPush_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageArrayPushStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storageArrayPush field value f slot elemType hValue hFind hDynArr =>
      exact compileStmt_storageArrayPush_singleSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        value f slot elemType hFind hDynArr hOk

/-- Lists of `storageArrayPush` source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_storageArrayPush_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageArrayPushStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStorageArrayPushStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStorageArrayPushStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_storageArrayPush_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_storageArrayPush_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageArrayPushStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceStorageArrayPushStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_storageArrayPush_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: `storageArrayPop`

`Stmt.storageArrayPop field` compiles via `compileStorageArrayPop` to a
singleton list containing one `.block` with seven statements, including
an `if iszero(__array_len) { revert(0,0) }` guard:

```
let __array_len := sload(lit slot)
if_ (iszero(ident __array_len)) [revert(0, 0)]
let __array_new_len := sub(ident __array_len, lit 1)
mstore(lit 0, lit slot)
let __array_base := keccak256(lit 0, lit 32)
sstore(add(ident __array_base, ident __array_new_len), lit 0)
sstore(lit slot, ident __array_new_len)
```

The body is no longer pure straight-line, so the outer block closes via
`bridgedStmt_block_of_bridgedStmts` over a `BridgedStmts` list. The
guard fragment uses `bridgedStmt_if_of_bridgedStmts` with
`BridgedStmts_singleton_revert_zero`. All other statements lift their
`BridgedStraightStmt` witness via `bridgedStmt_of_bridgedStraightStmt`.
-/

inductive BridgedSourceStorageArrayPopStmt (fields : List Field) : Stmt → Prop
  | storageArrayPop (field : String) (f : Field) (slot : Nat)
      (elemType : StorageArrayElemType)
      (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
      (hDynArr : f.ty = .dynamicArray elemType) :
      BridgedSourceStorageArrayPopStmt fields (.storageArrayPop field)

def BridgedSourceStorageArrayPopStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStorageArrayPopStmt fields stmt

theorem compileStmt_storageArrayPop_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.storageArrayPop field) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileStorageArrayPop at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind, Pure.pure, Except.pure] at hOk
  subst out
  -- BridgedExpr witnesses for composite exprs.
  have hSload : BridgedExpr
      (Compiler.Yul.YulExpr.call "sload"
        [Compiler.Yul.YulExpr.lit slot]) := by
    refine BridgedExpr.call "sload" _ (Or.inl ?_) ?_
    · simp [bridgedBuiltins]
    · intro arg hMem
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact BridgedExpr.lit _
      · cases hMem
  have hIszero : BridgedExpr
      (Compiler.Yul.YulExpr.call "iszero"
        [Compiler.Yul.YulExpr.ident "__array_len"]) := by
    refine BridgedExpr.call "iszero" _ (Or.inl ?_) ?_
    · simp [bridgedBuiltins]
    · intro arg hMem
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact BridgedExpr.ident _
      · cases hMem
  have hSubLen : BridgedExpr
      (Compiler.Yul.YulExpr.call "sub"
        [Compiler.Yul.YulExpr.ident "__array_len",
          Compiler.Yul.YulExpr.lit 1]) := by
    refine BridgedExpr.call "sub" _ (Or.inl ?_) ?_
    · simp [bridgedBuiltins]
    · intro arg hMem
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact BridgedExpr.ident _
      · rcases List.mem_cons.mp hMem with rfl | hMem
        · exact BridgedExpr.lit _
        · cases hMem
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  -- Close the outer `.block body` via its body list.
  apply bridgedStmt_block_of_bridgedStmts
  intro s hMemBlock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemBlock
  rcases hMemBlock with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bridgedStmt_of_bridgedStraightStmt
      (BridgedStraightStmt.let_ "__array_len" _ hSload)
  · exact bridgedStmt_if_of_bridgedStmts hIszero
      BridgedStmts_singleton_revert_zero
  · exact bridgedStmt_of_bridgedStraightStmt
      (BridgedStraightStmt.let_ "__array_new_len" _ hSubLen)
  · exact bridgedStmt_of_bridgedStraightStmt
      (BridgedStraightStmt.expr_mstore _ _
        (BridgedExpr.lit 0) (BridgedExpr.lit slot))
  · exact bridgedStmt_of_bridgedStraightStmt
      (bridgedStraightStmt_let_keccak256 "__array_base" _ _
        (BridgedExpr.lit 0) (BridgedExpr.lit 32))
  · exact bridgedStmt_of_bridgedStraightStmt
      (BridgedStraightStmt.expr_sstore_add _ _ _
        (BridgedExpr.ident "__array_base")
        (BridgedExpr.ident "__array_new_len")
        (BridgedExpr.lit 0))
  · exact bridgedStmt_of_bridgedStraightStmt
      (BridgedStraightStmt.expr_sstore_lit slot _
        (BridgedExpr.ident "__array_new_len"))

private theorem compileStmt_storageArrayPop_singleSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.storageArrayPop field) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileStorageArrayPop at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind, Pure.pure, Except.pure] at hOk
  subst out
  simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]

/-- Each statement in the storageArrayPop fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_storageArrayPop_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageArrayPopStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storageArrayPop field f slot elemType hFind hDynArr =>
      exact compileStmt_storageArrayPop_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field f slot
        elemType hFind hDynArr hOk

theorem compileStmt_storageArrayPop_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStorageArrayPopStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | storageArrayPop field f slot elemType hFind hDynArr =>
      exact compileStmt_storageArrayPop_singleSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field f
        slot elemType hFind hDynArr hOk

/-- Lists of `storageArrayPop` source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_storageArrayPop_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageArrayPopStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceStorageArrayPopStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceStorageArrayPopStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_storageArrayPop_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_storageArrayPop_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStorageArrayPopStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceStorageArrayPopStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_storageArrayPop_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: `setStorageArrayElement`

`Stmt.setStorageArrayElement field index value` compiles via
`compileSetStorageArrayElement` to a singleton list containing one `.block`
with six statements, including an `if iszero(lt(...)) { revert(0,0) }`
bounds-check guard:

```
let __array_len := sload(lit slot)
let __array_index := indexExpr
if_ (iszero(lt(ident __array_index, ident __array_len))) [revert(0, 0)]
mstore(lit 0, lit slot)
let __array_base := keccak256(lit 0, lit 32)
sstore(add(ident __array_base, ident __array_index), valueExpr)
```

Both `indexExpr` and `valueExpr` are closed via `compileExpr_bridgedSource`
on their `BridgedSourceExpr` hypotheses; the body list is closed via
`bridgedStmt_block_of_bridgedStmts` with `bridgedStmt_if_of_bridgedStmts` +
`BridgedStmts_singleton_revert_zero` for the bounds-check guard. -/

inductive BridgedSourceSetStorageArrayElementStmt (fields : List Field) :
    Stmt → Prop
  | setStorageArrayElement (field : String) (index value : Expr) (f : Field)
      (slot : Nat) (elemType : StorageArrayElemType)
      (hIndex : BridgedSourceExpr index)
      (hValue : BridgedSourceExpr value)
      (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
      (hDynArr : f.ty = .dynamicArray elemType) :
      BridgedSourceSetStorageArrayElementStmt fields
        (.setStorageArrayElement field index value)

def BridgedSourceSetStorageArrayElementStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceSetStorageArrayElementStmt fields stmt

theorem compileStmt_setStorageArrayElement_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (index value : Expr) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hIndex : BridgedSourceExpr index)
    (hValue : BridgedSourceExpr value)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStorageArrayElement field index value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorageArrayElement at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind] at hOk
  cases hIdxExpr : compileExpr fields dynamicSource index with
  | error err => simp [hIdxExpr, Pure.pure, Except.pure] at hOk
  | ok indexExpr =>
      simp [hIdxExpr, Pure.pure, Except.pure] at hOk
      cases hValExpr : compileExpr fields dynamicSource value with
      | error err => simp [hValExpr] at hOk
      | ok valueExpr =>
          simp [hValExpr] at hOk
          subst out
          have hIdxBridged : BridgedExpr indexExpr :=
            compileExpr_bridgedSource fields dynamicSource hIndex hIdxExpr
          have hValBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValExpr
          have hSload : BridgedExpr
              (Compiler.Yul.YulExpr.call "sload"
                [Compiler.Yul.YulExpr.lit slot]) := by
            refine BridgedExpr.call "sload" _ (Or.inl ?_) ?_
            · simp [bridgedBuiltins]
            · intro arg hMem
              rcases List.mem_cons.mp hMem with rfl | hMem
              · exact BridgedExpr.lit _
              · cases hMem
          have hLt : BridgedExpr
              (Compiler.Yul.YulExpr.call "lt"
                [Compiler.Yul.YulExpr.ident "__array_index",
                  Compiler.Yul.YulExpr.ident "__array_len"]) := by
            refine BridgedExpr.call "lt" _ (Or.inl ?_) ?_
            · simp [bridgedBuiltins]
            · intro arg hMem
              rcases List.mem_cons.mp hMem with rfl | hMem
              · exact BridgedExpr.ident _
              · rcases List.mem_cons.mp hMem with rfl | hMem
                · exact BridgedExpr.ident _
                · cases hMem
          have hIszero : BridgedExpr
              (Compiler.Yul.YulExpr.call "iszero"
                [Compiler.Yul.YulExpr.call "lt"
                  [Compiler.Yul.YulExpr.ident "__array_index",
                    Compiler.Yul.YulExpr.ident "__array_len"]]) := by
            refine BridgedExpr.call "iszero" _ (Or.inl ?_) ?_
            · simp [bridgedBuiltins]
            · intro arg hMem
              rcases List.mem_cons.mp hMem with rfl | hMem
              · exact hLt
              · cases hMem
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          apply bridgedStmt_block_of_bridgedStmts
          intro s hMemBlock
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hMemBlock
          rcases hMemBlock with rfl | rfl | rfl | rfl | rfl | rfl
          · exact bridgedStmt_of_bridgedStraightStmt
              (BridgedStraightStmt.let_ "__array_len" _ hSload)
          · exact bridgedStmt_of_bridgedStraightStmt
              (BridgedStraightStmt.let_ "__array_index" _ hIdxBridged)
          · exact bridgedStmt_if_of_bridgedStmts hIszero
              BridgedStmts_singleton_revert_zero
          · exact bridgedStmt_of_bridgedStraightStmt
              (BridgedStraightStmt.expr_mstore _ _
                (BridgedExpr.lit 0) (BridgedExpr.lit slot))
          · exact bridgedStmt_of_bridgedStraightStmt
              (bridgedStraightStmt_let_keccak256 "__array_base" _ _
                (BridgedExpr.lit 0) (BridgedExpr.lit 32))
          · exact bridgedStmt_of_bridgedStraightStmt
              (BridgedStraightStmt.expr_sstore_add _ _ _
                (BridgedExpr.ident "__array_base")
                (BridgedExpr.ident "__array_index") hValBridged)

private theorem compileStmt_setStorageArrayElement_singleSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) (index value : Expr) (f : Field) (slot : Nat)
    (elemType : StorageArrayElemType)
    (hFind : findFieldWithResolvedSlot fields field = some (f, slot))
    (hDynArr : f.ty = .dynamicArray elemType) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStorageArrayElement field index value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStorageArrayElement at hOk
  unfold validateDynamicArrayField at hOk
  simp [hFind, hDynArr, bind, Except.bind] at hOk
  cases hIdxExpr : compileExpr fields dynamicSource index with
  | error err => simp [hIdxExpr, Pure.pure, Except.pure] at hOk
  | ok indexExpr =>
      simp [hIdxExpr, Pure.pure, Except.pure] at hOk
      cases hValExpr : compileExpr fields dynamicSource value with
      | error err => simp [hValExpr] at hOk
      | ok valueExpr =>
          simp [hValExpr] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]

/-- Each statement in the setStorageArrayElement fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_setStorageArrayElement_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceSetStorageArrayElementStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStorageArrayElement field index value f slot elemType
      hIndex hValue hFind hDynArr =>
      exact compileStmt_setStorageArrayElement_singleSlot_bridged fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        index value f slot elemType hIndex hValue hFind hDynArr hOk

theorem compileStmt_setStorageArrayElement_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceSetStorageArrayElementStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStorageArrayElement field index value f slot elemType
      hIndex hValue hFind hDynArr =>
      exact compileStmt_setStorageArrayElement_singleSlot_noFuncDefs fields
        events errors dynamicSource internalRetNames isInternal inScopeNames
        field index value f slot elemType hFind hDynArr hOk

/-- Lists of `setStorageArrayElement` source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_setStorageArrayElement_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceSetStorageArrayElementStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceSetStorageArrayElementStmt fields
                  head := hSource head (by simp)
              have hTailSource : BridgedSourceSetStorageArrayElementStmts fields
                  tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_setStorageArrayElement_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_setStorageArrayElement_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceSetStorageArrayElementStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal
    (BridgedSourceSetStorageArrayElementStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_setStorageArrayElement_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: single-slot `setMappingWord`
(wordOffset ≠ 0)

When `wordOffset ≠ 0`, `compileMappingSlotWrite` on a single-slot mapping
emits `sstore(add(mappingSlot(lit slot, keyExpr), lit wordOffset), valueExpr)`
— the extra `add` layer is bridged via `expr_sstore_add`, with the
`mappingSlot(lit slot, keyExpr)` subexpression witnessed by `BridgedExpr.call`
since `mappingSlot ∈ bridgedBuiltins`. This generalises the existing
`wordOffset = 0` closure (which collapses to a direct
`expr_sstore_mapping`) to cover non-zero offsets. -/

/-- A single-slot `Stmt.setMappingWord field key wordOffset value` source
write at `wordOffset ≠ 0` with a pure bridged key and value. -/
inductive BridgedSourceMappingWordNonzeroStmt (fields : List Field) : Stmt → Prop
  | setMappingWord (field : String) {slot wordOffset : Nat} {key value : Expr}
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hNonzero : wordOffset ≠ 0) :
      BridgedSourceMappingWordNonzeroStmt fields
        (.setMappingWord field key wordOffset value)

def BridgedSourceMappingWordNonzeroStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWordNonzeroStmt fields stmt

/-- Shared helper: `compileMappingSlotWrite` on a single-slot mapping with
`wordOffset ≠ 0` and pre-compiled bridged key/value expressions produces a
`BridgedStmts` list (one `sstore(add(mappingSlot(lit slot, key), lit wordOffset), value)`). -/
private theorem compileMappingSlotWrite_singleSlot_nonzero_bridged
    (fields : List Field) (field : String) {slot wordOffset : Nat}
    (keyExpr valueExpr : YulExpr) (label : String)
    (hKey : BridgedExpr keyExpr) (hValue : BridgedExpr valueExpr)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileMappingSlotWrite fields field keyExpr valueExpr label wordOffset = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp [compileMappingSlotWrite, hMapping, hSlots, hBeq, Pure.pure, Except.pure] at hOk
  subst hOk
  intro yulStmt hMem
  simp only [List.mem_singleton] at hMem
  subst yulStmt
  have hMappingExpr : BridgedExpr (.call "mappingSlot" [.lit slot, keyExpr]) := by
    refine BridgedExpr.call "mappingSlot" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hArg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
    rcases hArg with rfl | rfl
    · exact BridgedExpr.lit slot
    · exact hKey
  exact BridgedStmt.straight _
    (BridgedStraightStmt.expr_sstore_add
      (.call "mappingSlot" [.lit slot, keyExpr]) (.lit wordOffset) valueExpr
      hMappingExpr (BridgedExpr.lit wordOffset) hValue)

/-- A single-slot `Stmt.setMappingWord` source write at `wordOffset ≠ 0`
with pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingWord_singleSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot wordOffset : Nat} {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingWord field key wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_singleSlot_nonzero_bridged fields field
            keyExpr valueExpr "setMappingWord"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hNonzero hOk

/-- Each statement in the nonzero-offset mappingWord-write fragment compiles
to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWordNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingWord field hKey hValue hMapping hSlots hNonzero =>
      exact compileStmt_setMappingWord_singleSlot_nonzero_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey hValue hMapping hSlots hNonzero hOk

/-- Lists of single-slot nonzero-offset mappingWord-write source statements
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWordNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingWordNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingWordNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWordNonzero_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMapping2Word`
(wordOffset ≠ 0)

When `wordOffset ≠ 0`, `compileSetMapping2Word` on a single-slot mapping2
emits `sstore(add(mappingSlot(mappingSlot(lit slot, key1Expr), key2Expr),
lit wordOffset), valueExpr)` — the outer `add` is bridged via
`expr_sstore_add`, with the doubly-nested `mappingSlot` subexpression
witnessed by `BridgedExpr.call` since `mappingSlot ∈ bridgedBuiltins`.
This generalises the existing `wordOffset = 0` closure (which collapses
to `expr_sstore_mapping`) to cover non-zero offsets. -/

/-- A single-slot `Stmt.setMapping2Word field key1 key2 wordOffset value`
source write at `wordOffset ≠ 0` with pure bridged key1/key2/value. -/
inductive BridgedSourceMapping2WordNonzeroStmt (fields : List Field) : Stmt → Prop
  | setMapping2Word (field : String) {slot wordOffset : Nat}
      {key1 key2 value : Expr}
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hNonzero : wordOffset ≠ 0) :
      BridgedSourceMapping2WordNonzeroStmt fields
        (.setMapping2Word field key1 key2 wordOffset value)

def BridgedSourceMapping2WordNonzeroStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMapping2WordNonzeroStmt fields stmt

/-- A single-slot `Stmt.setMapping2Word` source write at `wordOffset ≠ 0`
with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2Word_singleSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot wordOffset : Nat} {key1 key2 value : Expr}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2Word field key1 key2 wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp only [compileStmt] at hOk
  unfold compileSetMapping2Word at hOk
  simp [hMapping2, hSlots, hBeq] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err => simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              intro yulStmt hMem
              simp only [List.mem_singleton] at hMem
              subst yulStmt
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              have hInnerBridged : BridgedExpr
                  (Compiler.Yul.YulExpr.call "mappingSlot"
                    [Compiler.Yul.YulExpr.lit slot, key1Expr]) := by
                refine BridgedExpr.call "mappingSlot" _
                  (Or.inl (by simp [bridgedBuiltins])) ?_
                intro arg hArg
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                rcases hArg with rfl | rfl
                · exact BridgedExpr.lit slot
                · exact hBridgedKey1
              have hOuterBridged : BridgedExpr
                  (Compiler.Yul.YulExpr.call "mappingSlot"
                    [Compiler.Yul.YulExpr.call "mappingSlot"
                        [Compiler.Yul.YulExpr.lit slot, key1Expr],
                      key2Expr]) := by
                refine BridgedExpr.call "mappingSlot" _
                  (Or.inl (by simp [bridgedBuiltins])) ?_
                intro arg hArg
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                rcases hArg with rfl | rfl
                · exact hInnerBridged
                · exact hBridgedKey2
              exact BridgedStmt.straight _
                (BridgedStraightStmt.expr_sstore_add _ (.lit wordOffset) valueExpr
                  hOuterBridged (BridgedExpr.lit wordOffset) hBridgedValue)

/-- Each statement in the nonzero-offset mapping2Word-write fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mapping2WordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMapping2WordNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2Word field hKey1 hKey2 hValue hMapping2 hSlots hNonzero =>
      exact compileStmt_setMapping2Word_singleSlot_nonzero_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey1 hKey2 hValue hMapping2 hSlots hNonzero hOk

/-- Lists of single-slot nonzero-offset mapping2Word-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mapping2WordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMapping2WordNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMapping2WordNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMapping2WordNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mapping2WordNonzero_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMappingChain`

`Stmt.setMappingChain` dispatches through `compileSetMappingChain`. For a
single-slot mapping field with bridged source keys and value, the emitted
Yul shape is a single
`sstore(keyExprs.foldl (fun acc k => mappingSlot(acc, k)) (lit slot),
valueExpr)`. Closure branches on whether `keyExprs` is empty:
- `keyExprs = []` → fold collapses to `lit slot`; use
  `BridgedStraightStmt.expr_sstore_lit`.
- `keyExprs = prefix ++ [last]` → outermost call is
  `mappingSlot(prefixFold, last)`; use
  `BridgedStraightStmt.expr_sstore_mapping` with the prefix fold witness
  produced by the `bridgedExpr_foldl_mappingSlot` helper. -/

/-- The `foldl mappingSlot` chain over a list of bridged key expressions
applied to a bridged base expression stays bridged. Used to discharge
the outer slot argument of the `sstore` emitted by
`compileSetMappingChain`. -/
theorem bridgedExpr_foldl_mappingSlot
    (keys : List Compiler.Yul.YulExpr) :
    ∀ (base : Compiler.Yul.YulExpr),
      BridgedExpr base →
      (∀ k ∈ keys, BridgedExpr k) →
      BridgedExpr
        (keys.foldl
          (fun acc k => Compiler.Yul.YulExpr.call "mappingSlot" [acc, k])
          base) := by
  induction keys with
  | nil =>
      intro base hBase _
      simpa using hBase
  | cons k ks ih =>
      intro base hBase hAll
      have hKey : BridgedExpr k := hAll k (by simp)
      have hTail : ∀ k' ∈ ks, BridgedExpr k' := by
        intro k' hMem; exact hAll k' (by simp [hMem])
      have hNewBase : BridgedExpr
          (Compiler.Yul.YulExpr.call "mappingSlot" [base, k]) := by
        apply BridgedExpr.call
        · exact Or.inl (by decide)
        · intro arg hArg
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
          rcases hArg with hArg | hArg
          · subst hArg; exact hBase
          · subst hArg; exact hKey
      simpa [List.foldl] using ih _ hNewBase hTail

/-- A single-slot `Stmt.setMappingChain field keys value` source write
with pure bridged keys and value. -/
inductive BridgedSourceMappingChainStmt (fields : List Field) : Stmt → Prop
  | setMappingChain (field : String) {slot : Nat}
      {keys : List Expr} {value : Expr}
      (hKeys : ∀ k ∈ keys, BridgedSourceExpr k)
      (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot]) :
      BridgedSourceMappingChainStmt fields (.setMappingChain field keys value)

def BridgedSourceMappingChainStmts (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingChainStmt fields stmt

/-- A single-slot `Stmt.setMappingChain` source write with bridged keys
and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingChain_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {keys : List Expr} {value : Expr}
    (hKeys : ∀ k ∈ keys, BridgedSourceExpr k)
    (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingChain field keys value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetMappingChain at hOk
  simp [hMapping, hSlots] at hOk
  cases hKeyExprs : compileExprList fields dynamicSource keys with
  | error err => simp [hKeyExprs, bind, Except.bind] at hOk
  | ok keyExprs =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExprs, hValueExpr, bind, Except.bind] at hOk
      | ok valueExpr =>
          simp [hKeyExprs, hValueExpr, bind, Except.bind] at hOk
          subst hOk
          intro yulStmt hMem
          simp only [List.mem_singleton] at hMem
          subst yulStmt
          have hBridgedKeys : ∀ ke ∈ keyExprs, BridgedExpr ke :=
            compileExprList_bridgedSource fields dynamicSource hKeys hKeyExprs
          have hBridgedValue : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
          rcases keyExprs.eq_nil_or_concat with hNil | ⟨pre, last, hConcat⟩
          · -- keyExprs = [] → fold = lit slot → use expr_sstore_lit
            subst hNil
            simp only [List.foldl_nil]
            exact BridgedStmt.straight _
              (BridgedStraightStmt.expr_sstore_lit slot valueExpr hBridgedValue)
          · -- keyExprs = pre ++ [last] → outermost call is mappingSlot(...)
            rw [List.concat_eq_append] at hConcat
            subst hConcat
            have hAllPre : ∀ ke ∈ pre, BridgedExpr ke := by
              intro ke hMem
              exact hBridgedKeys ke (by simp [hMem])
            have hLast : BridgedExpr last := hBridgedKeys last (by simp)
            have hPreFold : BridgedExpr
                (pre.foldl
                  (fun acc k => Compiler.Yul.YulExpr.call "mappingSlot" [acc, k])
                  (Compiler.Yul.YulExpr.lit slot)) :=
              bridgedExpr_foldl_mappingSlot pre _ (BridgedExpr.lit slot) hAllPre
            simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
            exact BridgedStmt.straight _
              (BridgedStraightStmt.expr_sstore_mapping _ last valueExpr
                hPreFold hLast hBridgedValue)

private theorem compileStmt_setMappingChain_singleSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {keys : List Expr} {value : Expr}
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot]) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingChain field keys value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetMappingChain at hOk
  simp [hMapping, hSlots] at hOk
  cases hKeyExprs : compileExprList fields dynamicSource keys with
  | error err => simp [hKeyExprs, bind, Except.bind] at hOk
  | ok keyExprs =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExprs, hValueExpr, bind, Except.bind] at hOk
      | ok valueExpr =>
          simp [hKeyExprs, hValueExpr, bind, Except.bind] at hOk
          subst out
          simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]

/-- Each statement in the mapping-chain-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mappingChain_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingChainStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingChain field hKeys hValue hMapping hSlots =>
      exact compileStmt_setMappingChain_singleSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKeys hValue hMapping hSlots hOk

theorem compileStmt_mappingChain_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingChainStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingChain field hKeys hValue hMapping hSlots =>
      exact compileStmt_setMappingChain_singleSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        hMapping hSlots hOk

/-- Lists of single-slot mapping-chain-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingChain_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingChainStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingChainStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingChainStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingChain_bridged fields events errors dynamicSource
                  internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mappingChain_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingChainStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceMappingChainStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mappingChain_noFuncDefs fields events errors dynamicSource
        internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Multi-slot mapping-write source body closure (wordOffset = 0)

Multi-slot `setMapping` / `setMappingUint` writes hit the compatibility branch
of `compileMappingSlotWrite`, which emits a single outer
`YulStmt.block` wrapping:
- `let __compat_key := keyExpr`
- `let __compat_value := valueExpr`
- one `sstore(mappingSlot(lit slot, ident "__compat_key"), ident "__compat_value")`
  per slot.

All components are `BridgedExpr`/`BridgedStraightStmt`-shaped, so the whole
block is `BridgedStmts`. Covers two `Stmt` ctors (`setMapping`,
`setMappingUint`) that share the same emission path.
-/

/-- The `slots.map` fragment in the multi-slot compatibility branch of
`compileMappingSlotWrite` (with `wordOffset = 0`) is `BridgedStraightStmts`.
Each element is `sstore(mappingSlot(lit slot, ident "__compat_key"),
ident "__compat_value")`. -/
private theorem bridgedStraightStmts_multiSlot_sstore_mapping
    (slots : List Nat) :
    BridgedStraightStmts
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit slot,
               Compiler.Yul.YulExpr.ident "__compat_key"],
            Compiler.Yul.YulExpr.ident "__compat_value"])) := by
  induction slots with
  | nil => intro stmt hMem; cases hMem
  | cons s rest ih =>
      intro stmt hMem
      simp only [List.map_cons, List.mem_cons] at hMem
      rcases hMem with hMem | hMem
      · subst hMem
        exact BridgedStraightStmt.expr_sstore_mapping
          (Compiler.Yul.YulExpr.lit s)
          (Compiler.Yul.YulExpr.ident "__compat_key")
          (Compiler.Yul.YulExpr.ident "__compat_value")
          (BridgedExpr.lit s)
          (BridgedExpr.ident "__compat_key")
          (BridgedExpr.ident "__compat_value")
      · exact ih stmt hMem

private theorem yulStmtsContainFuncDef_multiSlot_sstore_mapping
    (slots : List Nat) :
    Native.yulStmtsContainFuncDef
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit slot,
               Compiler.Yul.YulExpr.ident "__compat_key"],
            Compiler.Yul.YulExpr.ident "__compat_value"])) = false := by
  induction slots with
  | nil => simp [Native.yulStmtsContainFuncDef]
  | cons slot rest ih =>
      simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef, ih]

/-- Shared helper: `compileMappingSlotWrite` on a multi-slot mapping (≥ 2
slots) with `wordOffset = 0` and pre-compiled bridged key/value expressions
produces a `BridgedStmts` list (one outer block wrapping two let-bindings
and N sstore writes). -/
private theorem compileMappingSlotWrite_multiSlot_bridged
    (fields : List Field) (field : String)
    {slot0 slot1 : Nat} {slotsRest : List Nat}
    (keyExpr valueExpr : YulExpr) (label : String)
    (hKey : BridgedExpr keyExpr) (hValue : BridgedExpr valueExpr)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileMappingSlotWrite fields field keyExpr valueExpr label 0 = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp [compileMappingSlotWrite, hMapping, hSlots, Pure.pure, Except.pure] at hOk
  subst hOk
  refine BridgedStmts_singleton_block ?_
  -- Body: [let __compat_key := keyExpr, let __compat_value := valueExpr]
  --   ++ (slot0 :: slot1 :: slotsRest).map sstoreFn
  -- After simp, simp has unfolded the cons head of List.map, so the body is:
  --   let_ __compat_key :: let_ __compat_value
  --     :: sstore_slot0 :: sstore_slot1 :: slotsRest.map sstoreFn
  intro stmt hMem
  simp only [List.mem_cons] at hMem
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ hKey)
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ hValue)
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_sstore_mapping
        (Compiler.Yul.YulExpr.lit slot0)
        (Compiler.Yul.YulExpr.ident "__compat_key")
        (Compiler.Yul.YulExpr.ident "__compat_value")
        (BridgedExpr.lit slot0)
        (BridgedExpr.ident "__compat_key")
        (BridgedExpr.ident "__compat_value"))
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_sstore_mapping
        (Compiler.Yul.YulExpr.lit slot1)
        (Compiler.Yul.YulExpr.ident "__compat_key")
        (Compiler.Yul.YulExpr.ident "__compat_value")
        (BridgedExpr.lit slot1)
        (BridgedExpr.ident "__compat_key")
        (BridgedExpr.ident "__compat_value"))
  · have hSstore : BridgedStraightStmt stmt :=
      bridgedStraightStmts_multiSlot_sstore_mapping slotsRest stmt
        (by simpa using hMem)
    exact BridgedStmt.straight _ hSstore

private theorem compileMappingSlotWrite_multiSlot_noFuncDefs
    (fields : List Field) (field : String)
    {slot0 slot1 : Nat} {slotsRest : List Nat}
    (keyExpr valueExpr : YulExpr) (label : String)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileMappingSlotWrite fields field keyExpr valueExpr label 0 = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp [compileMappingSlotWrite, hMapping, hSlots, Pure.pure, Except.pure] at hOk
  subst hOk
  simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef,
    yulStmtsContainFuncDef_multiSlot_sstore_mapping]

/-- Multi-slot mapping-write source statements: `setMapping` /
`setMappingUint` to a declared mapping field whose write slots list has ≥ 2
entries, with pure `BridgedSourceExpr` key/value. -/
inductive BridgedSourceMappingWriteMultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setMapping (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr}
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceMappingWriteMultiSlotStmt fields
        (.setMapping field key value)
  | setMappingUint (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr}
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceMappingWriteMultiSlotStmt fields
        (.setMappingUint field key value)

def BridgedSourceMappingWriteMultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWriteMultiSlotStmt fields stmt

/-- A multi-slot `Stmt.setMapping` source write with pure bridged key and
value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping field key value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_bridged fields field keyExpr
            valueExpr "setMapping"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

theorem compileStmt_setMapping_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr}
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping field key value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_noFuncDefs fields field
            keyExpr valueExpr "setMapping" hMapping hSlots hOk

/-- A multi-slot `Stmt.setMappingUint` source write with pure bridged key
and value compiles to `BridgedStmts`. Emission path is identical to
`Stmt.setMapping`, so this reuses the same mapping-write helper. -/
theorem compileStmt_setMappingUint_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr}
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingUint field key value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_bridged fields field keyExpr
            valueExpr "setMappingUint"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

theorem compileStmt_setMappingUint_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr}
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingUint field key value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_noFuncDefs fields field
            keyExpr valueExpr "setMappingUint" hMapping hSlots hOk

/-- Each statement in the multi-slot mapping-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWriteMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWriteMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping field hKey hValue hMapping hSlots =>
      exact compileStmt_setMapping_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey hValue hMapping hSlots hOk
  | setMappingUint field hKey hValue hMapping hSlots =>
      exact compileStmt_setMappingUint_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey hValue hMapping hSlots hOk

theorem compileStmt_mappingWriteMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWriteMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping field hKey hValue hMapping hSlots =>
      exact compileStmt_setMapping_multiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hMapping hSlots hOk
  | setMappingUint field hKey hValue hMapping hSlots =>
      exact compileStmt_setMappingUint_multiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hMapping hSlots hOk

/-- Lists of multi-slot mapping-write source statements compile to Yul lists
satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWriteMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWriteMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingWriteMultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource : BridgedSourceMappingWriteMultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWriteMultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mappingWriteMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWriteMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceMappingWriteMultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mappingWriteMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setMapping2` (wordOffset = 0)

Multi-slot `setMapping2` writes hit the `_` arm of `compileSetMapping2`'s
`match slots`, which emits a single outer `YulStmt.block` wrapping:
- `let __compat_key1 := key1Expr`
- `let __compat_key2 := key2Expr`
- `let __compat_value := valueExpr`
- one
  `sstore(mappingSlot(mappingSlot(lit slot, ident "__compat_key1"),
                       ident "__compat_key2"),
         ident "__compat_value")`
  per slot.

All components are `BridgedExpr`/`BridgedStraightStmt`-shaped, so the whole
block is `BridgedStmts`. One predicate ctor (`setMapping2`).
-/

/-- The `slots.map` fragment in the multi-slot branch of
`compileSetMapping2` is `BridgedStraightStmts`. Each element is
`sstore(mappingSlot(mappingSlot(lit slot, ident "__compat_key1"),
                     ident "__compat_key2"),
       ident "__compat_value")`. -/
private theorem bridgedStraightStmts_multiSlot_sstore_mapping2
    (slots : List Nat) :
    BridgedStraightStmts
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.call "mappingSlot"
                 [Compiler.Yul.YulExpr.lit slot,
                  Compiler.Yul.YulExpr.ident "__compat_key1"],
               Compiler.Yul.YulExpr.ident "__compat_key2"],
            Compiler.Yul.YulExpr.ident "__compat_value"])) := by
  induction slots with
  | nil => intro stmt hMem; cases hMem
  | cons s rest ih =>
      intro stmt hMem
      simp only [List.map_cons, List.mem_cons] at hMem
      rcases hMem with hMem | hMem
      · subst hMem
        have hInnerBridged : BridgedExpr
            (Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit s,
               Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg hArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
            rcases hArg with hArg | hArg
            · subst hArg; exact BridgedExpr.lit s
            · subst hArg; exact BridgedExpr.ident "__compat_key1"
        exact BridgedStraightStmt.expr_sstore_mapping
          (Compiler.Yul.YulExpr.call "mappingSlot"
            [Compiler.Yul.YulExpr.lit s,
             Compiler.Yul.YulExpr.ident "__compat_key1"])
          (Compiler.Yul.YulExpr.ident "__compat_key2")
          (Compiler.Yul.YulExpr.ident "__compat_value")
          hInnerBridged
          (BridgedExpr.ident "__compat_key2")
          (BridgedExpr.ident "__compat_value")
      · exact ih stmt hMem

private theorem yulStmtsContainFuncDef_multiSlot_sstore_mapping2
    (slots : List Nat) :
    Native.yulStmtsContainFuncDef
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.call "mappingSlot"
                 [Compiler.Yul.YulExpr.lit slot,
                  Compiler.Yul.YulExpr.ident "__compat_key1"],
               Compiler.Yul.YulExpr.ident "__compat_key2"],
            Compiler.Yul.YulExpr.ident "__compat_value"])) = false := by
  induction slots with
  | nil => simp [Native.yulStmtsContainFuncDef]
  | cons slot rest ih =>
      simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef, ih]

/-- Multi-slot double-mapping-write source statements: `setMapping2` to a
declared `isMapping2` field whose write slots list has ≥ 2 entries, with
pure `BridgedSourceExpr` key1/key2/value. -/
inductive BridgedSourceMappingWrite2MultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setMapping2 (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key1 key2 value : Expr}
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceMappingWrite2MultiSlotStmt fields
        (.setMapping2 field key1 key2 value)

def BridgedSourceMappingWrite2MultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWrite2MultiSlotStmt fields stmt

/-- A multi-slot `Stmt.setMapping2` source write with pure bridged
key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2 field key1 key2 value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetMapping2 at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              refine BridgedStmts_singleton_block ?_
              -- After simp, body is:
              --   let_ __compat_key1 :: let_ __compat_key2 :: let_ __compat_value
              --     :: sstore_slot0 :: sstore_slot1 :: slotsRest.map sstoreFn
              intro stmt hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey1)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey2)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedValue)
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot0,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot0
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner0
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot1,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot1
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner1
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              · have hSstore : BridgedStraightStmt stmt :=
                  bridgedStraightStmts_multiSlot_sstore_mapping2 slotsRest stmt
                    (by simpa using hMem)
                exact BridgedStmt.straight _ hSstore

theorem compileStmt_setMapping2_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr}
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2 field key1 key2 value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetMapping2 at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst out
              simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef,
                yulStmtsContainFuncDef_multiSlot_sstore_mapping2]

/-- Each statement in the multi-slot double-mapping-write fragment compiles
to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWrite2MultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWrite2MultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2 field hKey1 hKey2 hValue hMapping2 hSlots =>
      exact compileStmt_setMapping2_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey1 hKey2 hValue hMapping2 hSlots hOk

theorem compileStmt_mappingWrite2MultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWrite2MultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2 field hKey1 hKey2 hValue hMapping2 hSlots =>
      exact compileStmt_setMapping2_multiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hMapping2 hSlots hOk

/-- Lists of multi-slot double-mapping-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWrite2MultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWrite2MultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingWrite2MultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingWrite2MultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWrite2MultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mappingWrite2MultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWrite2MultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceMappingWrite2MultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mappingWrite2MultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setStructMember` (wordOffset = 0)

`Stmt.setStructMember` goes through `compileSetStructMember`. For an
unpacked, wordOffset=0 member on a multi-slot (≥ 2 slots) `mappingStruct`
field, the emission path dispatches to `compileMappingSlotWrite` with
`wordOffset = 0`, which produces the same block-wrapped shape as multi-slot
`setMapping` / `setMappingUint`. Closure reuses
`compileMappingSlotWrite_multiSlot_bridged` (cd135ff7). -/

/-- Unpacked, wordOffset=0 `setStructMember` on a multi-slot
`mappingStruct` field with a pure bridged key and value. -/
inductive BridgedSourceStructMemberMultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setStructMember (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} (memberName : String)
      (members : List StructMember) (member : StructMember)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hNotMapping2 : isMapping2 fields field = false)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hWordOffset : member.wordOffset = 0)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceStructMemberMultiSlotStmt fields
        (.setStructMember field key memberName value)

def BridgedSourceStructMemberMultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMemberMultiSlotStmt fields stmt

/-- A multi-slot, unpacked, wordOffset=0 `Stmt.setStructMember` source
write with a pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setStructMember_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember field key memberName value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, compileSetStructMember, hNotMapping2, hMembers,
    hFindMember, hUnpacked, hWordOffset, bind, Except.bind,
    Bool.false_eq_true, if_false] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr, pure, Pure.pure, Except.pure] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
          exact compileMappingSlotWrite_multiSlot_bridged fields field keyExpr
            valueExpr s!"setStructMember.{memberName}"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

theorem compileStmt_setStructMember_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember field key memberName value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt, compileSetStructMember, hNotMapping2, hMembers,
    hFindMember, hUnpacked, hWordOffset, bind, Except.bind,
    Bool.false_eq_true, if_false] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr, pure, Pure.pure, Except.pure] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
          exact compileMappingSlotWrite_multiSlot_noFuncDefs fields field
            keyExpr valueExpr s!"setStructMember.{memberName}"
            hMapping hSlots hOk

/-- Each statement in the multi-slot struct-member-write fragment compiles
to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_structMemberMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMemberMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember field memberName members member hKey hValue hNotMapping2
      hMembers hFindMember hUnpacked hWordOffset hMapping hSlots =>
      exact compileStmt_setStructMember_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field memberName
        members member hKey hValue hNotMapping2 hMembers hFindMember hUnpacked
        hWordOffset hMapping hSlots hOk

theorem compileStmt_structMemberMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMemberMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember field memberName members member hKey hValue hNotMapping2
      hMembers hFindMember hUnpacked hWordOffset hMapping hSlots =>
      exact compileStmt_setStructMember_multiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field memberName
        members member hNotMapping2 hMembers hFindMember hUnpacked hWordOffset
        hMapping hSlots hOk

/-- Lists of multi-slot struct-member-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMemberMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMemberMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceStructMemberMultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceStructMemberMultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMemberMultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_structMemberMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMemberMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceStructMemberMultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_structMemberMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setStructMember2`
(wordOffset = 0)

Multi-slot `setStructMember2` writes on a `mappingStruct2` field with ≥ 2
write slots hit the `_` arm of `compileSetStructMember2`'s `match slots`.
With `member.wordOffset = 0` and `member.packed = none`, the emission is
identical to multi-slot `setMapping2` (wordOffset=0), so the same
per-sstore helper `bridgedStraightStmts_multiSlot_sstore_mapping2`
applies. -/

/-- Unpacked, wordOffset=0 `setStructMember2` on a multi-slot
`mappingStruct2` field with pure bridged key1/key2/value. -/
inductive BridgedSourceStructMember2MultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setStructMember2 (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key1 key2 value : Expr} (memberName : String)
      (members : List StructMember) (member : StructMember)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hWordOffset : member.wordOffset = 0)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceStructMember2MultiSlotStmt fields
        (.setStructMember2 field key1 key2 memberName value)

def BridgedSourceStructMember2MultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMember2MultiSlotStmt fields stmt

/-- A multi-slot, unpacked, wordOffset=0 `Stmt.setStructMember2` source
write with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setStructMember2_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember2 field key1 key2 memberName value) =
          .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStructMember2 at hOk
  simp [hMapping2, hMembers, hFindMember, hUnpacked, hWordOffset, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              refine BridgedStmts_singleton_block ?_
              -- After simp, body is:
              --   let_ __compat_key1 :: let_ __compat_key2 :: let_ __compat_value
              --     :: sstore_slot0 :: sstore_slot1 :: slotsRest.map sstoreFn
              intro stmt hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey1)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey2)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedValue)
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot0,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot0
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner0
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot1,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot1
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner1
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              · have hSstore : BridgedStraightStmt stmt :=
                  bridgedStraightStmts_multiSlot_sstore_mapping2 slotsRest stmt
                    (by simpa using hMem)
                exact BridgedStmt.straight _ hSstore

theorem compileStmt_setStructMember2_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hWordOffset : member.wordOffset = 0)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember2 field key1 key2 memberName value) =
          .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  simp only [compileStmt] at hOk
  unfold compileSetStructMember2 at hOk
  simp [hMapping2, hMembers, hFindMember, hUnpacked, hWordOffset, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst out
              simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]
              simpa [Function.comp_def] using
                yulStmtsContainFuncDef_multiSlot_sstore_mapping2 slotsRest

/-- Each statement in the multi-slot struct-member2-write fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_structMember2MultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMember2MultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember2 field memberName members member hKey1 hKey2 hValue hMapping2
      hMembers hFindMember hUnpacked hWordOffset hSlots =>
      exact compileStmt_setStructMember2_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field memberName
        members member hKey1 hKey2 hValue hMapping2 hMembers hFindMember hUnpacked
        hWordOffset hSlots hOk

theorem compileStmt_structMember2MultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMember2MultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember2 field memberName members member hKey1 hKey2 hValue hMapping2
      hMembers hFindMember hUnpacked hWordOffset hSlots =>
      exact compileStmt_setStructMember2_multiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        memberName members member hMapping2 hMembers hFindMember hUnpacked
        hWordOffset hSlots hOk

/-- Lists of multi-slot struct-member2-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMember2MultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMember2MultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceStructMember2MultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceStructMember2MultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMember2MultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_structMember2MultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMember2MultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceStructMember2MultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_structMember2MultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setMappingWord`
(wordOffset=0)

`Stmt.setMappingWord field key wordOffset value` dispatches in
`Compile.lean:88` directly to
`compileMappingSlotWrite fields field keyExpr valueExpr "setMappingWord"
  wordOffset`. For a declared `isMapping` field with ≥ 2 write slots and
`wordOffset = 0`, the emitted shape is identical to multi-slot
`setMapping` — so we reuse `compileMappingSlotWrite_multiSlot_bridged`
directly (cd135ff7, line 8827). Mirrors
`compileStmt_setMappingUint_multiSlot_bridged` (line 8940). -/

/-- A multi-slot `Stmt.setMappingWord field key 0 value` source write
with pure bridged key and value at `wordOffset = 0` on a mapping field
whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMappingWordMultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setMappingWord (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} (wordOffset : Nat)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hWordOffset : wordOffset = 0) :
      BridgedSourceMappingWordMultiSlotStmt fields
        (.setMappingWord field key wordOffset value)

def BridgedSourceMappingWordMultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWordMultiSlotStmt fields stmt

/-- A multi-slot `Stmt.setMappingWord` source write at `wordOffset = 0`
with pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingWord_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (wordOffset : Nat)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingWord field key wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_bridged fields field keyExpr
            valueExpr "setMappingWord"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hOk

theorem compileStmt_setMappingWord_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (wordOffset : Nat)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingWord field key wordOffset value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_noFuncDefs fields field
            keyExpr valueExpr "setMappingWord" hMapping hSlots hOk

/-- Each statement in the multi-slot mappingWord-write fragment compiles
to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWordMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingWord field wordOffset hKey hValue hMapping hSlots hWordOffset =>
      exact compileStmt_setMappingWord_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field wordOffset
        hKey hValue hMapping hSlots hWordOffset hOk

theorem compileStmt_mappingWordMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWordMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingWord field wordOffset hKey hValue hMapping hSlots hWordOffset =>
      exact compileStmt_setMappingWord_multiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        wordOffset hMapping hSlots hWordOffset hOk

/-- Lists of multi-slot mappingWord-write source statements compile to
Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWordMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingWordMultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingWordMultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWordMultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mappingWordMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWordMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceMappingWordMultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mappingWordMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setMapping2Word`
(wordOffset=0)

`Stmt.setMapping2Word field key1 key2 wordOffset value` dispatches in
`Compile.lean:103` to `compileSetMapping2Word`. For a declared
`isMapping2` field with ≥ 2 write slots and `wordOffset = 0`, the
`if wordOffset == 0 then outerSlot else ...` conditional collapses to
`outerSlot`, making the emission identical to multi-slot
`setMapping2`. Closure mirrors `compileStmt_setMapping2_multiSlot_bridged`
(defa6150) with an extra `subst hWordOffset`. -/

/-- A multi-slot `Stmt.setMapping2Word field key1 key2 0 value` source
write with pure bridged key1/key2/value at `wordOffset = 0` on a
declared `isMapping2` field whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMapping2WordMultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setMapping2Word (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key1 key2 value : Expr} (wordOffset : Nat)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hWordOffset : wordOffset = 0) :
      BridgedSourceMapping2WordMultiSlotStmt fields
        (.setMapping2Word field key1 key2 wordOffset value)

def BridgedSourceMapping2WordMultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMapping2WordMultiSlotStmt fields stmt

/-- A multi-slot `Stmt.setMapping2Word` source write at `wordOffset = 0`
with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2Word_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} (wordOffset : Nat)
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2Word field key1 key2 wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt] at hOk
  unfold compileSetMapping2Word at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              refine BridgedStmts_singleton_block ?_
              intro stmt hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey1)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey2)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedValue)
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot0,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot0
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner0
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot1,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot1
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_mapping _ _ _
                    hInner1
                    (BridgedExpr.ident "__compat_key2")
                    (BridgedExpr.ident "__compat_value"))
              · have hSstore : BridgedStraightStmt stmt :=
                  bridgedStraightStmts_multiSlot_sstore_mapping2 slotsRest stmt
                    (by simpa using hMem)
                exact BridgedStmt.straight _ hSstore

theorem compileStmt_setMapping2Word_multiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} (wordOffset : Nat)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hWordOffset : wordOffset = 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2Word field key1 key2 wordOffset value) = .ok out →
      Native.yulStmtsContainFuncDef out = false := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt] at hOk
  unfold compileSetMapping2Word at hOk
  simp [hMapping2, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst out
              simp [Native.yulStmtContainsFuncDef, Native.yulStmtsContainFuncDef]
              simpa [Function.comp_def] using
                yulStmtsContainFuncDef_multiSlot_sstore_mapping2 slotsRest

/-- Each statement in the multi-slot mapping2Word-write fragment compiles
to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mapping2WordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMapping2WordMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2Word field wordOffset hKey1 hKey2 hValue hMapping2 hSlots hWordOffset =>
      exact compileStmt_setMapping2Word_multiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field wordOffset
        hKey1 hKey2 hValue hMapping2 hSlots hWordOffset hOk

theorem compileStmt_mapping2WordMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMapping2WordMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        Native.yulStmtsContainFuncDef out = false := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2Word field wordOffset hKey1 hKey2 hValue hMapping2 hSlots hWordOffset =>
      exact compileStmt_setMapping2Word_multiSlot_noFuncDefs fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        wordOffset hMapping2 hSlots hWordOffset hOk

/-- Lists of multi-slot mapping2Word-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mapping2WordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMapping2WordMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMapping2WordMultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMapping2WordMultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mapping2WordMultiSlot_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

theorem compileStmtList_mapping2WordMultiSlot_noFuncDefs
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMapping2WordMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        Native.yulStmtsContainFuncDef out = false :=
  compileStmtList_noFuncDefs_of_forall fields events errors dynamicSource
    internalRetNames isInternal (BridgedSourceMapping2WordMultiSlotStmt fields)
    (fun inScopeNames {_} {_} hStmt hOk =>
      compileStmt_mapping2WordMultiSlot_noFuncDefs fields events errors
        dynamicSource internalRetNames isInternal inScopeNames hStmt hOk)

/-! ## Source statement body closure: multi-slot `setMappingWord`
(wordOffset ≠ 0)

`Stmt.setMappingWord field key wordOffset value` with `wordOffset ≠ 0`
on a multi-slot (≥ 2 slots) `isMapping` field. `compileMappingSlotWrite`
multi-slot branch emits
`block [let __compat_key := keyExpr, let __compat_value := valueExpr,
       sstore(add(mappingSlot(lit slot, __compat_key), lit wordOffset),
              __compat_value) for each slot]`.
The per-slot element is an `expr_sstore_add` over a bridged mappingSlot
subexpression, so closure delegates to a new shared helper
`bridgedStraightStmts_multiSlot_sstore_mapping_add` that mirrors
`bridgedStraightStmts_multiSlot_sstore_mapping` (line 8797) but with the
extra `add` layer. -/

/-- Helper: the `slots.map` fragment in the multi-slot nonzero-offset
compatibility branch of `compileMappingSlotWrite` is
`BridgedStraightStmts`. Each element is
`sstore(add(mappingSlot(lit slot, ident "__compat_key"),
lit wordOffset), ident "__compat_value")`. -/
private theorem bridgedStraightStmts_multiSlot_sstore_mapping_add
    (slots : List Nat) (wordOffset : Nat) :
    BridgedStraightStmts
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "add" [
              Compiler.Yul.YulExpr.call "mappingSlot"
                [Compiler.Yul.YulExpr.lit slot,
                 Compiler.Yul.YulExpr.ident "__compat_key"],
              Compiler.Yul.YulExpr.lit wordOffset],
            Compiler.Yul.YulExpr.ident "__compat_value"])) := by
  induction slots with
  | nil => intro stmt hMem; cases hMem
  | cons s rest ih =>
      intro stmt hMem
      simp only [List.map_cons, List.mem_cons] at hMem
      rcases hMem with hMem | hMem
      · subst hMem
        have hMappingExpr : BridgedExpr
            (Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit s,
               Compiler.Yul.YulExpr.ident "__compat_key"]) := by
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg hArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
            rcases hArg with hArg | hArg
            · subst hArg; exact BridgedExpr.lit s
            · subst hArg; exact BridgedExpr.ident "__compat_key"
        exact BridgedStraightStmt.expr_sstore_add
          (Compiler.Yul.YulExpr.call "mappingSlot"
            [Compiler.Yul.YulExpr.lit s,
             Compiler.Yul.YulExpr.ident "__compat_key"])
          (Compiler.Yul.YulExpr.lit wordOffset)
          (Compiler.Yul.YulExpr.ident "__compat_value")
          hMappingExpr
          (BridgedExpr.lit wordOffset)
          (BridgedExpr.ident "__compat_value")
      · exact ih stmt hMem

/-- Shared helper: `compileMappingSlotWrite` on a multi-slot mapping
(≥ 2 slots) with `wordOffset ≠ 0` and pre-compiled bridged key/value
expressions produces a `BridgedStmts` list. Mirrors
`compileMappingSlotWrite_multiSlot_bridged` (cd135ff7, line 8827) but
with the `add`-wrapped sstore shape. -/
private theorem compileMappingSlotWrite_multiSlot_nonzero_bridged
    (fields : List Field) (field : String)
    {slot0 slot1 : Nat} {slotsRest : List Nat} {wordOffset : Nat}
    (keyExpr valueExpr : YulExpr) (label : String)
    (hKey : BridgedExpr keyExpr) (hValue : BridgedExpr valueExpr)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileMappingSlotWrite fields field keyExpr valueExpr label wordOffset = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp [compileMappingSlotWrite, hMapping, hSlots, hBeq, Pure.pure, Except.pure] at hOk
  subst hOk
  refine BridgedStmts_singleton_block ?_
  intro stmt hMem
  simp only [List.mem_cons] at hMem
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ hKey)
  rcases hMem with hEq | hMem
  · subst hEq
    exact BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ hValue)
  · have hSstore : BridgedStraightStmt stmt :=
      bridgedStraightStmts_multiSlot_sstore_mapping_add
        (slot0 :: slot1 :: slotsRest) wordOffset stmt (by simpa using hMem)
    exact BridgedStmt.straight _ hSstore

/-- A multi-slot `Stmt.setMappingWord field key wordOffset value` source
write with pure bridged key and value at `wordOffset ≠ 0` on a mapping
field whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMappingWordMultiSlotNonzeroStmt (fields : List Field) :
    Stmt → Prop
  | setMappingWord (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} (wordOffset : Nat)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hNonzero : wordOffset ≠ 0) :
      BridgedSourceMappingWordMultiSlotNonzeroStmt fields
        (.setMappingWord field key wordOffset value)

def BridgedSourceMappingWordMultiSlotNonzeroStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingWordMultiSlotNonzeroStmt fields stmt

/-- A multi-slot `Stmt.setMappingWord` source write at `wordOffset ≠ 0`
with pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingWord_multiSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (wordOffset : Nat)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMappingWord field key wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr] at hOk
          exact compileMappingSlotWrite_multiSlot_nonzero_bridged fields field
            keyExpr valueExpr "setMappingWord"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hNonzero hOk

/-- Each statement in the multi-slot nonzero-offset mappingWord-write
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingWordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingWordMultiSlotNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingWord field wordOffset hKey hValue hMapping hSlots hNonzero =>
      exact compileStmt_setMappingWord_multiSlot_nonzero_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field wordOffset
        hKey hValue hMapping hSlots hNonzero hOk

/-- Lists of multi-slot nonzero-offset mappingWord-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingWordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingWordMultiSlotNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingWordMultiSlotNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingWordMultiSlotNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingWordMultiSlotNonzero_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: multi-slot `setMapping2Word`
(wordOffset ≠ 0)

`Stmt.setMapping2Word field key1 key2 wordOffset value` with
`wordOffset ≠ 0` on a multi-slot (≥ 2 slots) `isMapping2` field.
`compileSetMapping2Word` multi-slot branch emits
`block [let __compat_key1 := key1Expr, let __compat_key2 := key2Expr,
       let __compat_value := valueExpr,
       sstore(add(mappingSlot(mappingSlot(lit slot, __compat_key1),
                               __compat_key2),
                   lit wordOffset),
              __compat_value) for each slot]`.
Per-slot element is an `expr_sstore_add` over a nested mappingSlot
subexpression. Closure mirrors the wordOffset=0 multi-slot case
(defa6150) with an extra `add` layer, using new helper
`bridgedStraightStmts_multiSlot_sstore_mapping2_add`. -/

/-- Helper: the `slots.map` fragment in the multi-slot nonzero-offset
compatibility branch of `compileSetMapping2Word` is
`BridgedStraightStmts`. Each element is
`sstore(add(mappingSlot(mappingSlot(lit slot, ident "__compat_key1"),
                        ident "__compat_key2"),
           lit wordOffset),
       ident "__compat_value")`. -/
private theorem bridgedStraightStmts_multiSlot_sstore_mapping2_add
    (slots : List Nat) (wordOffset : Nat) :
    BridgedStraightStmts
      (slots.map fun slot =>
        Compiler.Yul.YulStmt.expr
          (Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "add" [
              Compiler.Yul.YulExpr.call "mappingSlot" [
                Compiler.Yul.YulExpr.call "mappingSlot"
                  [Compiler.Yul.YulExpr.lit slot,
                   Compiler.Yul.YulExpr.ident "__compat_key1"],
                Compiler.Yul.YulExpr.ident "__compat_key2"],
              Compiler.Yul.YulExpr.lit wordOffset],
            Compiler.Yul.YulExpr.ident "__compat_value"])) := by
  induction slots with
  | nil => intro stmt hMem; cases hMem
  | cons s rest ih =>
      intro stmt hMem
      simp only [List.map_cons, List.mem_cons] at hMem
      rcases hMem with hMem | hMem
      · subst hMem
        have hInnerBridged : BridgedExpr
            (Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit s,
               Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg hArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
            rcases hArg with hArg | hArg
            · subst hArg; exact BridgedExpr.lit s
            · subst hArg; exact BridgedExpr.ident "__compat_key1"
        have hOuterBridged : BridgedExpr
            (Compiler.Yul.YulExpr.call "mappingSlot" [
              Compiler.Yul.YulExpr.call "mappingSlot"
                [Compiler.Yul.YulExpr.lit s,
                 Compiler.Yul.YulExpr.ident "__compat_key1"],
              Compiler.Yul.YulExpr.ident "__compat_key2"]) := by
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg hArg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
            rcases hArg with hArg | hArg
            · subst hArg; exact hInnerBridged
            · subst hArg; exact BridgedExpr.ident "__compat_key2"
        exact BridgedStraightStmt.expr_sstore_add
          (Compiler.Yul.YulExpr.call "mappingSlot" [
            Compiler.Yul.YulExpr.call "mappingSlot"
              [Compiler.Yul.YulExpr.lit s,
               Compiler.Yul.YulExpr.ident "__compat_key1"],
            Compiler.Yul.YulExpr.ident "__compat_key2"])
          (Compiler.Yul.YulExpr.lit wordOffset)
          (Compiler.Yul.YulExpr.ident "__compat_value")
          hOuterBridged
          (BridgedExpr.lit wordOffset)
          (BridgedExpr.ident "__compat_value")
      · exact ih stmt hMem

/-- A multi-slot `Stmt.setMapping2Word field key1 key2 wordOffset value`
source write with pure bridged key1/key2/value at `wordOffset ≠ 0` on a
declared `isMapping2` field whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMapping2WordMultiSlotNonzeroStmt (fields : List Field) :
    Stmt → Prop
  | setMapping2Word (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key1 key2 value : Expr} {wordOffset : Nat}
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hNonzero : wordOffset ≠ 0) :
      BridgedSourceMapping2WordMultiSlotNonzeroStmt fields
        (.setMapping2Word field key1 key2 wordOffset value)

def BridgedSourceMapping2WordMultiSlotNonzeroStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMapping2WordMultiSlotNonzeroStmt fields stmt

/-- A multi-slot `Stmt.setMapping2Word` source write at `wordOffset ≠ 0`
with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setMapping2Word_multiSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} {wordOffset : Nat}
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hNonzero : wordOffset ≠ 0) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setMapping2Word field key1 key2 wordOffset value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp only [compileStmt] at hOk
  unfold compileSetMapping2Word at hOk
  simp [hMapping2, hSlots, hBeq] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              refine BridgedStmts_singleton_block ?_
              intro stmt hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey1)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey2)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedValue)
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot0,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot0
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                have hOuter0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot" [
                      Compiler.Yul.YulExpr.call "mappingSlot"
                        [Compiler.Yul.YulExpr.lit slot0,
                         Compiler.Yul.YulExpr.ident "__compat_key1"],
                      Compiler.Yul.YulExpr.ident "__compat_key2"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact hInner0
                    · subst hArg; exact BridgedExpr.ident "__compat_key2"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_add _ _ _
                    hOuter0
                    (BridgedExpr.lit wordOffset)
                    (BridgedExpr.ident "__compat_value"))
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot1,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot1
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                have hOuter1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot" [
                      Compiler.Yul.YulExpr.call "mappingSlot"
                        [Compiler.Yul.YulExpr.lit slot1,
                         Compiler.Yul.YulExpr.ident "__compat_key1"],
                      Compiler.Yul.YulExpr.ident "__compat_key2"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact hInner1
                    · subst hArg; exact BridgedExpr.ident "__compat_key2"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_add _ _ _
                    hOuter1
                    (BridgedExpr.lit wordOffset)
                    (BridgedExpr.ident "__compat_value"))
              · have hSstore : BridgedStraightStmt stmt :=
                  bridgedStraightStmts_multiSlot_sstore_mapping2_add slotsRest
                    wordOffset stmt (by simpa using hMem)
                exact BridgedStmt.straight _ hSstore

/-- Each statement in the multi-slot mapping2Word-write wordOffset≠0
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mapping2WordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMapping2WordMultiSlotNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMapping2Word field hKey1 hKey2 hValue hMapping2 hSlots hNonzero =>
      exact compileStmt_setMapping2Word_multiSlot_nonzero_bridged fields events errors
        dynamicSource internalRetNames isInternal inScopeNames field
        hKey1 hKey2 hValue hMapping2 hSlots hNonzero hOk

/-- Lists of multi-slot mapping2Word-write wordOffset≠0 source statements
compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mapping2WordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMapping2WordMultiSlotNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMapping2WordMultiSlotNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMapping2WordMultiSlotNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mapping2WordMultiSlotNonzero_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: multi-slot `setStructMember`
(wordOffset ≠ 0)

Multi-slot unpacked `Stmt.setStructMember` writes with `member.wordOffset ≠ 0`
on a `mappingStruct` field with ≥ 2 write slots dispatch through
`compileMappingSlotWrite fields field keyExpr valueExpr label member.wordOffset`.
The existing private helper `compileMappingSlotWrite_multiSlot_nonzero_bridged`
(c0642e7d) already closes that target shape, so this section simply
threads the struct-member preconditions through it, mirroring the
`setStructMember` wordOffset=0 multi-slot section. -/

/-- Unpacked, wordOffset ≠ 0 `setStructMember` on a multi-slot
`mappingStruct` field with a pure bridged key and value. -/
inductive BridgedSourceStructMemberMultiSlotNonzeroStmt (fields : List Field) :
    Stmt → Prop
  | setStructMember (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} (memberName : String)
      (members : List StructMember) (member : StructMember)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hNotMapping2 : isMapping2 fields field = false)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hNonzero : member.wordOffset ≠ 0)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceStructMemberMultiSlotNonzeroStmt fields
        (.setStructMember field key memberName value)

def BridgedSourceStructMemberMultiSlotNonzeroStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMemberMultiSlotNonzeroStmt fields stmt

/-- A multi-slot, unpacked, wordOffset ≠ 0 `Stmt.setStructMember` source
write with a pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setStructMember_multiSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hNotMapping2 : isMapping2 fields field = false)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hNonzero : member.wordOffset ≠ 0)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember field key memberName value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  simp only [compileStmt, compileSetStructMember, hNotMapping2, hMembers,
    hFindMember, hUnpacked, bind, Except.bind,
    Bool.false_eq_true, if_false] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr, pure, Pure.pure, Except.pure] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err =>
          simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, pure, Pure.pure, Except.pure] at hOk
          exact compileMappingSlotWrite_multiSlot_nonzero_bridged fields field
            keyExpr valueExpr s!"setStructMember.{memberName}"
            (compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr)
            (compileExpr_bridgedSource fields dynamicSource hValue hValueExpr)
            hMapping hSlots hNonzero hOk

/-- Each statement in the multi-slot nonzero-offset struct-member-write
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_structMemberMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMemberMultiSlotNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember field memberName members member hKey hValue hNotMapping2
      hMembers hFindMember hUnpacked hNonzero hMapping hSlots =>
      exact compileStmt_setStructMember_multiSlot_nonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        memberName members member hKey hValue hNotMapping2 hMembers hFindMember
        hUnpacked hNonzero hMapping hSlots hOk

/-- Lists of multi-slot nonzero-offset struct-member-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMemberMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMemberMultiSlotNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceStructMemberMultiSlotNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceStructMemberMultiSlotNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMemberMultiSlotNonzero_bridged fields events
                  errors dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: multi-slot `setStructMember2`
(wordOffset ≠ 0)

Multi-slot unpacked `Stmt.setStructMember2` writes with
`member.wordOffset ≠ 0` emit the same shape as multi-slot
`setMapping2Word` wordOffset≠0: an outer block with three let-bindings
(`__compat_key1`, `__compat_key2`, `__compat_value`) followed by one
`sstore` per write slot whose slot argument is
`add(mappingSlot(mappingSlot(lit slot, __compat_key1), __compat_key2),
lit wordOffset)`. The existing per-slot helper
`bridgedStraightStmts_multiSlot_sstore_mapping2_add` (6f1ad0bf) already
bridges that shape, so this section simply threads the struct-member
preconditions through the same five-way enumeration used for
`compileStmt_setMapping2Word_multiSlot_nonzero_bridged`. -/

/-- Unpacked, wordOffset ≠ 0 `setStructMember2` on a multi-slot
`mappingStruct2` field with pure bridged key1/key2/value. -/
inductive BridgedSourceStructMember2MultiSlotNonzeroStmt (fields : List Field) :
    Stmt → Prop
  | setStructMember2 (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key1 key2 value : Expr} (memberName : String)
      (members : List StructMember) (member : StructMember)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (hValue : BridgedSourceExpr value)
      (hMapping2 : isMapping2 fields field = true)
      (hMembers : findStructMembers fields field = some members)
      (hFindMember : findStructMember members memberName = some member)
      (hUnpacked : member.packed = none)
      (hNonzero : member.wordOffset ≠ 0)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest)) :
      BridgedSourceStructMember2MultiSlotNonzeroStmt fields
        (.setStructMember2 field key1 key2 memberName value)

def BridgedSourceStructMember2MultiSlotNonzeroStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceStructMember2MultiSlotNonzeroStmt fields stmt

/-- A multi-slot, unpacked, wordOffset ≠ 0 `Stmt.setStructMember2` source
write with pure bridged key1/key2/value compiles to `BridgedStmts`. -/
theorem compileStmt_setStructMember2_multiSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key1 key2 value : Expr} (memberName : String)
    (members : List StructMember) (member : StructMember)
    (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
    (hValue : BridgedSourceExpr value)
    (hMapping2 : isMapping2 fields field = true)
    (hMembers : findStructMembers fields field = some members)
    (hFindMember : findStructMember members memberName = some member)
    (hUnpacked : member.packed = none)
    (hNonzero : member.wordOffset ≠ 0)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest)) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames [] (.setStructMember2 field key1 key2 memberName value) =
          .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (member.wordOffset == 0) = false := by
    cases h : member.wordOffset with
    | zero => exact absurd h hNonzero
    | succ n => rfl
  simp only [compileStmt] at hOk
  unfold compileSetStructMember2 at hOk
  simp [hMapping2, hMembers, hFindMember, hUnpacked, hBeq, hSlots] at hOk
  cases hKey1Expr : compileExpr fields dynamicSource key1 with
  | error err => simp [hKey1Expr, bind, Except.bind] at hOk
  | ok key1Expr =>
      cases hKey2Expr : compileExpr fields dynamicSource key2 with
      | error err => simp [hKey1Expr, hKey2Expr, bind, Except.bind] at hOk
      | ok key2Expr =>
          cases hValueExpr : compileExpr fields dynamicSource value with
          | error err =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
          | ok valueExpr =>
              simp [hKey1Expr, hKey2Expr, hValueExpr, bind, Except.bind] at hOk
              subst hOk
              have hBridgedKey1 : BridgedExpr key1Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey1 hKey1Expr
              have hBridgedKey2 : BridgedExpr key2Expr :=
                compileExpr_bridgedSource fields dynamicSource hKey2 hKey2Expr
              have hBridgedValue : BridgedExpr valueExpr :=
                compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
              refine BridgedStmts_singleton_block ?_
              intro stmt hMem
              simp only [List.mem_cons] at hMem
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey1)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedKey2)
              rcases hMem with hEq | hMem
              · subst hEq
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.let_ _ _ hBridgedValue)
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot0,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot0
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                have hOuter0 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot" [
                      Compiler.Yul.YulExpr.call "mappingSlot"
                        [Compiler.Yul.YulExpr.lit slot0,
                         Compiler.Yul.YulExpr.ident "__compat_key1"],
                      Compiler.Yul.YulExpr.ident "__compat_key2"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact hInner0
                    · subst hArg; exact BridgedExpr.ident "__compat_key2"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_add _ _ _
                    hOuter0
                    (BridgedExpr.lit member.wordOffset)
                    (BridgedExpr.ident "__compat_value"))
              rcases hMem with hEq | hMem
              · subst hEq
                have hInner1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot"
                      [Compiler.Yul.YulExpr.lit slot1,
                       Compiler.Yul.YulExpr.ident "__compat_key1"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact BridgedExpr.lit slot1
                    · subst hArg; exact BridgedExpr.ident "__compat_key1"
                have hOuter1 : BridgedExpr
                    (Compiler.Yul.YulExpr.call "mappingSlot" [
                      Compiler.Yul.YulExpr.call "mappingSlot"
                        [Compiler.Yul.YulExpr.lit slot1,
                         Compiler.Yul.YulExpr.ident "__compat_key1"],
                      Compiler.Yul.YulExpr.ident "__compat_key2"]) := by
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg hArg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                    rcases hArg with hArg | hArg
                    · subst hArg; exact hInner1
                    · subst hArg; exact BridgedExpr.ident "__compat_key2"
                exact BridgedStmt.straight _
                  (BridgedStraightStmt.expr_sstore_add _ _ _
                    hOuter1
                    (BridgedExpr.lit member.wordOffset)
                    (BridgedExpr.ident "__compat_value"))
              · have hSstore : BridgedStraightStmt stmt :=
                  bridgedStraightStmts_multiSlot_sstore_mapping2_add slotsRest
                    member.wordOffset stmt (by simpa using hMem)
                exact BridgedStmt.straight _ hSstore

/-- Each statement in the multi-slot nonzero-offset struct-member2-write
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_structMember2MultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceStructMember2MultiSlotNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames isInternal
          inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setStructMember2 field memberName members member hKey1 hKey2 hValue hMapping2
      hMembers hFindMember hUnpacked hNonzero hSlots =>
      exact compileStmt_setStructMember2_multiSlot_nonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        memberName members member hKey1 hKey2 hValue hMapping2 hMembers
        hFindMember hUnpacked hNonzero hSlots hOk

/-- Lists of multi-slot nonzero-offset struct-member2-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_structMember2MultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceStructMember2MultiSlotNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
          isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceStructMember2MultiSlotNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceStructMember2MultiSlotNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_structMember2MultiSlotNonzero_bridged fields events
                  errors dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMappingPackedWord`
(wordOffset=0)

`Stmt.setMappingPackedWord field key 0 packed value` routes through
`compileMappingPackedSlotWrite fields field keyExpr valueExpr 0 packed
"setMappingPackedWord"`. When the mapping's declared write-slots list has
exactly one slot and `wordOffset = 0`, the emitted shape is a
one-element list wrapping a `YulStmt.block` with four `let_` bindings and
a terminating `sstore(mappingSlot(lit slot, keyExpr), or(ident, shl(...)))`.
Every inner expression is built from `and`/`or`/`not`/`shl`/`sload` —
all of which live in `bridgedBuiltins` — plus `lit`/`ident` wrappers, so
each statement is closed either by `BridgedStraightStmt.let_` over a
`BridgedExpr.call` or by `BridgedStraightStmt.expr_sstore_mapping`. -/

/-- A single-slot `Stmt.setMappingPackedWord field key 0 packed value`
source write with pure bridged key and value at `wordOffset = 0`, gated
by `packedBitsValid packed`. -/
inductive BridgedSourceMappingPackedWordStmt (fields : List Field) :
    Stmt → Prop
  | setMappingPackedWord (field : String) {slot : Nat} {key value : Expr}
      (wordOffset : Nat) (packed : PackedBits)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hWordOffset : wordOffset = 0)
      (hPacked : packedBitsValid packed = true) :
      BridgedSourceMappingPackedWordStmt fields
        (.setMappingPackedWord field key wordOffset packed value)

def BridgedSourceMappingPackedWordStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingPackedWordStmt fields stmt

/-- A single-slot `Stmt.setMappingPackedWord` source write at
`wordOffset = 0` with pure bridged key and value compiles to
`BridgedStmts`. -/
theorem compileStmt_setMappingPackedWord_singleSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot : Nat} {key value : Expr}
    (wordOffset : Nat) (packed : PackedBits)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hWordOffset : wordOffset = 0)
    (hPacked : packedBitsValid packed = true) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames
        [] (.setMappingPackedWord field key wordOffset packed value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, compileMappingPackedSlotWrite,
            hMapping, hPacked, hSlots, Pure.pure, Except.pure] at hOk
          subst hOk
          have hKeyBridged : BridgedExpr keyExpr :=
            compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr
          have _hValueBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
          have hMappingBase : BridgedExpr
              (Compiler.Yul.YulExpr.call "mappingSlot"
                [Compiler.Yul.YulExpr.lit slot, keyExpr]) := by
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.lit slot
              · subst hArg; exact hKeyBridged
          refine BridgedStmts_singleton_block ?_
          intro stmt hMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
          rcases hMem with rfl | rfl | rfl | rfl | rfl
          · -- let_ "__compat_value" valueExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ _hValueBridged)
          · -- let_ "__compat_packed" (and(ident "__compat_value", lit maskNat))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_value"
              · subst hArg; exact BridgedExpr.lit _
          · -- let_ "__compat_slot_word" (sload(mappingSlot(lit slot, keyExpr)))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              subst hArg; exact hMappingBase
          · -- let_ "__compat_slot_cleared"
            --   (and(ident "__compat_slot_word", not(lit shiftedMaskNat)))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_slot_word"
              · subst hArg
                apply BridgedExpr.call
                · exact Or.inl (by decide)
                · intro arg' hArg'
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hArg'
                  subst hArg'; exact BridgedExpr.lit _
          · -- expr (sstore(mappingSlot(lit slot, keyExpr),
            --         or(ident "__compat_slot_cleared",
            --            shl(lit packed.offset, ident "__compat_packed"))))
            have hVal : BridgedExpr
                (Compiler.Yul.YulExpr.call "or" [
                  Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
                  Compiler.Yul.YulExpr.call "shl" [
                    Compiler.Yul.YulExpr.lit packed.offset,
                    Compiler.Yul.YulExpr.ident "__compat_packed"]]) := by
              apply BridgedExpr.call
              · exact Or.inl (by decide)
              · intro arg hArg
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                rcases hArg with hArg | hArg
                · subst hArg; exact BridgedExpr.ident "__compat_slot_cleared"
                · subst hArg
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg' hArg'
                    simp only [List.mem_cons, List.not_mem_nil,
                      or_false] at hArg'
                    rcases hArg' with hArg' | hArg'
                    · subst hArg'; exact BridgedExpr.lit _
                    · subst hArg'; exact BridgedExpr.ident "__compat_packed"
            exact BridgedStmt.straight _
              (BridgedStraightStmt.expr_sstore_mapping
                (Compiler.Yul.YulExpr.lit slot) keyExpr _
                (BridgedExpr.lit slot) hKeyBridged hVal)

/-- Each statement in the mappingPackedWord-write fragment compiles to Yul
satisfying `BridgedStmts`. -/
theorem compileStmt_mappingPackedWord_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingPackedWordStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingPackedWord field wordOffset packed hKey hValue hMapping hSlots
      hWordOffset hPacked =>
      exact compileStmt_setMappingPackedWord_singleSlot_bridged fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        wordOffset packed hKey hValue hMapping hSlots hWordOffset hPacked hOk

/-- Lists of single-slot mappingPackedWord-write source statements compile
to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingPackedWord_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingPackedWordStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
      cases hHead : compileStmt fields events errors dynamicSource
          internalRetNames isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceMappingPackedWordStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingPackedWordStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingPackedWord_bridged fields events errors
                  dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: single-slot `setMappingPackedWord`
(wordOffset ≠ 0)

When `wordOffset ≠ 0`, `compileMappingPackedSlotWrite` on a single-slot
mapping emits a `YulStmt.block` whose `__compat_slot_word` `sload`
argument and whose terminating `sstore` slot are both
`add(mappingSlot(lit slot, keyExpr), lit wordOffset)` rather than the
bare `mappingSlot`. The extra `add` layer is bridged via
`BridgedExpr.call "add"` (since `add ∈ bridgedBuiltins`) and, for the
final sstore, via `BridgedStraightStmt.expr_sstore_add`. -/

/-- A single-slot `Stmt.setMappingPackedWord field key wordOffset packed
value` source write with pure bridged key and value at `wordOffset ≠ 0`,
gated by `packedBitsValid packed`. -/
inductive BridgedSourceMappingPackedWordNonzeroStmt (fields : List Field) :
    Stmt → Prop
  | setMappingPackedWord (field : String) {slot wordOffset : Nat}
      {key value : Expr} (packed : PackedBits)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field = some [slot])
      (hNonzero : wordOffset ≠ 0)
      (hPacked : packedBitsValid packed = true) :
      BridgedSourceMappingPackedWordNonzeroStmt fields
        (.setMappingPackedWord field key wordOffset packed value)

def BridgedSourceMappingPackedWordNonzeroStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingPackedWordNonzeroStmt fields stmt

/-- A single-slot `Stmt.setMappingPackedWord` source write at
`wordOffset ≠ 0` with pure bridged key and value compiles to
`BridgedStmts`. -/
theorem compileStmt_setMappingPackedWord_singleSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot wordOffset : Nat} {key value : Expr}
    (packed : PackedBits)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field = some [slot])
    (hNonzero : wordOffset ≠ 0)
    (hPacked : packedBitsValid packed = true) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames
        [] (.setMappingPackedWord field key wordOffset packed value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, compileMappingPackedSlotWrite,
            hMapping, hPacked, hSlots, hBeq, Pure.pure, Except.pure] at hOk
          subst hOk
          have hKeyBridged : BridgedExpr keyExpr :=
            compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr
          have _hValueBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
          have hMappingBase : BridgedExpr
              (Compiler.Yul.YulExpr.call "mappingSlot"
                [Compiler.Yul.YulExpr.lit slot, keyExpr]) := by
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.lit slot
              · subst hArg; exact hKeyBridged
          have hWriteSlot : BridgedExpr
              (Compiler.Yul.YulExpr.call "add" [
                Compiler.Yul.YulExpr.call "mappingSlot"
                  [Compiler.Yul.YulExpr.lit slot, keyExpr],
                Compiler.Yul.YulExpr.lit wordOffset]) := by
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact hMappingBase
              · subst hArg; exact BridgedExpr.lit wordOffset
          refine BridgedStmts_singleton_block ?_
          intro stmt hMem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
          rcases hMem with rfl | rfl | rfl | rfl | rfl
          · -- let_ "__compat_value" valueExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ _hValueBridged)
          · -- let_ "__compat_packed" (and(ident "__compat_value", lit maskNat))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_value"
              · subst hArg; exact BridgedExpr.lit _
          · -- let_ "__compat_slot_word" (sload(add(mappingBase, lit wordOffset)))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              subst hArg; exact hWriteSlot
          · -- let_ "__compat_slot_cleared"
            --   (and(ident "__compat_slot_word", not(lit shiftedMaskNat)))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_slot_word"
              · subst hArg
                apply BridgedExpr.call
                · exact Or.inl (by decide)
                · intro arg' hArg'
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hArg'
                  subst hArg'; exact BridgedExpr.lit _
          · -- expr (sstore(add(mappingBase, lit wordOffset),
            --         or(ident "__compat_slot_cleared",
            --            shl(lit packed.offset, ident "__compat_packed"))))
            have hVal : BridgedExpr
                (Compiler.Yul.YulExpr.call "or" [
                  Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
                  Compiler.Yul.YulExpr.call "shl" [
                    Compiler.Yul.YulExpr.lit packed.offset,
                    Compiler.Yul.YulExpr.ident "__compat_packed"]]) := by
              apply BridgedExpr.call
              · exact Or.inl (by decide)
              · intro arg hArg
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
                rcases hArg with hArg | hArg
                · subst hArg; exact BridgedExpr.ident "__compat_slot_cleared"
                · subst hArg
                  apply BridgedExpr.call
                  · exact Or.inl (by decide)
                  · intro arg' hArg'
                    simp only [List.mem_cons, List.not_mem_nil,
                      or_false] at hArg'
                    rcases hArg' with hArg' | hArg'
                    · subst hArg'; exact BridgedExpr.lit _
                    · subst hArg'; exact BridgedExpr.ident "__compat_packed"
            exact BridgedStmt.straight _
              (BridgedStraightStmt.expr_sstore_add
                (Compiler.Yul.YulExpr.call "mappingSlot"
                  [Compiler.Yul.YulExpr.lit slot, keyExpr])
                (Compiler.Yul.YulExpr.lit wordOffset) _
                hMappingBase (BridgedExpr.lit wordOffset) hVal)

/-- Each statement in the wordOffset≠0 mappingPackedWord-write fragment
compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingPackedWordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt}, BridgedSourceMappingPackedWordNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingPackedWord field packed hKey hValue hMapping hSlots hNonzero
      hPacked =>
      exact compileStmt_setMappingPackedWord_singleSlot_nonzero_bridged fields
        events errors dynamicSource internalRetNames isInternal inScopeNames
        field packed hKey hValue hMapping hSlots hNonzero hPacked hOk

/-- Lists of single-slot wordOffset≠0 mappingPackedWord-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingPackedWordNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingPackedWordNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
      cases hHead : compileStmt fields events errors dynamicSource
          internalRetNames isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingPackedWordNonzeroStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingPackedWordNonzeroStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingPackedWordNonzero_bridged fields events
                  errors dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: multi-slot `setMappingPackedWord`
(wordOffset = 0)

For a declared `isMapping` field with ≥ 2 write slots and `wordOffset = 0`,
`compileMappingPackedSlotWrite` emits one outer `YulStmt.block` whose body
is `[let_ __compat_key keyExpr, let_ __compat_value valueExpr,
  let_ __compat_packed (and(ident "__compat_value", lit maskNat))] ++
  slots.map (fun slot => YulStmt.block [innerThreeStmts slot])`. Each
inner block contains `let_ __compat_slot_word (sload(mappingSlot(lit slot,
ident "__compat_key")))`, an and-not clearing assignment, and a
terminating `sstore(mappingSlot(lit slot, ident "__compat_key"),
or(cleared, shl(offset, packed)))`. Every inner expression uses only
`mappingSlot`/`sload`/`and`/`not`/`or`/`shl` (all in `bridgedBuiltins`)
over `ident`/`lit` leaves, so every inner statement is either a
`let_`/`straight` BridgedStmt or an `expr_sstore_mapping` straight stmt
wrapped in an inner `BridgedStmts_singleton_block`. -/

/-- Helper: for any `slot` and valid `packed`, the three-stmt inner block
`YulStmt.block [sload-let, cleared-let, sstore-expr]` produced by the
multi-slot `compileMappingPackedSlotWrite` wordOffset=0 branch is a
`BridgedStmt`. -/
private theorem bridgedStmt_packedInnerBlock_wordOffsetZero
    (slot : Nat) (packed : PackedBits) :
    BridgedStmt (Compiler.Yul.YulStmt.block [
      Compiler.Yul.YulStmt.let_ "__compat_slot_word"
        (Compiler.Yul.YulExpr.call "sload" [
          Compiler.Yul.YulExpr.call "mappingSlot" [
            Compiler.Yul.YulExpr.lit slot,
            Compiler.Yul.YulExpr.ident "__compat_key"]]),
      Compiler.Yul.YulStmt.let_ "__compat_slot_cleared"
        (Compiler.Yul.YulExpr.call "and" [
          Compiler.Yul.YulExpr.ident "__compat_slot_word",
          Compiler.Yul.YulExpr.call "not" [
            Compiler.Yul.YulExpr.lit (packedShiftedMaskNat packed)]]),
      Compiler.Yul.YulStmt.expr (
        Compiler.Yul.YulExpr.call "sstore" [
          Compiler.Yul.YulExpr.call "mappingSlot" [
            Compiler.Yul.YulExpr.lit slot,
            Compiler.Yul.YulExpr.ident "__compat_key"],
          Compiler.Yul.YulExpr.call "or" [
            Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
            Compiler.Yul.YulExpr.call "shl" [
              Compiler.Yul.YulExpr.lit packed.offset,
              Compiler.Yul.YulExpr.ident "__compat_packed"]]])]) := by
  have hMappingBase : BridgedExpr
      (Compiler.Yul.YulExpr.call "mappingSlot" [
        Compiler.Yul.YulExpr.lit slot,
        Compiler.Yul.YulExpr.ident "__compat_key"]) := by
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with hArg | hArg
      · subst hArg; exact BridgedExpr.lit slot
      · subst hArg; exact BridgedExpr.ident "__compat_key"
  refine BridgedStmt.block _ ?_
  intro stmt hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl
  · -- let_ __compat_slot_word (sload(mappingSlot(lit slot, ident "__compat_key")))
    refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      subst hArg; exact hMappingBase
  · -- let_ __compat_slot_cleared (and(ident, not(lit shiftedMaskNat)))
    refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with hArg | hArg
      · subst hArg; exact BridgedExpr.ident "__compat_slot_word"
      · subst hArg
        apply BridgedExpr.call
        · exact Or.inl (by decide)
        · intro arg' hArg'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg'
          subst hArg'; exact BridgedExpr.lit _
  · -- expr (sstore(mappingSlot(lit slot, ident "__compat_key"),
    --         or(ident, shl(lit offset, ident))))
    have hVal : BridgedExpr
        (Compiler.Yul.YulExpr.call "or" [
          Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
          Compiler.Yul.YulExpr.call "shl" [
            Compiler.Yul.YulExpr.lit packed.offset,
            Compiler.Yul.YulExpr.ident "__compat_packed"]]) := by
      apply BridgedExpr.call
      · exact Or.inl (by decide)
      · intro arg hArg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
        rcases hArg with hArg | hArg
        · subst hArg; exact BridgedExpr.ident "__compat_slot_cleared"
        · subst hArg
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg' hArg'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg'
            rcases hArg' with hArg' | hArg'
            · subst hArg'; exact BridgedExpr.lit _
            · subst hArg'; exact BridgedExpr.ident "__compat_packed"
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_sstore_mapping
        (Compiler.Yul.YulExpr.lit slot)
        (Compiler.Yul.YulExpr.ident "__compat_key") _
        (BridgedExpr.lit slot)
        (BridgedExpr.ident "__compat_key") hVal)

/-- Helper: every element of `slots.map innerBlockFn` satisfies
`BridgedStmt` via the single-slot inner-block helper. -/
private theorem bridgedStmts_slotsMap_packedInnerBlock_wordOffsetZero
    (slots : List Nat) (packed : PackedBits) :
    ∀ stmt ∈ slots.map (fun slot =>
      Compiler.Yul.YulStmt.block [
        Compiler.Yul.YulStmt.let_ "__compat_slot_word"
          (Compiler.Yul.YulExpr.call "sload" [
            Compiler.Yul.YulExpr.call "mappingSlot" [
              Compiler.Yul.YulExpr.lit slot,
              Compiler.Yul.YulExpr.ident "__compat_key"]]),
        Compiler.Yul.YulStmt.let_ "__compat_slot_cleared"
          (Compiler.Yul.YulExpr.call "and" [
            Compiler.Yul.YulExpr.ident "__compat_slot_word",
            Compiler.Yul.YulExpr.call "not" [
              Compiler.Yul.YulExpr.lit (packedShiftedMaskNat packed)]]),
        Compiler.Yul.YulStmt.expr (
          Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "mappingSlot" [
              Compiler.Yul.YulExpr.lit slot,
              Compiler.Yul.YulExpr.ident "__compat_key"],
            Compiler.Yul.YulExpr.call "or" [
              Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
              Compiler.Yul.YulExpr.call "shl" [
                Compiler.Yul.YulExpr.lit packed.offset,
                Compiler.Yul.YulExpr.ident "__compat_packed"]]])]),
      BridgedStmt stmt := by
  intro stmt hMem
  rw [List.mem_map] at hMem
  obtain ⟨slot, _, hEq⟩ := hMem
  subst hEq
  exact bridgedStmt_packedInnerBlock_wordOffsetZero slot packed

/-- A multi-slot `Stmt.setMappingPackedWord field key 0 packed value`
source write with pure bridged key and value, on a declared `isMapping`
field whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMappingPackedWordMultiSlotStmt (fields : List Field) :
    Stmt → Prop
  | setMappingPackedWord (field : String)
      {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} (wordOffset : Nat) (packed : PackedBits)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hWordOffset : wordOffset = 0)
      (hPacked : packedBitsValid packed = true) :
      BridgedSourceMappingPackedWordMultiSlotStmt fields
        (.setMappingPackedWord field key wordOffset packed value)

def BridgedSourceMappingPackedWordMultiSlotStmts (fields : List Field)
    (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts, BridgedSourceMappingPackedWordMultiSlotStmt fields stmt

/-- A multi-slot `Stmt.setMappingPackedWord` source write at
`wordOffset = 0` with pure bridged key and value compiles to
`BridgedStmts`. -/
theorem compileStmt_setMappingPackedWord_multiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} (wordOffset : Nat) (packed : PackedBits)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hWordOffset : wordOffset = 0)
    (hPacked : packedBitsValid packed = true) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames
        [] (.setMappingPackedWord field key wordOffset packed value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  subst hWordOffset
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, compileMappingPackedSlotWrite,
            hMapping, hPacked, hSlots, Pure.pure, Except.pure] at hOk
          subst hOk
          have hKeyBridged : BridgedExpr keyExpr :=
            compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr
          have hValueBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
          refine BridgedStmts_singleton_block ?_
          intro stmt hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · -- let_ __compat_key keyExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ hKeyBridged)
          rcases hMem with rfl | hMem
          · -- let_ __compat_value valueExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ hValueBridged)
          rcases hMem with rfl | hMem
          · -- let_ __compat_packed (and(ident "__compat_value", lit maskNat))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_value"
              · subst hArg; exact BridgedExpr.lit _
          -- Remaining: slots.map (inner block fn) for slot0 :: slot1 :: slotsRest.
          -- After simp unfolds the head of List.map, hMem ranges over
          -- inner_block(slot0) :: inner_block(slot1) :: slotsRest.map inner_block_fn
          rcases hMem with rfl | hMem
          · exact bridgedStmt_packedInnerBlock_wordOffsetZero slot0 packed
          rcases hMem with rfl | hMem
          · exact bridgedStmt_packedInnerBlock_wordOffsetZero slot1 packed
          · exact bridgedStmts_slotsMap_packedInnerBlock_wordOffsetZero
              slotsRest packed stmt hMem

/-- Each statement in the multi-slot mappingPackedWord-write fragment
(wordOffset=0) compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingPackedWordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceMappingPackedWordMultiSlotStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingPackedWord field wordOffset packed hKey hValue hMapping hSlots
      hWordOffset hPacked =>
      exact compileStmt_setMappingPackedWord_multiSlot_bridged fields events
        errors dynamicSource internalRetNames isInternal inScopeNames field
        wordOffset packed hKey hValue hMapping hSlots hWordOffset hPacked hOk

/-- Lists of multi-slot mappingPackedWord-write source statements
(wordOffset=0) compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingPackedWordMultiSlot_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingPackedWordMultiSlotStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
      cases hHead : compileStmt fields events errors dynamicSource
          internalRetNames isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingPackedWordMultiSlotStmt fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingPackedWordMultiSlotStmts fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingPackedWordMultiSlot_bridged fields events
                  errors dynamicSource internalRetNames isInternal inScopeNames
                  hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-! ## Source statement body closure: multi-slot `setMappingPackedWord`
(wordOffset ≠ 0)

For a declared `isMapping` field with ≥ 2 write slots and `wordOffset ≠ 0`,
`compileMappingPackedSlotWrite` emits the same outer block shape as the
wordOffset=0 multi-slot case (3-stmt prefix + `slots.map inner_block_fn`),
but each per-slot write address becomes
`add(mappingSlot(lit slot, ident "__compat_key"), lit wordOffset)`. The
inner block's `sload` arg and its terminating `sstore` slot both use that
added expression. The `sload` branch closes via `BridgedExpr.call "add"`
(since `add ∈ bridgedBuiltins`); the terminator closes via
`BridgedStraightStmt.expr_sstore_add` rather than `expr_sstore_mapping`. -/

/-- Helper: for any `slot`, non-zero `wordOffset`, and valid `packed`, the
three-stmt inner block `YulStmt.block [sload-let, cleared-let, sstore-expr]`
produced by the multi-slot wordOffset≠0 packed-write shape satisfies
`BridgedStmt`. -/
private theorem bridgedStmt_packedInnerBlock_wordOffsetNonzero
    (slot wordOffset : Nat) (packed : PackedBits) :
    BridgedStmt (Compiler.Yul.YulStmt.block [
      Compiler.Yul.YulStmt.let_ "__compat_slot_word"
        (Compiler.Yul.YulExpr.call "sload" [
          Compiler.Yul.YulExpr.call "add" [
            Compiler.Yul.YulExpr.call "mappingSlot" [
              Compiler.Yul.YulExpr.lit slot,
              Compiler.Yul.YulExpr.ident "__compat_key"],
            Compiler.Yul.YulExpr.lit wordOffset]]),
      Compiler.Yul.YulStmt.let_ "__compat_slot_cleared"
        (Compiler.Yul.YulExpr.call "and" [
          Compiler.Yul.YulExpr.ident "__compat_slot_word",
          Compiler.Yul.YulExpr.call "not" [
            Compiler.Yul.YulExpr.lit (packedShiftedMaskNat packed)]]),
      Compiler.Yul.YulStmt.expr (
        Compiler.Yul.YulExpr.call "sstore" [
          Compiler.Yul.YulExpr.call "add" [
            Compiler.Yul.YulExpr.call "mappingSlot" [
              Compiler.Yul.YulExpr.lit slot,
              Compiler.Yul.YulExpr.ident "__compat_key"],
            Compiler.Yul.YulExpr.lit wordOffset],
          Compiler.Yul.YulExpr.call "or" [
            Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
            Compiler.Yul.YulExpr.call "shl" [
              Compiler.Yul.YulExpr.lit packed.offset,
              Compiler.Yul.YulExpr.ident "__compat_packed"]]])]) := by
  have hMappingBase : BridgedExpr
      (Compiler.Yul.YulExpr.call "mappingSlot" [
        Compiler.Yul.YulExpr.lit slot,
        Compiler.Yul.YulExpr.ident "__compat_key"]) := by
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with hArg | hArg
      · subst hArg; exact BridgedExpr.lit slot
      · subst hArg; exact BridgedExpr.ident "__compat_key"
  have hWriteSlot : BridgedExpr
      (Compiler.Yul.YulExpr.call "add" [
        Compiler.Yul.YulExpr.call "mappingSlot" [
          Compiler.Yul.YulExpr.lit slot,
          Compiler.Yul.YulExpr.ident "__compat_key"],
        Compiler.Yul.YulExpr.lit wordOffset]) := by
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with hArg | hArg
      · subst hArg; exact hMappingBase
      · subst hArg; exact BridgedExpr.lit wordOffset
  refine BridgedStmt.block _ ?_
  intro stmt hMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl
  · -- let_ __compat_slot_word (sload(add(mappingSlot, lit wordOffset)))
    refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      subst hArg; exact hWriteSlot
  · -- let_ __compat_slot_cleared (and(ident, not(lit shiftedMaskNat)))
    refine BridgedStmt.straight _ (BridgedStraightStmt.let_ _ _ ?_)
    apply BridgedExpr.call
    · exact Or.inl (by decide)
    · intro arg hArg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
      rcases hArg with hArg | hArg
      · subst hArg; exact BridgedExpr.ident "__compat_slot_word"
      · subst hArg
        apply BridgedExpr.call
        · exact Or.inl (by decide)
        · intro arg' hArg'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg'
          subst hArg'; exact BridgedExpr.lit _
  · -- expr (sstore(add(mappingSlot, lit wordOffset),
    --         or(ident, shl(lit offset, ident))))
    have hVal : BridgedExpr
        (Compiler.Yul.YulExpr.call "or" [
          Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
          Compiler.Yul.YulExpr.call "shl" [
            Compiler.Yul.YulExpr.lit packed.offset,
            Compiler.Yul.YulExpr.ident "__compat_packed"]]) := by
      apply BridgedExpr.call
      · exact Or.inl (by decide)
      · intro arg hArg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
        rcases hArg with hArg | hArg
        · subst hArg; exact BridgedExpr.ident "__compat_slot_cleared"
        · subst hArg
          apply BridgedExpr.call
          · exact Or.inl (by decide)
          · intro arg' hArg'
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg'
            rcases hArg' with hArg' | hArg'
            · subst hArg'; exact BridgedExpr.lit _
            · subst hArg'; exact BridgedExpr.ident "__compat_packed"
    exact BridgedStmt.straight _
      (BridgedStraightStmt.expr_sstore_add
        (Compiler.Yul.YulExpr.call "mappingSlot"
          [Compiler.Yul.YulExpr.lit slot,
           Compiler.Yul.YulExpr.ident "__compat_key"])
        (Compiler.Yul.YulExpr.lit wordOffset) _
        hMappingBase (BridgedExpr.lit wordOffset) hVal)

/-- Helper: every element of `slots.map innerBlockFn` (wordOffset ≠ 0)
satisfies `BridgedStmt` via the single-slot inner-block helper. -/
private theorem bridgedStmts_slotsMap_packedInnerBlock_wordOffsetNonzero
    (slots : List Nat) (wordOffset : Nat) (packed : PackedBits) :
    ∀ stmt ∈ slots.map (fun slot =>
      Compiler.Yul.YulStmt.block [
        Compiler.Yul.YulStmt.let_ "__compat_slot_word"
          (Compiler.Yul.YulExpr.call "sload" [
            Compiler.Yul.YulExpr.call "add" [
              Compiler.Yul.YulExpr.call "mappingSlot" [
                Compiler.Yul.YulExpr.lit slot,
                Compiler.Yul.YulExpr.ident "__compat_key"],
              Compiler.Yul.YulExpr.lit wordOffset]]),
        Compiler.Yul.YulStmt.let_ "__compat_slot_cleared"
          (Compiler.Yul.YulExpr.call "and" [
            Compiler.Yul.YulExpr.ident "__compat_slot_word",
            Compiler.Yul.YulExpr.call "not" [
              Compiler.Yul.YulExpr.lit (packedShiftedMaskNat packed)]]),
        Compiler.Yul.YulStmt.expr (
          Compiler.Yul.YulExpr.call "sstore" [
            Compiler.Yul.YulExpr.call "add" [
              Compiler.Yul.YulExpr.call "mappingSlot" [
                Compiler.Yul.YulExpr.lit slot,
                Compiler.Yul.YulExpr.ident "__compat_key"],
              Compiler.Yul.YulExpr.lit wordOffset],
            Compiler.Yul.YulExpr.call "or" [
              Compiler.Yul.YulExpr.ident "__compat_slot_cleared",
              Compiler.Yul.YulExpr.call "shl" [
                Compiler.Yul.YulExpr.lit packed.offset,
                Compiler.Yul.YulExpr.ident "__compat_packed"]]])]),
      BridgedStmt stmt := by
  intro stmt hMem
  rw [List.mem_map] at hMem
  obtain ⟨slot, _, hEq⟩ := hMem
  subst hEq
  exact bridgedStmt_packedInnerBlock_wordOffsetNonzero slot wordOffset packed

/-- A multi-slot `Stmt.setMappingPackedWord field key wordOffset packed
value` source write with pure bridged key and value at `wordOffset ≠ 0`,
on a declared `isMapping` field whose write slots list has ≥ 2 entries. -/
inductive BridgedSourceMappingPackedWordMultiSlotNonzeroStmt
    (fields : List Field) : Stmt → Prop
  | setMappingPackedWord (field : String)
      {slot0 slot1 : Nat} {slotsRest : List Nat}
      {key value : Expr} {wordOffset : Nat} (packed : PackedBits)
      (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
      (hMapping : isMapping fields field = true)
      (hSlots : findFieldWriteSlots fields field =
        some (slot0 :: slot1 :: slotsRest))
      (hNonzero : wordOffset ≠ 0)
      (hPacked : packedBitsValid packed = true) :
      BridgedSourceMappingPackedWordMultiSlotNonzeroStmt fields
        (.setMappingPackedWord field key wordOffset packed value)

def BridgedSourceMappingPackedWordMultiSlotNonzeroStmts
    (fields : List Field) (stmts : List Stmt) : Prop :=
  ∀ stmt ∈ stmts,
    BridgedSourceMappingPackedWordMultiSlotNonzeroStmt fields stmt

/-- A multi-slot `Stmt.setMappingPackedWord` source write at `wordOffset ≠ 0`
with pure bridged key and value compiles to `BridgedStmts`. -/
theorem compileStmt_setMappingPackedWord_multiSlot_nonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (field : String) {slot0 slot1 : Nat} {slotsRest : List Nat}
    {key value : Expr} {wordOffset : Nat} (packed : PackedBits)
    (hKey : BridgedSourceExpr key) (hValue : BridgedSourceExpr value)
    (hMapping : isMapping fields field = true)
    (hSlots : findFieldWriteSlots fields field =
      some (slot0 :: slot1 :: slotsRest))
    (hNonzero : wordOffset ≠ 0)
    (hPacked : packedBitsValid packed = true) :
    ∀ {out : List YulStmt},
      compileStmt fields events errors dynamicSource internalRetNames isInternal
        inScopeNames
        [] (.setMappingPackedWord field key wordOffset packed value) = .ok out →
      BridgedStmts out := by
  intro out hOk
  have hBeq : (wordOffset == 0) = false := by
    cases wordOffset with
    | zero => exact absurd rfl hNonzero
    | succ n => rfl
  simp only [compileStmt, bind, Except.bind] at hOk
  cases hKeyExpr : compileExpr fields dynamicSource key with
  | error err => simp [hKeyExpr] at hOk
  | ok keyExpr =>
      cases hValueExpr : compileExpr fields dynamicSource value with
      | error err => simp [hKeyExpr, hValueExpr] at hOk
      | ok valueExpr =>
          simp [hKeyExpr, hValueExpr, compileMappingPackedSlotWrite,
            hMapping, hPacked, hSlots, hBeq, Pure.pure, Except.pure] at hOk
          subst hOk
          have hKeyBridged : BridgedExpr keyExpr :=
            compileExpr_bridgedSource fields dynamicSource hKey hKeyExpr
          have hValueBridged : BridgedExpr valueExpr :=
            compileExpr_bridgedSource fields dynamicSource hValue hValueExpr
          refine BridgedStmts_singleton_block ?_
          intro stmt hMem
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · -- let_ __compat_key keyExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ hKeyBridged)
          rcases hMem with rfl | hMem
          · -- let_ __compat_value valueExpr
            exact BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ hValueBridged)
          rcases hMem with rfl | hMem
          · -- let_ __compat_packed (and(ident "__compat_value", lit maskNat))
            refine BridgedStmt.straight _
              (BridgedStraightStmt.let_ _ _ ?_)
            apply BridgedExpr.call
            · exact Or.inl (by decide)
            · intro arg hArg
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hArg
              rcases hArg with hArg | hArg
              · subst hArg; exact BridgedExpr.ident "__compat_value"
              · subst hArg; exact BridgedExpr.lit _
          -- Remaining: slots.map (inner_block_fn) for slot0 :: slot1 :: slotsRest.
          rcases hMem with rfl | hMem
          · exact bridgedStmt_packedInnerBlock_wordOffsetNonzero slot0
              wordOffset packed
          rcases hMem with rfl | hMem
          · exact bridgedStmt_packedInnerBlock_wordOffsetNonzero slot1
              wordOffset packed
          · exact bridgedStmts_slotsMap_packedInnerBlock_wordOffsetNonzero
              slotsRest wordOffset packed stmt hMem

/-- Each statement in the multi-slot wordOffset≠0 mappingPackedWord-write
fragment compiles to Yul satisfying `BridgedStmts`. -/
theorem compileStmt_mappingPackedWordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String) :
    ∀ {stmt : Stmt},
      BridgedSourceMappingPackedWordMultiSlotNonzeroStmt fields stmt →
      ∀ {out : List YulStmt},
        compileStmt fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmt = .ok out →
        BridgedStmts out := by
  intro stmt hStmt out hOk
  cases hStmt with
  | setMappingPackedWord field packed hKey hValue hMapping hSlots hNonzero
      hPacked =>
      exact compileStmt_setMappingPackedWord_multiSlot_nonzero_bridged fields
        events errors dynamicSource internalRetNames isInternal inScopeNames
        field packed hKey hValue hMapping hSlots hNonzero hPacked hOk

/-- Lists of multi-slot wordOffset≠0 mappingPackedWord-write source
statements compile to Yul lists satisfying `BridgedStmts`. -/
theorem compileStmtList_mappingPackedWordMultiSlotNonzero_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSourceMappingPackedWordMultiSlotNonzeroStmts fields stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
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
      cases hHead : compileStmt fields events errors dynamicSource
          internalRetNames isInternal inScopeNames [] head with
      | error err => simp [hHead] at hOk
      | ok headOut =>
          simp [hHead] at hOk
          cases hTail : compileStmtList fields events errors dynamicSource
              internalRetNames isInternal (collectStmtNames head ++ inScopeNames) [] tail with
          | error err => simp [hTail] at hOk
          | ok tailOut =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource :
                  BridgedSourceMappingPackedWordMultiSlotNonzeroStmt
                    fields head :=
                hSource head (by simp)
              have hTailSource :
                  BridgedSourceMappingPackedWordMultiSlotNonzeroStmts
                    fields tail := by
                intro stmt hMem
                exact hSource stmt (by simp [hMem])
              exact BridgedStmts_append
                (compileStmt_mappingPackedWordMultiSlotNonzero_bridged fields
                  events errors dynamicSource internalRetNames isInternal
                  inScopeNames hHeadSource hHead)
                (ih (collectStmtNames head ++ inScopeNames) hTailSource hTail)

/-!
## Universal safe-body closure

`BridgedSafeStmts` is the source-level whitelist used by the EVMYulLean
retargeting report: it collects the statement-list fragments that this module
has proved to compile into `BridgedStmts`. The external-call family
(`internalCall`, `internalCallAssign`, `externalCallBind`, and `ecm`) is
intentionally absent; those statements still need function-table simulation
before they can be discharged without explicit hypotheses.
-/

inductive BridgedSafeStmts
    (fields : List Field) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String) :
    Bool → List Stmt → Prop
  | externalRecursiveRawLog {stmts : List Stmt}
      (hStmts : BridgedSourceExternalRecursiveBodyWithRawLogStmts
        fields errors dynamicSource stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts
  | internalRecursiveRawLog {stmts : List Stmt}
      (hStmts : BridgedSourceInternalRecursiveBodyWithRawLogStmts
        fields errors dynamicSource stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames true stmts
  | setStorageArrayElement {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceSetStorageArrayElementStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingChain {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingChainStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWriteMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWriteMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWrite2MultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWrite2MultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMemberMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2MultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2MultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2WordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingWordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingWordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mapping2WordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMapping2WordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMemberMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMemberMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | structMember2MultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStructMember2MultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWord {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordMultiSlot {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordMultiSlotStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | mappingPackedWordMultiSlotNonzero {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMappingPackedWordMultiSlotNonzeroStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | returnValuesExternal {stmts : List Stmt}
      (hStmts : BridgedSourceReturnValuesExternalStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames false stmts
  | returnValuesInternal {stmts : List Stmt}
      (hStmts : BridgedSourceReturnValuesInternalStmts internalRetNames stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames true stmts
  | mstore {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceMstoreStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | tstore {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceTstoreStmts stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | storageArrayPush {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageArrayPushStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts
  | storageArrayPop {isInternal : Bool} {stmts : List Stmt}
      (hStmts : BridgedSourceStorageArrayPopStmts fields stmts) :
      BridgedSafeStmts fields errors dynamicSource internalRetNames isInternal stmts

/-- Every source statement list accepted by `BridgedSafeStmts` compiles to a
Yul statement list accepted by `BridgedStmts`. This is the B7 aggregation
theorem: callers use one whitelist witness instead of choosing a fragment-
specific closure lemma manually. -/
theorem compileStmtList_always_bridged
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) :
    ∀ (stmts : List Stmt) (inScopeNames : List String),
      BridgedSafeStmts fields errors dynamicSource internalRetNames
        isInternal stmts →
      ∀ {out : List YulStmt},
        compileStmtList fields events errors dynamicSource internalRetNames
          isInternal inScopeNames [] stmts = .ok out →
        BridgedStmts out := by
  intro stmts inScopeNames hSafe out hOk
  cases hSafe with
  | externalRecursiveRawLog hStmts =>
      exact compileStmtList_external_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | internalRecursiveRawLog hStmts =>
      exact compileStmtList_internal_recursive_body_with_raw_log_bridged fields
        events errors dynamicSource internalRetNames hStmts inScopeNames hOk
  | setStorageArrayElement hStmts =>
      exact compileStmtList_setStorageArrayElement_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingChain hStmts =>
      exact compileStmtList_mappingChain_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingWriteMultiSlot hStmts =>
      exact compileStmtList_mappingWriteMultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingWrite2MultiSlot hStmts =>
      exact compileStmtList_mappingWrite2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | structMemberMultiSlot hStmts =>
      exact compileStmtList_structMemberMultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | structMember2MultiSlot hStmts =>
      exact compileStmtList_structMember2MultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingWordMultiSlot hStmts =>
      exact compileStmtList_mappingWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mapping2WordMultiSlot hStmts =>
      exact compileStmtList_mapping2WordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingWordMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal stmts inScopeNames
        hStmts hOk
  | mapping2WordMultiSlotNonzero hStmts =>
      exact compileStmtList_mapping2WordMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal stmts inScopeNames
        hStmts hOk
  | structMemberMultiSlotNonzero hStmts =>
      exact compileStmtList_structMemberMultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal stmts inScopeNames
        hStmts hOk
  | structMember2MultiSlotNonzero hStmts =>
      exact compileStmtList_structMember2MultiSlotNonzero_bridged fields events
        errors dynamicSource internalRetNames isInternal stmts inScopeNames
        hStmts hOk
  | mappingPackedWord hStmts =>
      exact compileStmtList_mappingPackedWord_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingPackedWordNonzero hStmts =>
      exact compileStmtList_mappingPackedWordNonzero_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingPackedWordMultiSlot hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlot_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | mappingPackedWordMultiSlotNonzero hStmts =>
      exact compileStmtList_mappingPackedWordMultiSlotNonzero_bridged fields
        events errors dynamicSource internalRetNames isInternal stmts inScopeNames
        hStmts hOk
  | returnValuesExternal hStmts =>
      exact compileStmtList_returnValuesExternal_bridged fields events errors
        dynamicSource internalRetNames stmts inScopeNames hStmts hOk
  | returnValuesInternal hStmts =>
      exact compileStmtList_returnValuesInternal_bridged fields events errors
        dynamicSource internalRetNames stmts inScopeNames hStmts hOk
  | mstore hStmts =>
      exact compileStmtList_mstore_bridged fields events errors dynamicSource
        internalRetNames isInternal stmts inScopeNames hStmts hOk
  | tstore hStmts =>
      exact compileStmtList_tstore_bridged fields events errors dynamicSource
        internalRetNames isInternal stmts inScopeNames hStmts hOk
  | storageArrayPush hStmts =>
      exact compileStmtList_storageArrayPush_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk
  | storageArrayPop hStmts =>
      exact compileStmtList_storageArrayPop_bridged fields events errors
        dynamicSource internalRetNames isInternal stmts inScopeNames hStmts hOk

end Compiler.Proofs.YulGeneration.Backends
