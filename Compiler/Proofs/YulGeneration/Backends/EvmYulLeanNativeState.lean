import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeLowering
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge
import Compiler.Proofs.YulGeneration.RuntimeTypes
import Compiler.Codegen
import EvmYul.Yul.Interpreter
import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

/-!
Native EVMYulLean state and generated-runtime support predicates.

This module owns the executable state setup around the native proof boundary:
initial state construction, literal storage-slot materialization, generated
runtime shape checks, native environment validation, and basic initial-state
projection facts. Keeping these definitions out of `EvmYulLeanNativeHarness`
keeps the dispatcher and result-projection proofs focused on execution.
-/

/-- Build a native EVMYulLean state for a generated runtime contract.

The bridge starts from the flat Verity `YulState` projection, then installs the
lowered `YulContract` both in the execution environment and in the current
account. Runtime entrypoints are mutable by default (`perm := true`);
static-call-specific harnesses can override this later when #1737 widens to
external-call semantics.
-/
def initialState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.State :=
  let verityState := YulState.initial tx storage
  let shared := toSharedState verityState observableSlots
  let addr := natToAddress tx.thisAddress
  let account : EvmYul.Account .Yul :=
    match shared.accountMap.find? addr with
    | some acc => { acc with code := contract }
    | none =>
        { nonce := ⟨0⟩
          balance := ⟨0⟩
          storage := projectStorage storage observableSlots
          code := contract
          tstorage := Batteries.RBMap.empty }
  let shared' : EvmYul.SharedState .Yul :=
    { shared with
      accountMap := shared.accountMap.insert addr account
      executionEnv :=
        { shared.executionEnv with
          code := contract
          perm := true } }
  .Ok shared' ∅

/-! ## Native Storage Materialization -/

partial def yulExprLiteralStorageReadSlots : YulExpr → List Nat
  | .call "sload" [.lit slot] => [slot]
  | .call _ args => args.flatMap yulExprLiteralStorageReadSlots
  | _ => []

mutual
  partial def yulStmtLiteralStorageReadSlots : YulStmt → List Nat
    | .let_ _ value => yulExprLiteralStorageReadSlots value
    | .letMany _ value => yulExprLiteralStorageReadSlots value
    | .assign _ value => yulExprLiteralStorageReadSlots value
    | .expr e => yulExprLiteralStorageReadSlots e
    | .if_ cond body =>
        yulExprLiteralStorageReadSlots cond ++ yulStmtsLiteralStorageReadSlots body
    | .for_ init cond post body =>
        yulStmtsLiteralStorageReadSlots init ++
          yulExprLiteralStorageReadSlots cond ++
          yulStmtsLiteralStorageReadSlots post ++
          yulStmtsLiteralStorageReadSlots body
    | .switch discr cases defaultBody =>
        yulExprLiteralStorageReadSlots discr ++
          cases.flatMap (fun entry => yulStmtsLiteralStorageReadSlots entry.2) ++
          (defaultBody.map yulStmtsLiteralStorageReadSlots).getD []
    | .block stmts => yulStmtsLiteralStorageReadSlots stmts
    | .funcDef _ _ _ body => yulStmtsLiteralStorageReadSlots body
    | .comment _ | .leave => []

  partial def yulStmtsLiteralStorageReadSlots (stmts : List YulStmt) : List Nat :=
    stmts.flatMap yulStmtLiteralStorageReadSlots
end

def materializedStorageSlots
    (runtimeCode : List YulStmt)
    (observableSlots : List Nat) :
    List Nat :=
  -- Slot zero is the common simple-storage getter slot and is harmless to
  -- materialize twice; keeping it explicit avoids depending on the opaque
  -- partial literal-read collector for baseline storage projection facts.
  0 :: yulStmtsLiteralStorageReadSlots runtimeCode ++ observableSlots

theorem observableSlot_mem_materializedStorageSlots
    (runtimeCode : List YulStmt)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots) :
    slot ∈ materializedStorageSlots runtimeCode observableSlots := by
  simp [materializedStorageSlots, hSlot]

/-! ## Native Environment Support Boundary -/

partial def yulExprUsesBuiltinExceptFunctions
    (builtin : String)
    (functionNames : List String) :
    YulExpr → Bool
  | .call func args =>
      ((func == builtin) && !functionNames.contains func) ||
        args.any (yulExprUsesBuiltinExceptFunctions builtin functionNames)
  | _ => false

partial def yulExprCalledFunctions : YulExpr → List String
  | .call func args => func :: args.flatMap yulExprCalledFunctions
  | _ => []

mutual
  partial def yulStmtUsesBuiltinExceptFunctions
      (builtin : String)
      (functionNames : List String) :
      YulStmt → Bool
    | .let_ _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .letMany _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .assign _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .expr e => yulExprUsesBuiltinExceptFunctions builtin functionNames e
    | .if_ cond body =>
        yulExprUsesBuiltinExceptFunctions builtin functionNames cond ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .for_ init cond post body =>
        yulStmtsUseBuiltinExceptFunctions builtin functionNames init ||
          yulExprUsesBuiltinExceptFunctions builtin functionNames cond ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames post ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .switch discr cases defaultBody =>
        yulExprUsesBuiltinExceptFunctions builtin functionNames discr ||
          cases.any (fun (_, body) =>
            yulStmtsUseBuiltinExceptFunctions builtin functionNames body) ||
          defaultBody.any (yulStmtsUseBuiltinExceptFunctions builtin functionNames)
    | .block stmts => yulStmtsUseBuiltinExceptFunctions builtin functionNames stmts
    | .funcDef _ _ _ body =>
        yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .comment _ | .leave => false

  partial def yulStmtsUseBuiltinExceptFunctions
      (builtin : String)
      (functionNames : List String)
      (stmts : List YulStmt) :
      Bool :=
    stmts.any (yulStmtUsesBuiltinExceptFunctions builtin functionNames)
end

mutual
  partial def yulStmtCalledFunctions : YulStmt → List String
    | .let_ _ value => yulExprCalledFunctions value
    | .letMany _ value => yulExprCalledFunctions value
    | .assign _ value => yulExprCalledFunctions value
    | .expr e => yulExprCalledFunctions e
    | .if_ cond body => yulExprCalledFunctions cond ++ yulStmtsCalledFunctions body
    | .for_ init cond post body =>
        yulStmtsCalledFunctions init ++
          yulExprCalledFunctions cond ++
          yulStmtsCalledFunctions post ++
          yulStmtsCalledFunctions body
    | .switch discr cases defaultBody =>
        yulExprCalledFunctions discr ++
          cases.flatMap (fun entry => yulStmtsCalledFunctions entry.2) ++
          (defaultBody.map yulStmtsCalledFunctions).getD []
    | .block stmts => yulStmtsCalledFunctions stmts
    | .funcDef _ _ _ body => yulStmtsCalledFunctions body
    | .comment _ | .leave => []

  partial def yulStmtsCalledFunctions (stmts : List YulStmt) : List String :=
    stmts.flatMap yulStmtCalledFunctions
end

def yulFunctionBodies (runtimeCode : List YulStmt) : List (String × List YulStmt) :=
  runtimeCode.filterMap fun
    | .funcDef name _ _ body => some (name, body)
    | _ => none

@[simp] theorem yulFunctionBodies_nil :
    yulFunctionBodies [] = [] := by
  rfl

@[simp] theorem yulFunctionBodies_funcDef_cons
    (name : String) (params rets : List String) (body rest : List YulStmt) :
    yulFunctionBodies (YulStmt.funcDef name params rets body :: rest) =
      (name, body) :: yulFunctionBodies rest := by
  rfl

@[simp] theorem yulFunctionBodies_nonFunc_cons
    (stmt : YulStmt) (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    yulFunctionBodies (stmt :: rest) = yulFunctionBodies rest := by
  cases stmt <;> simp [yulFunctionBodies]
  case funcDef name params rets body =>
    exact False.elim (hNoFunc name params rets body rfl)

/-! ## Generated Native Runtime Fragment -/

mutual
  def yulStmtContainsFuncDef : YulStmt → Bool
    | .funcDef _ _ _ _ => true
    | .if_ _ body => yulStmtsContainFuncDef body
    | .for_ init _ post body =>
        yulStmtsContainFuncDef init ||
          yulStmtsContainFuncDef post ||
          yulStmtsContainFuncDef body
    | .switch _ cases defaultBody =>
        yulSwitchCasesContainFuncDef cases ||
          match defaultBody with
          | some stmts => yulStmtsContainFuncDef stmts
          | none => false
    | .block stmts => yulStmtsContainFuncDef stmts
    | .comment _ | .let_ _ _ | .letMany _ _ | .assign _ _ | .expr _ | .leave => false

  def yulStmtsContainFuncDef : List YulStmt → Bool
    | [] => false
    | stmt :: rest => yulStmtContainsFuncDef stmt || yulStmtsContainFuncDef rest

  def yulSwitchCasesContainFuncDef : List (Nat × List YulStmt) → Bool
    | [] => false
    | (_, body) :: rest =>
        yulStmtsContainFuncDef body || yulSwitchCasesContainFuncDef rest
end

@[simp] theorem yulStmtsContainFuncDef_nil :
    yulStmtsContainFuncDef [] = false := by
  rfl

@[simp] theorem yulStmtsContainFuncDef_cons
    (stmt : YulStmt) (stmts : List YulStmt) :
    yulStmtsContainFuncDef (stmt :: stmts) =
      (yulStmtContainsFuncDef stmt || yulStmtsContainFuncDef stmts) := by
  rfl

@[simp] theorem yulStmtsContainFuncDef_append
    (xs ys : List YulStmt) :
    yulStmtsContainFuncDef (xs ++ ys) =
      (yulStmtsContainFuncDef xs || yulStmtsContainFuncDef ys) := by
  induction xs with
  | nil =>
      simp
  | cons stmt rest ih =>
      simp [ih, Bool.or_assoc]

theorem yulStmtsContainFuncDef_flatMap_false {α : Type}
    (xs : List α) (f : α → List YulStmt)
    (h : ∀ x, x ∈ xs → yulStmtsContainFuncDef (f x) = false) :
    yulStmtsContainFuncDef (xs.flatMap f) = false := by
  induction xs with
  | nil =>
      simp
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : ∀ y, y ∈ rest → yulStmtsContainFuncDef (f y) = false := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.flatMap, List.map_cons, List.flatten_cons,
        yulStmtsContainFuncDef_append, hx, Bool.false_or]
      exact ih hrest

mutual
/-- Native statement-group lowering succeeds for any statement with no nested
function definitions. The native lowerer only rejects inline `funcDef`s; this
lemma packages that structural totality fact for generated-runtime proofs. -/
theorem lowerStmtGroupNativeWithSwitchIds_ok_of_yulStmtContainsFuncDef_false
    (reservedNames : List String) (nextSwitchId : Nat) (stmt : YulStmt)
    (hNoFunc : yulStmtContainsFuncDef stmt = false) :
    ∃ (native : List EvmYul.Yul.Ast.Stmt) (next : Nat),
      Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt =
        .ok (native, next) := by
  cases stmt with
  | comment c => simp
  | let_ name value => simp
  | letMany names value => simp
  | assign name value => simp
  | expr e => simp
  | «leave» => simp
  | if_ cond body =>
      have hBody : yulStmtsContainFuncDef body = false := by
        simpa [yulStmtContainsFuncDef] using hNoFunc
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames nextSwitchId body hBody with
        ⟨bodyNative, next, hLowerBody⟩
      refine ⟨[.If (Backends.lowerExprNative cond) bodyNative], next, ?_⟩
      simp [Backends.lowerStmtGroupNativeWithSwitchIds, hLowerBody]
  | for_ init cond post body =>
      have hAll :
          (yulStmtsContainFuncDef init = false ∧
            yulStmtsContainFuncDef post = false) ∧
            yulStmtsContainFuncDef body = false := by
        simpa [yulStmtContainsFuncDef] using hNoFunc
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames nextSwitchId init hAll.1.1 with
        ⟨initNative, afterInit, hLowerInit⟩
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames afterInit post hAll.1.2 with
        ⟨postNative, afterPost, hLowerPost⟩
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames afterPost body hAll.2 with
        ⟨bodyNative, next, hLowerBody⟩
      refine
        ⟨initNative ++ [.For (Backends.lowerExprNative cond) postNative bodyNative],
          next, ?_⟩
      rw [Backends.lowerStmtGroupNativeWithSwitchIds]
      rw [hLowerInit]
      simp only [Bind.bind, Except.bind]
      rw [hLowerPost]
      simp
      rw [hLowerBody]
      simp [Pure.pure, Except.pure]
  | «switch» expr cases defaultCase =>
      cases defaultCase with
      | none =>
          have hCases : yulSwitchCasesContainFuncDef cases = false := by
            simpa [yulStmtContainsFuncDef] using hNoFunc
          rcases
            lowerSwitchCasesNativeWithSwitchIds_ok_of_yulSwitchCasesContainFuncDef_false
              reservedNames (Backends.freshNativeSwitchId reservedNames nextSwitchId + 1)
              cases hCases with
            ⟨casesNative, next, hLowerCases⟩
          refine
            ⟨[Backends.lowerNativeSwitchBlock expr
                (Backends.freshNativeSwitchId reservedNames nextSwitchId)
                casesNative []],
              next, ?_⟩
          simp [Backends.lowerStmtGroupNativeWithSwitchIds, hLowerCases]
      | some defaultBody =>
          have hAll :
              yulSwitchCasesContainFuncDef cases = false ∧
                yulStmtsContainFuncDef defaultBody = false := by
            simpa [yulStmtContainsFuncDef] using hNoFunc
          rcases
            lowerSwitchCasesNativeWithSwitchIds_ok_of_yulSwitchCasesContainFuncDef_false
              reservedNames (Backends.freshNativeSwitchId reservedNames nextSwitchId + 1)
              cases hAll.1 with
            ⟨casesNative, afterCases, hLowerCases⟩
          rcases
            lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
              reservedNames afterCases defaultBody hAll.2 with
            ⟨defaultNative, next, hLowerDefault⟩
          refine
            ⟨[Backends.lowerNativeSwitchBlock expr
                (Backends.freshNativeSwitchId reservedNames nextSwitchId)
                casesNative defaultNative],
              next, ?_⟩
          rw [Backends.lowerStmtGroupNativeWithSwitchIds]
          simp only [hLowerCases, Bind.bind, Except.bind]
          rw [hLowerDefault]
          simp [Pure.pure, Except.pure]
  | block stmts =>
      have hStmts : yulStmtsContainFuncDef stmts = false := by
        simpa [yulStmtContainsFuncDef] using hNoFunc
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames nextSwitchId stmts hStmts with
        ⟨stmtsNative, next, hLowerStmts⟩
      refine ⟨[.Block stmtsNative], next, ?_⟩
      simp [Backends.lowerStmtGroupNativeWithSwitchIds, hLowerStmts]
  | funcDef name params rets body =>
      simp [yulStmtContainsFuncDef] at hNoFunc

/-- Native statement-list lowering succeeds for statement lists with no nested
function definitions. -/
theorem lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
    (reservedNames : List String) (nextSwitchId : Nat) (stmts : List YulStmt)
    (hNoFunc : yulStmtsContainFuncDef stmts = false) :
    ∃ (native : List EvmYul.Yul.Ast.Stmt) (next : Nat),
      Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts =
        .ok (native, next) := by
  cases stmts with
  | nil =>
      exact ⟨[], nextSwitchId, Backends.lowerStmtsNativeWithSwitchIds_nil _ _⟩
  | cons stmt rest =>
      have hAll :
          yulStmtContainsFuncDef stmt = false ∧
            yulStmtsContainFuncDef rest = false := by
        simpa [yulStmtsContainFuncDef] using hNoFunc
      rcases
        lowerStmtGroupNativeWithSwitchIds_ok_of_yulStmtContainsFuncDef_false
          reservedNames nextSwitchId stmt hAll.1 with
        ⟨headNative, midSwitchId, hLowerHead⟩
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames midSwitchId rest hAll.2 with
        ⟨restNative, finalSwitchId, hLowerRest⟩
      refine ⟨headNative ++ restNative, finalSwitchId, ?_⟩
      rw [Backends.lowerStmtsNativeWithSwitchIds_cons]
      rw [hLowerHead]
      simp only [Bind.bind, Except.bind]
      rw [hLowerRest]
      simp [Pure.pure, Except.pure]

/-- Native switch-case lowering succeeds when every case body has no nested
function definitions. -/
theorem lowerSwitchCasesNativeWithSwitchIds_ok_of_yulSwitchCasesContainFuncDef_false
    (reservedNames : List String) (nextSwitchId : Nat)
    (cases : List (Nat × List YulStmt))
    (hNoFunc : yulSwitchCasesContainFuncDef cases = false) :
    ∃ (native : List (Nat × List EvmYul.Yul.Ast.Stmt)) (next : Nat),
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId cases =
        .ok (native, next) := by
  cases cases with
  | nil =>
      exact ⟨[], nextSwitchId,
        Backends.lowerSwitchCasesNativeWithSwitchIds_nil _ _⟩
  | cons entry rest =>
      rcases entry with ⟨tag, body⟩
      have hAll :
          yulStmtsContainFuncDef body = false ∧
            yulSwitchCasesContainFuncDef rest = false := by
        simpa [yulSwitchCasesContainFuncDef] using hNoFunc
      rcases
        lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
          reservedNames nextSwitchId body hAll.1 with
        ⟨bodyNative, midSwitchId, hLowerBody⟩
      rcases
        lowerSwitchCasesNativeWithSwitchIds_ok_of_yulSwitchCasesContainFuncDef_false
          reservedNames midSwitchId rest hAll.2 with
        ⟨restNative, finalSwitchId, hLowerRest⟩
      refine ⟨(tag, bodyNative) :: restNative, finalSwitchId, ?_⟩
      rw [Backends.lowerSwitchCasesNativeWithSwitchIds_cons]
      rw [hLowerBody]
      simp only [Bind.bind, Except.bind]
      rw [hLowerRest]
      simp [Pure.pure, Except.pure]
end

/-- Public wrapper for native statement-list lowering totality. -/
theorem lowerStmtsNative_ok_of_yulStmtsContainFuncDef_false
    (stmts : List YulStmt)
    (hNoFunc : yulStmtsContainFuncDef stmts = false) :
    ∃ native, Backends.lowerStmtsNative stmts = .ok native := by
  rcases
    lowerStmtsNativeWithSwitchIds_ok_of_yulStmtsContainFuncDef_false
      (Backends.yulStmtsIdentifierNames stmts) 0 stmts hNoFunc with
    ⟨native, next, hLower⟩
  refine ⟨native, ?_⟩
  simp [Backends.lowerStmtsNative, hLower, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

def yulRuntimeTopLevelFunctionNames (runtimeCode : List YulStmt) : List String :=
  runtimeCode.filterMap fun
    | .funcDef name _ _ _ => some name
    | _ => none

def yulRuntimeDispatcherStmts (runtimeCode : List YulStmt) : List YulStmt :=
  runtimeCode.filter fun
    | .funcDef _ _ _ _ => false
    | _ => true

@[simp] theorem yulRuntimeTopLevelFunctionNames_nil :
    yulRuntimeTopLevelFunctionNames [] = [] := by
  rfl

@[simp] theorem yulRuntimeTopLevelFunctionNames_funcDef_cons
    (name : String) (params rets : List String) (body rest : List YulStmt) :
    yulRuntimeTopLevelFunctionNames
        (YulStmt.funcDef name params rets body :: rest) =
      name :: yulRuntimeTopLevelFunctionNames rest := by
  rfl

@[simp] theorem yulRuntimeTopLevelFunctionNames_nonFunc_cons
    (stmt : YulStmt) (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    yulRuntimeTopLevelFunctionNames (stmt :: rest) =
      yulRuntimeTopLevelFunctionNames rest := by
  cases stmt <;> simp [yulRuntimeTopLevelFunctionNames]
  case funcDef name params rets body =>
    exact False.elim (hNoFunc name params rets body rfl)

@[simp] theorem yulRuntimeTopLevelFunctionNames_append
    (left right : List YulStmt) :
    yulRuntimeTopLevelFunctionNames (left ++ right) =
      yulRuntimeTopLevelFunctionNames left ++
        yulRuntimeTopLevelFunctionNames right := by
  induction left with
  | nil => rfl
  | cons stmt rest ih =>
      cases stmt <;> simp [yulRuntimeTopLevelFunctionNames]

theorem yulRuntimeTopLevelFunctionNames_eq_nil_of_all_nonFunc
    (stmts : List YulStmt)
    (hNoFunc : ∀ stmt, stmt ∈ stmts →
      ∀ name params rets body, stmt ≠ YulStmt.funcDef name params rets body) :
    yulRuntimeTopLevelFunctionNames stmts = [] := by
  induction stmts with
  | nil => rfl
  | cons stmt rest ih =>
      rw [yulRuntimeTopLevelFunctionNames_nonFunc_cons]
      · exact ih (by
          intro stmt hmem
          exact hNoFunc stmt (by simp [hmem]))
      · intro name params rets body h
        exact hNoFunc stmt (by simp) name params rets body h

@[simp] theorem yulRuntimeDispatcherStmts_nil :
    yulRuntimeDispatcherStmts [] = [] := by
  rfl

@[simp] theorem yulRuntimeDispatcherStmts_funcDef_cons
    (name : String) (params rets : List String) (body rest : List YulStmt) :
    yulRuntimeDispatcherStmts
        (YulStmt.funcDef name params rets body :: rest) =
      yulRuntimeDispatcherStmts rest := by
  rfl

@[simp] theorem yulRuntimeDispatcherStmts_nonFunc_cons
    (stmt : YulStmt) (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    yulRuntimeDispatcherStmts (stmt :: rest) =
      stmt :: yulRuntimeDispatcherStmts rest := by
  cases stmt <;> simp [yulRuntimeDispatcherStmts]
  case funcDef name params rets body =>
    exact False.elim (hNoFunc name params rets body rfl)

def stringListHasDuplicate : List String → Bool
  | [] => false
  | name :: rest => rest.contains name || stringListHasDuplicate rest

def generatedRuntimeFunctionNamesUnique (runtimeCode : List YulStmt) : Bool :=
  !stringListHasDuplicate (yulRuntimeTopLevelFunctionNames runtimeCode)

def generatedRuntimeDispatcherHasNoFuncDefs (runtimeCode : List YulStmt) : Bool :=
  !yulStmtsContainFuncDef (yulRuntimeDispatcherStmts runtimeCode)

def generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
    (runtimeCode : List YulStmt) :
    Bool :=
  (yulFunctionBodies runtimeCode).all fun entry => !yulStmtsContainFuncDef entry.2

@[simp] theorem generatedRuntimeDispatcherHasNoFuncDefs_funcDef_cons
    (name : String) (params rets : List String) (body rest : List YulStmt) :
    generatedRuntimeDispatcherHasNoFuncDefs
        (YulStmt.funcDef name params rets body :: rest) =
      generatedRuntimeDispatcherHasNoFuncDefs rest := by
  simp [generatedRuntimeDispatcherHasNoFuncDefs]

@[simp] theorem generatedRuntimeDispatcherHasNoFuncDefs_nonFunc_cons
    (stmt : YulStmt) (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    generatedRuntimeDispatcherHasNoFuncDefs (stmt :: rest) =
      (!yulStmtContainsFuncDef stmt &&
        generatedRuntimeDispatcherHasNoFuncDefs rest) := by
  simp [generatedRuntimeDispatcherHasNoFuncDefs,
    yulRuntimeDispatcherStmts_nonFunc_cons stmt rest hNoFunc]

@[simp] theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_funcDef_cons
    (name : String) (params rets : List String) (body rest : List YulStmt) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
        (YulStmt.funcDef name params rets body :: rest) =
      (!yulStmtsContainFuncDef body &&
        generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs rest) := by
  simp [generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs]

@[simp] theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_nonFunc_cons
    (stmt : YulStmt) (rest : List YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs (stmt :: rest) =
      generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs rest := by
  simp [generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs,
    yulFunctionBodies_nonFunc_cons stmt rest hNoFunc]

theorem dispatchBody_noFuncDefs
    (payable : Bool) (label : String) (body : List YulStmt)
    (hBody : yulStmtsContainFuncDef body = false) :
    yulStmtsContainFuncDef
      (Compiler.CodegenCommon.dispatchBody payable label body) = false := by
  cases payable <;>
    simp [Compiler.CodegenCommon.dispatchBody, Compiler.CodegenCommon.callvalueGuard,
      yulStmtContainsFuncDef, yulStmtsContainFuncDef, hBody]

theorem buildSwitchCases_noFuncDefs
    (funcs : List IRFunction)
    (hBodies : ∀ fn, fn ∈ funcs → yulStmtsContainFuncDef fn.body = false) :
    yulSwitchCasesContainFuncDef
      (funcs.map fun fn =>
        (fn.selector,
          Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
            (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body))) =
      false := by
  induction funcs with
  | nil => rfl
  | cons fn rest ih =>
      have hFnBody : yulStmtsContainFuncDef fn.body = false := hBodies fn (by simp)
      have hRest : ∀ fn, fn ∈ rest → yulStmtsContainFuncDef fn.body = false := by
        intro fn hmem
        exact hBodies fn (by simp [hmem])
      have hDispatch :
          yulStmtsContainFuncDef
            (Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
              (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)) =
            false := by
        apply dispatchBody_noFuncDefs
        simp [Compiler.CodegenCommon.calldatasizeGuard, yulStmtContainsFuncDef,
          yulStmtsContainFuncDef, hFnBody]
      simp [yulSwitchCasesContainFuncDef, hDispatch, ih hRest]

theorem buildSwitch_noFuncDefs_noFallback_noReceive
    (funcs : List IRFunction)
    (hBodies : ∀ fn, fn ∈ funcs → yulStmtsContainFuncDef fn.body = false) :
    yulStmtContainsFuncDef
      (Compiler.CodegenCommon.buildSwitch funcs none none) = false := by
  have hCases := buildSwitchCases_noFuncDefs funcs hBodies
  simpa [Compiler.CodegenCommon.buildSwitch, Compiler.CodegenCommon.defaultDispatchCase,
    Compiler.CodegenCommon.dispatchBody, Compiler.CodegenCommon.calldatasizeGuard,
    Compiler.CodegenCommon.callvalueGuard, yulStmtContainsFuncDef,
    yulStmtsContainFuncDef, yulSwitchCasesContainFuncDef] using hCases

/-- Dispatch body emitted for one external function case. This native-harness
copy avoids importing the executable `Codegen` module into the proof path. -/
def switchCaseBody (fn : IRFunction) : List YulStmt :=
  Compiler.CodegenCommon.dispatchBody fn.payable s!"{fn.name}()"
    ([Compiler.CodegenCommon.calldatasizeGuard fn.params.length] ++ fn.body)

/-- Switch cases generated from IR functions. -/
def switchCases (fns : List IRFunction) : List (Nat × List YulStmt) :=
  fns.map (fun fn => (fn.selector, switchCaseBody fn))

/-- Source case list emitted inside `buildSwitch` before the optional default
case is attached. Kept explicit so native lowering lemmas can speak about the
actual generated dispatcher source list, not only the proof-side `switchCases`
abbreviation. -/
def buildSwitchSourceCases (funcs : List IRFunction) :
    List (Nat × List YulStmt) :=
  funcs.map (fun fn =>
    (fn.selector, switchCaseBody fn))

/-- The case list emitted by `buildSwitch` is the native-harness switch case
abbreviation. -/
theorem buildSwitchSourceCases_eq_switchCases (funcs : List IRFunction) :
    buildSwitchSourceCases funcs = switchCases funcs := by
  rfl

theorem find_switch_case_of_find_function
    (fns : List IRFunction) (sel : Nat) (fn : IRFunction)
    (hFind : fns.find? (fun f => f.selector == sel) = some fn) :
    (switchCases fns).find? (fun (c, _) => c = sel) =
      some (fn.selector, switchCaseBody fn) := by
  induction fns with
  | nil =>
      simp at hFind
  | cons f rest ih =>
      by_cases hsel : f.selector = sel
      · have hselb : (f.selector == sel) = true := by
          simp [hsel]
        have hFind' : some f = some fn := by
          simpa [List.find?, hselb] using hFind
        cases hFind'
        simp [switchCases, hsel]
      · have hselb : (f.selector == sel) = false := by
          simp [hsel]
        have hFind' : rest.find? (fun f => f.selector == sel) = some fn := by
          simpa [List.find?, hselb] using hFind
        have ih' := ih hFind'
        simpa [switchCases, List.find?, hsel] using ih'

theorem find_switch_case_of_find_function_eq_selector
    (fns : List IRFunction) (sel : Nat) (fn : IRFunction)
    (hFind : fns.find? (fun f => f.selector == sel) = some fn) :
    (switchCases fns).find? (fun (c, _) => c = sel) =
      some (sel, switchCaseBody fn) := by
  have hCase := find_switch_case_of_find_function fns sel fn hFind
  have hSel : fn.selector = sel := by
    have h := List.find?_some hFind
    simp at h
    exact h
  simpa [hSel] using hCase

theorem find_switch_case_of_find_function_none
    (fns : List IRFunction) (sel : Nat)
    (hFind : fns.find? (fun f => f.selector == sel) = none) :
    (switchCases fns).find? (fun (c, _) => c = sel) = none := by
  induction fns with
  | nil =>
      simp at hFind
      simp [switchCases]
  | cons f rest ih =>
      by_cases hsel : f.selector = sel
      · have hselb : (f.selector == sel) = true := by
          simp [hsel]
        have hFind' : (some f : Option IRFunction) = none := by
          simp [List.find?, hselb] at hFind
        cases hFind'
      · have hselb : (f.selector == sel) = false := by
          simp [hsel]
        have hFind' : rest.find? (fun f => f.selector == sel) = none := by
          simpa [List.find?, hselb] using hFind
        have ih' := ih hFind'
        simpa [switchCases, List.find?, hsel] using ih'

/-- Generated-dispatcher selector hit specialized to `IRFunction` lookup.

This composes the source `buildSwitch` case lookup theorem with native switch
case lowering, yielding the lowered native body selected by the same function
selector that `interpretIR` found. -/
theorem lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function
    (reservedNames : List String) (nextSwitchId final selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
      (switchCases funcs) = .ok (cases', final))
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn) :
    ∃ body' bodyStart bodyEnd,
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) := by
  have hCase :
      (switchCases funcs).find? (fun entry => entry.1 == selector) =
        some (selector, switchCaseBody fn) := by
    simpa using
      (find_switch_case_of_find_function_eq_selector funcs selector fn hFind)
  exact Backends.lowerSwitchCasesNativeWithSwitchIds_find?_some
    reservedNames nextSwitchId final selector selector (switchCaseBody fn)
    (switchCases funcs) cases' hLower hCase

/-- Generated-dispatcher selector miss specialized to `IRFunction` lookup.

If `interpretIR` finds no function for the selector, native lowering preserves
that miss on the generated `buildSwitch` case list. -/
theorem lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function
    (reservedNames : List String) (nextSwitchId final selector : Nat)
    (funcs : List IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
      (switchCases funcs) = .ok (cases', final))
    (hFind : funcs.find? (fun f => f.selector == selector) = none) :
    cases'.find? (fun entry => entry.1 == selector) = none := by
  have hCase :
      (switchCases funcs).find? (fun entry => entry.1 == selector) = none := by
    simpa using
      (find_switch_case_of_find_function_none funcs selector hFind)
  exact Backends.lowerSwitchCasesNativeWithSwitchIds_find?_none
    reservedNames nextSwitchId final selector (switchCases funcs) cases'
    hLower hCase

/-- `buildSwitch`-source variant of
`lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function`. -/
theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function
    (reservedNames : List String) (nextSwitchId final selector : Nat)
    (funcs : List IRFunction) (fn : IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
      (buildSwitchSourceCases funcs) = .ok (cases', final))
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn) :
    ∃ body' bodyStart bodyEnd,
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) := by
  rw [buildSwitchSourceCases_eq_switchCases] at hLower
  exact lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function
    reservedNames nextSwitchId final selector funcs fn cases' hLower hFind

/-- `buildSwitch`-source variant of
`lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function`. -/
theorem lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
    (reservedNames : List String) (nextSwitchId final selector : Nat)
    (funcs : List IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
      (buildSwitchSourceCases funcs) = .ok (cases', final))
    (hFind : funcs.find? (fun f => f.selector == selector) = none) :
    cases'.find? (fun entry => entry.1 == selector) = none := by
  rw [buildSwitchSourceCases_eq_switchCases] at hLower
  exact lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function
    reservedNames nextSwitchId final selector funcs cases' hLower hFind

/-- A singleton non-`funcDef` runtime lowers exactly through statement lowering,
with an empty native function table.

This is the generic native-lowering boundary used when generated runtime code
has only the dispatcher shell. -/
theorem lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative
    (stmt : YulStmt)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    Backends.lowerRuntimeContractNative [stmt] =
      match Backends.lowerStmtsNative [stmt] with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions := (∅ : Backends.NativeFunctionMap) }
      | .error err => .error err := by
  unfold Backends.lowerRuntimeContractNative
  unfold Backends.lowerStmtsNative
  dsimp
  rw [Backends.lowerRuntimeContractNativeAux_stmt_cons]
  · rw [Backends.lowerStmtsNativeWithSwitchIds_cons]
    cases hLower :
        Backends.lowerStmtGroupNativeWithSwitchIds
          (Backends.yulStmtsIdentifierNames [stmt]) 0 stmt with
    | ok pair =>
        cases pair with
        | mk lowered next =>
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
              Backends.lowerRuntimeContractNativeAux]
    | error err =>
        simp [Bind.bind, Except.bind]
  · exact hNoFunc

/-- Singleton non-`funcDef` runtime lowering, preserving the caller's
reserved-name context and native function table. This is the form needed after
runtime helper definitions have already populated the native function map. -/
theorem lowerRuntimeContractNativeAux_single_stmt_eq_lowerStmtsNativeWithSwitchIds
    (reservedNames : List String)
    (stmt : YulStmt)
    (functions : Backends.NativeFunctionMap)
    (hNoFunc : ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    (Backends.lowerRuntimeContractNativeAux reservedNames [stmt] [] functions 0 >>=
      fun a =>
        pure ({ dispatcher := EvmYul.Yul.Ast.Stmt.Block a.1
                functions := a.2.1 } : EvmYul.Yul.Ast.YulContract)) =
      match Backends.lowerStmtsNativeWithSwitchIds reservedNames 0 [stmt] with
      | .ok (dispatcher, _) =>
          .ok ({ dispatcher := EvmYul.Yul.Ast.Stmt.Block dispatcher
                 functions := functions } : EvmYul.Yul.Ast.YulContract)
      | .error err => .error err := by
  rw [Backends.lowerRuntimeContractNativeAux_stmt_cons]
  · rw [Backends.lowerStmtsNativeWithSwitchIds_cons]
    cases hLower :
        Backends.lowerStmtGroupNativeWithSwitchIds reservedNames 0 stmt with
    | ok pair =>
        cases pair with
        | mk lowered next =>
            simp [Bind.bind, Except.bind, Pure.pure, Except.pure,
              Backends.lowerRuntimeContractNativeAux]
    | error err =>
        simp [Bind.bind, Except.bind]
  · exact hNoFunc

/-- A non-`funcDef` runtime statement list lowers exactly through statement
lowering, preserving the caller's native function table. -/
theorem lowerRuntimeContractNativeAux_nonFunc_eq_lowerStmtsNativeWithSwitchIds
    (reservedNames : List String)
    (stmts : List YulStmt)
    (dispatcherAcc : List EvmYul.Yul.Ast.Stmt)
    (functions : Backends.NativeFunctionMap)
    (nextSwitchId : Nat)
    (hNoFunc : ∀ stmt, stmt ∈ stmts → ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    Backends.lowerRuntimeContractNativeAux reservedNames stmts
        dispatcherAcc functions nextSwitchId =
      match Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId stmts with
      | .ok (dispatcher, nextSwitchId) =>
          .ok (dispatcherAcc.reverse ++ dispatcher, functions, nextSwitchId)
      | .error err => .error err := by
  induction stmts generalizing dispatcherAcc nextSwitchId with
  | nil =>
      simp [Backends.lowerRuntimeContractNativeAux, Pure.pure, Except.pure]
  | cons stmt rest ih =>
      rw [Backends.lowerRuntimeContractNativeAux_stmt_cons]
      · rw [Backends.lowerStmtsNativeWithSwitchIds_cons]
        cases hLower :
            Backends.lowerStmtGroupNativeWithSwitchIds reservedNames nextSwitchId stmt with
        | error err =>
            simp [Bind.bind, Except.bind]
        | ok pair =>
            cases pair with
            | mk lowered nextSwitchId' =>
                simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
                rw [ih]
                · cases hRest :
                    Backends.lowerStmtsNativeWithSwitchIds reservedNames
                      nextSwitchId' rest with
                  | error err =>
                      simp
                  | ok pair =>
                      cases pair with
                      | mk restLowered finalSwitchId =>
                          simp [List.reverse_append, List.append_assoc]
                · intro stmt hmem
                  exact hNoFunc stmt (by simp [hmem])
      · exact hNoFunc stmt (by simp)

/-- A non-`funcDef` runtime statement list lowers exactly through statement
lowering, with an empty native function table. -/
theorem lowerRuntimeContractNative_nonFunc_eq_lowerStmtsNative
    (stmts : List YulStmt)
    (hNoFunc : ∀ stmt, stmt ∈ stmts → ∀ name params rets body,
      stmt ≠ YulStmt.funcDef name params rets body) :
    Backends.lowerRuntimeContractNative stmts =
      match Backends.lowerStmtsNative stmts with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions := (∅ : Backends.NativeFunctionMap) }
      | .error err => .error err := by
  unfold Backends.lowerRuntimeContractNative
  unfold Backends.lowerStmtsNative
  dsimp
  rw [lowerRuntimeContractNativeAux_nonFunc_eq_lowerStmtsNativeWithSwitchIds
    (Backends.yulStmtsIdentifierNames stmts) stmts [] (∅ : Backends.NativeFunctionMap)
    0 hNoFunc]
  cases hLower :
      Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames stmts) 0 stmts with
  | error err =>
      simp [hLower, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | ok pair =>
      cases pair
      simp [hLower, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Helper-free, no-fallback/no-receive emitted runtimes are exactly the
generated dispatcher shell prefixed by free-memory-pointer initialization. -/
theorem emitYul_runtimeCode_eq_single_dispatcher_of_noMapping_noInternals_noFallback_noReceive
    (contract : IRContract)
    (hNoMapping : contract.usesMapping = false)
    (hInternals : contract.internalFunctions = [])
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    (Compiler.emitYul contract).runtimeCode =
      [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch contract.functions none none] := by
  simp [Compiler.emitYul, Compiler.CodegenCommon.emitYul,
    Compiler.CodegenCommon.runtimeCode, hNoMapping, hInternals, hNoFallback,
    hNoReceive]

/-- In the helper-free, no-fallback/no-receive generated case, native runtime
lowering reduces to lowering the single dispatcher shell. -/
theorem lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive
    (contract : IRContract)
    (hNoMapping : contract.usesMapping = false)
    (hInternals : contract.internalFunctions = [])
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    Backends.lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      match Backends.lowerStmtsNative
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch contract.functions none none] with
      | .ok dispatcher =>
          .ok { dispatcher := .Block dispatcher
                functions := (∅ : Backends.NativeFunctionMap) }
      | .error err => .error err := by
  rw [emitYul_runtimeCode_eq_single_dispatcher_of_noMapping_noInternals_noFallback_noReceive
    contract hNoMapping hInternals hNoFallback hNoReceive]
  exact lowerRuntimeContractNative_nonFunc_eq_lowerStmtsNative
    [Compiler.CodegenCommon.initFreeMemoryPointer,
      Compiler.CodegenCommon.buildSwitch contract.functions none none]
    (by
      intro stmt hmem name params rets body h
      simp only [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with hInit | hSwitch
      · subst hInit
        simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h
      · rcases hSwitch with hSwitch | hNil
        · subst hSwitch
          simp [Compiler.CodegenCommon.buildSwitch] at h
        · cases hNil)

/-- If helper-free emitted runtime lowering succeeds, the successful contract is
exactly the native dispatcher shell produced by lowering the generated
dispatcher statement. -/
theorem lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher
    (contract : IRContract)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hNoMapping : contract.usesMapping = false)
    (hInternals : contract.internalFunctions = [])
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hLower :
      Backends.lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
        .ok nativeContract) :
    ∃ dispatcher : List EvmYul.Yul.Ast.Stmt,
      Backends.lowerStmtsNative
          [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch contract.functions none none] =
        .ok dispatcher ∧
      nativeContract =
        { dispatcher := .Block dispatcher
          functions := (∅ : Backends.NativeFunctionMap) } := by
  rw [lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive
    contract hNoMapping hInternals hNoFallback hNoReceive] at hLower
  cases hDispatcher :
      Backends.lowerStmtsNative
        [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch contract.functions none none] with
  | ok dispatcher =>
      rw [hDispatcher] at hLower
      simp only [Except.ok.injEq] at hLower
      exact ⟨dispatcher, rfl, hLower.symm⟩
  | error err =>
      rw [hDispatcher] at hLower
      simp at hLower

/-- A `.block` head in native lowering surfaces as a singleton `.Block` output
when the lowering succeeds. -/
theorem lowerStmtsNative_single_block_ok_singleton
    (stmts : List YulStmt)
    (lowered : List EvmYul.Yul.Ast.Stmt)
    (h : Backends.lowerStmtsNative [YulStmt.block stmts] = .ok lowered) :
    ∃ inner, lowered = [.Block inner] := by
  unfold Backends.lowerStmtsNative at h
  dsimp at h
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons] at h
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner :
      Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames [YulStmt.block stmts])
        0 stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk inner next =>
          rw [hInner] at h
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
            Backends.lowerStmtsNativeWithSwitchIds_nil, List.append_nil,
            Except.ok.injEq] at h
          exact ⟨inner, h.symm⟩

/-- A successful lowering of singleton `[.block stmts]` reveals exactly the
lowering result for the inner statement list. -/
theorem lowerStmtsNative_block_stmts_eq
    (stmts : List YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (h : Backends.lowerStmtsNative [YulStmt.block stmts] = .ok [.Block inner]) :
    ∃ next : Nat,
      Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames [YulStmt.block stmts])
        0 stmts = .ok (inner, next) := by
  unfold Backends.lowerStmtsNative at h
  dsimp at h
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons] at h
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner :
      Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames [YulStmt.block stmts])
        0 stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk inner' next =>
          rw [hInner] at h
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
            Backends.lowerStmtsNativeWithSwitchIds_nil, List.append_nil,
            Except.ok.injEq] at h
          injection h with hStmt _
          injection hStmt with hEq
          subst hEq
          exact ⟨next, rfl⟩

/-- A successful reserved-context lowering of singleton `[.block stmts]` reveals
exactly the lowering result for the inner statement list. -/
theorem lowerStmtsNativeWithSwitchIds_block_stmts_eq
    (reservedNames : List String) (n0 : Nat)
    (stmts : List YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        [YulStmt.block stmts] = .ok ([.Block inner], next)) :
    Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 stmts =
      .ok (inner, next) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons] at h
  rw [Backends.lowerStmtGroupNativeWithSwitchIds_block] at h
  cases hInner :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 stmts with
  | error err =>
      rw [hInner] at h
      simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk inner' next' =>
          rw [hInner] at h
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
            Backends.lowerStmtsNativeWithSwitchIds_nil, List.append_nil,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hList, hNext⟩ := h
          injection hList with hBlock
          injection hBlock with hInnerEq
          subst hInnerEq
          subst hNext
          rfl

/-- A `.let_`-headed statement-list lowering peels its head into a singleton
`.Let` statement and threads the unchanged switch counter through the tail. -/
theorem lowerStmtsNativeWithSwitchIds_let_head_eq
    (reservedNames : List String) (n0 : Nat)
    (name : String) (value : YulExpr)
    (rest : List YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            (YulStmt.let_ name value :: rest) = .ok (inner, next)) :
    ∃ rest' : List EvmYul.Yul.Ast.Stmt,
      inner = EvmYul.Yul.Ast.Stmt.Let [name]
                (some (Backends.lowerExprNative value)) :: rest' ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 rest =
        .ok (rest', next) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_let] at h
  simp only [Bind.bind, Except.bind] at h
  cases hRest : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 rest with
  | error err =>
      rw [hRest] at h
      simp only [reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk rest' n =>
          rw [hRest] at h
          simp only [Pure.pure, Except.pure, List.singleton_append,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hList, hNat⟩ := h
          subst hNat
          exact ⟨rest', hList.symm, rfl⟩

/-- A `.comment`-headed statement-list lowering emits a native no-op
`.Block []` and threads the switch counter through the tail unchanged.
Generated dispatch cases start with such a label comment, so this is the first
peel needed before reasoning about their executable guards. -/
theorem lowerStmtsNativeWithSwitchIds_comment_head_eq
    (reservedNames : List String) (n0 : Nat)
    (text : String)
    (rest : List YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            (YulStmt.comment text :: rest) = .ok (inner, next)) :
    ∃ rest' : List EvmYul.Yul.Ast.Stmt,
      inner = EvmYul.Yul.Ast.Stmt.Block [] :: rest' ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 rest =
        .ok (rest', next) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_comment] at h
  simp only [Bind.bind, Except.bind] at h
  cases hRest : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 rest with
  | error err =>
      rw [hRest] at h
      simp only [reduceCtorEq] at h
  | ok pair =>
      cases pair with
      | mk rest' n =>
          rw [hRest] at h
          simp only [Pure.pure, Except.pure, List.singleton_append,
            Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hList, hNat⟩ := h
          subst hNat
          exact ⟨rest', hList.symm, rfl⟩

/-- An `.if_`-headed statement-list lowering peels its head into a singleton
`.If` statement and threads the body's switch-counter advance through the tail. -/
theorem lowerStmtsNativeWithSwitchIds_if_head_eq
    (reservedNames : List String) (n0 : Nat)
    (cond : YulExpr) (body : List YulStmt)
    (rest : List YulStmt)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            (YulStmt.if_ cond body :: rest) = .ok (inner, next)) :
    ∃ (body' : List EvmYul.Yul.Ast.Stmt) (midN : Nat)
      (rest' : List EvmYul.Yul.Ast.Stmt),
      inner = EvmYul.Yul.Ast.Stmt.If
                (Backends.lowerExprNative cond) body' :: rest' ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 body =
        .ok (body', midN) ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames midN rest =
        .ok (rest', next) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_if] at h
  cases hBody : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0 body with
  | error _ => rw [hBody] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok bodyPair =>
    obtain ⟨body', midN⟩ := bodyPair
    rw [hBody] at h
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases hRest : Backends.lowerStmtsNativeWithSwitchIds reservedNames midN rest with
    | error _ =>
      rw [hRest] at h; simp only [reduceCtorEq] at h
    | ok restPair =>
      obtain ⟨rest', _⟩ := restPair
      rw [hRest] at h
      simp only [List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hList, hNat⟩ := h
      subst hNat
      exact ⟨body', midN, rest', hList.symm, rfl, hRest⟩

/-- Successful native lowering of a payable generated switch-case body exposes
the label no-op, the calldata-size guard, and the lowered user body tail. -/
theorem lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = true)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (guardBody bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      inner =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          guardBody ::
        bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  have hShape :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (YulStmt.comment s!"{fn.name}()" ::
          Compiler.CodegenCommon.calldatasizeGuard fn.params.length ::
          fn.body) = .ok (inner, next) := by
    simpa [switchCaseBody, Compiler.CodegenCommon.dispatchBody,
      Compiler.CodegenCommon.callvalueGuard, hPayable] using h
  rcases lowerStmtsNativeWithSwitchIds_comment_head_eq
      reservedNames n0 s!"{fn.name}()"
      (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      inner next hShape with
    ⟨afterComment, hInner, hAfterComment⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames n0
      (Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [],
         Yul.YulExpr.lit (4 + fn.params.length * 32)])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      fn.body afterComment next hAfterComment with
    ⟨guardBody, bodyStart, bodyNative, hAfterCommentShape, _hGuard,
      hBody⟩
  refine ⟨guardBody, bodyNative, bodyStart, ?_, hBody⟩
  rw [hInner, hAfterCommentShape]

/-- Successful native lowering of a non-payable generated switch-case body
exposes the label no-op, the callvalue guard, the calldata-size guard, and the
lowered user body tail. -/
theorem lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = false)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (callvalueGuardBody calldataGuardBody bodyNative :
          List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      inner =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          callvalueGuardBody ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          calldataGuardBody ::
        bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  have hShape :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (YulStmt.comment s!"{fn.name}()" ::
          Compiler.CodegenCommon.callvalueGuard ::
          Compiler.CodegenCommon.calldatasizeGuard fn.params.length ::
          fn.body) = .ok (inner, next) := by
    simpa [switchCaseBody, Compiler.CodegenCommon.dispatchBody,
      Compiler.CodegenCommon.callvalueGuard, hPayable] using h
  rcases lowerStmtsNativeWithSwitchIds_comment_head_eq
      reservedNames n0 s!"{fn.name}()"
      (Compiler.CodegenCommon.callvalueGuard ::
        Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      inner next hShape with
    ⟨afterComment, hInner, hAfterComment⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames n0
      (Yul.YulExpr.call "callvalue" [])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      afterComment next hAfterComment with
    ⟨callvalueGuardBody, calldataGuardStart, afterCallvalue,
      hAfterCommentShape, _hCallvalueGuard, hAfterCallvalue⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames calldataGuardStart
      (Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [],
         Yul.YulExpr.lit (4 + fn.params.length * 32)])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      fn.body afterCallvalue next hAfterCallvalue with
    ⟨calldataGuardBody, bodyStart, bodyNative, hAfterCallvalueShape,
      _hCalldataGuard, hBody⟩
  refine ⟨callvalueGuardBody, calldataGuardBody, bodyNative, bodyStart,
    ?_, hBody⟩
  rw [hInner, hAfterCommentShape, hAfterCallvalueShape]

set_option linter.unusedSimpArgs false in
/-- A singleton `.switch`-headed statement-list lowering reduces to a singleton
`.lowerNativeSwitchBlock` over the same source expression. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : YulExpr) (cases : List (Nat × List YulStmt))
    (defaultCase : Option (List YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [YulStmt.switch expr cases defaultCase] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
      (default' : List EvmYul.Yul.Ast.Stmt),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases' default'] := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      cases defaultCase with
      | none =>
          simp only [Backends.lowerStmtsNativeWithSwitchIds_nil,
            List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
          exact ⟨cases', [], h.1.symm⟩
      | some defaultBody =>
          dsimp only [] at h
          cases hDef : Backends.lowerStmtsNativeWithSwitchIds
              reservedNames midN defaultBody with
          | error _ =>
              rw [hDef] at h
              simp only [Bind.bind, Except.bind, reduceCtorEq] at h
          | ok defaultPair =>
              obtain ⟨default', _⟩ := defaultPair
              rw [hDef] at h
              simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
                Backends.lowerStmtsNativeWithSwitchIds_nil,
                List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨cases', default', h.1.symm⟩

def nativeRevertZeroZeroStmt : EvmYul.Yul.Ast.Stmt :=
  .ExprStmtCall
    (.Call (Sum.inl (EvmYul.Operation.REVERT : EvmYul.Operation .Yul))
      [.Lit (EvmYul.UInt256.ofNat 0), .Lit (EvmYul.UInt256.ofNat 0)])

@[simp] theorem nativeStmtWriteNames_nativeRevertZeroZeroStmt :
    Backends.nativeStmtWriteNames nativeRevertZeroZeroStmt = [] := by
  simp [nativeRevertZeroZeroStmt, Backends.nativeStmtWriteNames]

@[simp] theorem nativeStmtsWriteNames_singleton_nativeRevertZeroZeroStmt :
    Backends.nativeStmtsWriteNames [nativeRevertZeroZeroStmt] = [] := by
  simp [Backends.nativeStmtsWriteNames]

theorem nativeSwitchTempsFreshForWrites_nil
    (switchId : Nat) :
    Backends.nativeSwitchTempsFreshForWrites switchId [] := by
  simp [Backends.nativeSwitchTempsFreshForWrites]

theorem nativeSwitchTempsFreshForWrites_nativeRevertZeroZeroStmt
    (switchId : Nat) :
    Backends.nativeSwitchTempsFreshForWrites switchId
      (Backends.nativeStmtsWriteNames [nativeRevertZeroZeroStmt]) := by
  simp [nativeSwitchTempsFreshForWrites_nil]

theorem nativeStmtsWriteNames_payable_dispatch_guard_prefix
    (fn : IRFunction) (bodyNative : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames
        (EvmYul.Yul.Ast.Stmt.Block [] ::
          EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit (4 + fn.params.length * 32)]))
            [nativeRevertZeroZeroStmt] ::
          bodyNative) =
      Backends.nativeStmtsWriteNames bodyNative := by
  simp [Backends.nativeStmtsWriteNames, Backends.nativeStmtWriteNames]

theorem nativeStmtsWriteNames_nonpayable_dispatch_guard_prefix
    (fn : IRFunction) (bodyNative : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames
        (EvmYul.Yul.Ast.Stmt.Block [] ::
          EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
            [nativeRevertZeroZeroStmt] ::
          EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit (4 + fn.params.length * 32)]))
            [nativeRevertZeroZeroStmt] ::
          bodyNative) =
      Backends.nativeStmtsWriteNames bodyNative := by
  simp [Backends.nativeStmtsWriteNames, Backends.nativeStmtWriteNames]

/-- The singleton default-revert body lowers to the native `revert(0,0)` stmt
without advancing the native switch counter. -/
theorem lowerStmtsNativeWithSwitchIds_revert_zero_zero
    (reservedNames : List String) (n : Nat) :
    Backends.lowerStmtsNativeWithSwitchIds reservedNames n
        [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] =
      .ok ([nativeRevertZeroZeroStmt], n) := by
  simp [Backends.lowerStmtsNativeWithSwitchIds, nativeRevertZeroZeroStmt,
    Backends.lowerExprNative, Backends.lookupRuntimePrimOp]
  rfl

/-- Concrete generated-guard variant of
`lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq`: the payable case
prefix lowers the generated calldata-size guard body to
`[nativeRevertZeroZeroStmt]`. -/
theorem lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = true)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      inner =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          [nativeRevertZeroZeroStmt] ::
        bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  have hShape :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (YulStmt.comment s!"{fn.name}()" ::
          Compiler.CodegenCommon.calldatasizeGuard fn.params.length ::
          fn.body) = .ok (inner, next) := by
    simpa [switchCaseBody, Compiler.CodegenCommon.dispatchBody,
      Compiler.CodegenCommon.callvalueGuard, hPayable] using h
  rcases lowerStmtsNativeWithSwitchIds_comment_head_eq
      reservedNames n0 s!"{fn.name}()"
      (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      inner next hShape with
    ⟨afterComment, hInner, hAfterComment⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames n0
      (Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [],
         Yul.YulExpr.lit (4 + fn.params.length * 32)])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      fn.body afterComment next hAfterComment with
    ⟨guardBody, bodyStart, bodyNative, hAfterCommentShape, hGuard,
      hBody⟩
  have hGuardPair :
      ([nativeRevertZeroZeroStmt], n0) = (guardBody, bodyStart) := by
    exact Except.ok.inj
      ((lowerStmtsNativeWithSwitchIds_revert_zero_zero reservedNames n0).symm.trans
        hGuard)
  have hGuardBody : guardBody = [nativeRevertZeroZeroStmt] := by
    exact (congrArg Prod.fst hGuardPair).symm
  refine ⟨bodyNative, bodyStart, ?_, hBody⟩
  rw [hInner, hAfterCommentShape, hGuardBody]

theorem nativeStmtsWriteNames_lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_eq_body
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = true)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.nativeStmtsWriteNames inner =
        Backends.nativeStmtsWriteNames bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_payable_revert_eq
      reservedNames n0 fn inner next hPayable h with
    ⟨bodyNative, bodyStart, hInner, hBody⟩
  refine ⟨bodyNative, bodyStart, ?_, hBody⟩
  rw [hInner, nativeStmtsWriteNames_payable_dispatch_guard_prefix]

/-- Concrete generated-guard variant of
`lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq`: the non-payable
case prefix lowers both generated revert bodies to `[nativeRevertZeroZeroStmt]`.
-/
theorem lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = false)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      inner =
        EvmYul.Yul.Ast.Stmt.Block [] ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          [nativeRevertZeroZeroStmt] ::
        EvmYul.Yul.Ast.Stmt.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit (4 + fn.params.length * 32)]))
          [nativeRevertZeroZeroStmt] ::
        bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  have hShape :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (YulStmt.comment s!"{fn.name}()" ::
          Compiler.CodegenCommon.callvalueGuard ::
          Compiler.CodegenCommon.calldatasizeGuard fn.params.length ::
          fn.body) = .ok (inner, next) := by
    simpa [switchCaseBody, Compiler.CodegenCommon.dispatchBody,
      Compiler.CodegenCommon.callvalueGuard, hPayable] using h
  rcases lowerStmtsNativeWithSwitchIds_comment_head_eq
      reservedNames n0 s!"{fn.name}()"
      (Compiler.CodegenCommon.callvalueGuard ::
        Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      inner next hShape with
    ⟨afterComment, hInner, hAfterComment⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames n0
      (Yul.YulExpr.call "callvalue" [])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      (Compiler.CodegenCommon.calldatasizeGuard fn.params.length :: fn.body)
      afterComment next hAfterComment with
    ⟨callvalueGuardBody, calldataGuardStart, afterCallvalue,
      hAfterCommentShape, hCallvalueGuard, hAfterCallvalue⟩
  rcases lowerStmtsNativeWithSwitchIds_if_head_eq
      reservedNames calldataGuardStart
      (Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [],
         Yul.YulExpr.lit (4 + fn.params.length * 32)])
      [YulStmt.expr (Yul.YulExpr.call "revert" [Yul.YulExpr.lit 0,
        Yul.YulExpr.lit 0])]
      fn.body afterCallvalue next hAfterCallvalue with
    ⟨calldataGuardBody, bodyStart, bodyNative, hAfterCallvalueShape,
      hCalldataGuard, hBody⟩
  have hCallvaluePair :
      ([nativeRevertZeroZeroStmt], n0) =
        (callvalueGuardBody, calldataGuardStart) := by
    exact Except.ok.inj
      ((lowerStmtsNativeWithSwitchIds_revert_zero_zero reservedNames n0).symm.trans
        hCallvalueGuard)
  have hCallvalueGuardBody :
      callvalueGuardBody = [nativeRevertZeroZeroStmt] := by
    exact (congrArg Prod.fst hCallvaluePair).symm
  have hCalldataPair :
      ([nativeRevertZeroZeroStmt], calldataGuardStart) =
        (calldataGuardBody, bodyStart) := by
    exact Except.ok.inj
      ((lowerStmtsNativeWithSwitchIds_revert_zero_zero
        reservedNames calldataGuardStart).symm.trans hCalldataGuard)
  have hCalldataGuardBody :
      calldataGuardBody = [nativeRevertZeroZeroStmt] := by
    exact (congrArg Prod.fst hCalldataPair).symm
  refine ⟨bodyNative, bodyStart, ?_, hBody⟩
  rw [hInner, hAfterCommentShape, hAfterCallvalueShape,
    hCallvalueGuardBody, hCalldataGuardBody]

theorem nativeStmtsWriteNames_lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_eq_body
    (reservedNames : List String) (n0 : Nat)
    (fn : IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (hPayable : fn.payable = false)
    (h :
      Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
        (switchCaseBody fn) = .ok (inner, next)) :
    ∃ (bodyNative : List EvmYul.Yul.Ast.Stmt) (bodyStart : Nat),
      Backends.nativeStmtsWriteNames inner =
        Backends.nativeStmtsWriteNames bodyNative ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart fn.body =
        .ok (bodyNative, next) := by
  rcases lowerStmtsNativeWithSwitchIds_switchCaseBody_nonpayable_revert_eq
      reservedNames n0 fn inner next hPayable h with
    ⟨bodyNative, bodyStart, hInner, hBody⟩
  refine ⟨bodyNative, bodyStart, ?_, hBody⟩
  rw [hInner, nativeStmtsWriteNames_nonpayable_dispatch_guard_prefix]

private theorem nativeSwitchTempsFreshForNativeBodies_cons_of_lowerSwitchCasesNativeWithSwitchIds
    (reservedNames : List String) (nextSwitchId final switchId tag : Nat)
    (body : List YulStmt) (rest : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      nextSwitchId ((tag, body) :: rest) = .ok (cases', final))
    (hHeadFresh :
      ∀ bodyNative bodyEnd,
        Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body =
          .ok (bodyNative, bodyEnd) →
        Backends.nativeSwitchTempsFreshForWrites switchId
          (Backends.nativeStmtsWriteNames bodyNative))
    (hRestFresh :
      ∀ bodyNative bodyEnd restNative restEnd,
        Backends.lowerStmtsNativeWithSwitchIds reservedNames nextSwitchId body =
          .ok (bodyNative, bodyEnd) →
        Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames bodyEnd rest = .ok (restNative, restEnd) →
        Backends.nativeSwitchTempsFreshForNativeBodies switchId restNative defaultBody) :
    Backends.nativeSwitchTempsFreshForNativeBodies switchId cases' defaultBody := by
  rw [Backends.lowerSwitchCasesNativeWithSwitchIds_cons] at hLower
  cases hBody : Backends.lowerStmtsNativeWithSwitchIds reservedNames
      nextSwitchId body with
  | error err =>
      rw [hBody] at hLower
      simp only [Bind.bind, Except.bind, reduceCtorEq] at hLower
  | ok bodyPair =>
      obtain ⟨bodyNative, bodyEnd⟩ := bodyPair
      rw [hBody] at hLower
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hLower
      cases hRest : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames bodyEnd rest with
      | error err =>
          rw [hRest] at hLower
          simp only [reduceCtorEq] at hLower
      | ok restPair =>
          obtain ⟨restNative, restEnd⟩ := restPair
          rw [hRest] at hLower
          simp only [Except.ok.injEq, Prod.mk.injEq] at hLower
          rcases hLower with ⟨hCases', hFinal⟩
          subst cases'
          subst final
          constructor
          · intro tag' body' hMem
            rcases (by simpa using hMem : (tag', body') = (tag, bodyNative) ∨
                (tag', body') ∈ restNative) with hHead | hTail
            · cases hHead
              exact hHeadFresh bodyNative bodyEnd hBody
            · exact (hRestFresh bodyNative bodyEnd restNative restEnd hBody hRest).1 tag' body' hTail
          · exact
              (hRestFresh bodyNative bodyEnd restNative restEnd hBody hRest).2

theorem nativeSwitchTempsFreshForNativeBodies_of_lowerSwitchCasesNativeWithSwitchIds
    (reservedNames : List String) (nextSwitchId final switchId : Nat)
    (cases : List (Nat × List YulStmt))
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hLower :
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames nextSwitchId
        cases = .ok (cases', final))
    (hCaseFresh :
      ∀ tag body bodyNative bodyStart bodyEnd,
        (tag, body) ∈ cases →
        Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart body =
          .ok (bodyNative, bodyEnd) →
        Backends.nativeSwitchTempsFreshForWrites switchId
          (Backends.nativeStmtsWriteNames bodyNative))
    (hDefaultFresh :
      Backends.nativeSwitchTempsFreshForWrites switchId
        (Backends.nativeStmtsWriteNames defaultBody)) :
    Backends.nativeSwitchTempsFreshForNativeBodies switchId cases'
      defaultBody := by
  induction cases generalizing nextSwitchId cases' final with
  | nil =>
    rw [Backends.lowerSwitchCasesNativeWithSwitchIds_nil] at hLower
    rcases (by simpa using hLower : cases' = [] ∧ nextSwitchId = final) with
      ⟨hCases', _⟩
    subst cases'
    simp [Backends.nativeSwitchTempsFreshForNativeBodies, hDefaultFresh]
  | cons head rest ih =>
    obtain ⟨tag, body⟩ := head
    exact
      nativeSwitchTempsFreshForNativeBodies_cons_of_lowerSwitchCasesNativeWithSwitchIds
        reservedNames nextSwitchId final switchId tag body rest cases'
        defaultBody hLower
        (by
          intro bodyNative bodyEnd hBody
          exact hCaseFresh tag body bodyNative nextSwitchId bodyEnd
            (by simp) hBody)
        (by
          intro bodyNative bodyEnd restNative restEnd _hBody hRest
          exact ih bodyEnd restEnd restNative hRest (by
            intro tag' body' bodyNative' bodyStart bodyEnd' hMem hLowerBody
            exact hCaseFresh tag' body' bodyNative' bodyStart bodyEnd'
              (by simp [hMem]) hLowerBody))

theorem nativeSwitchTempsFreshForNativeBodies_buildSwitchSourceCases_of_lowerSwitchCasesNativeWithSwitchIds_of_case_body_fresh
    (reservedNames : List String) (n0 midN : Nat)
    (funcs : List IRFunction)
    (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hLower : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1)
      (buildSwitchSourceCases funcs) = .ok (cases', midN))
    (hCaseFresh :
      ∀ fn bodyNative bodyStart bodyEnd,
        fn ∈ funcs →
        Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
          (switchCaseBody fn) = .ok (bodyNative, bodyEnd) →
        Backends.nativeSwitchTempsFreshForWrites
          (Backends.freshNativeSwitchId reservedNames n0)
          (Backends.nativeStmtsWriteNames bodyNative)) :
    Backends.nativeSwitchTempsFreshForNativeBodies
      (Backends.freshNativeSwitchId reservedNames n0) cases'
      [nativeRevertZeroZeroStmt] := by
  exact
    nativeSwitchTempsFreshForNativeBodies_of_lowerSwitchCasesNativeWithSwitchIds
      reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      (Backends.freshNativeSwitchId reservedNames n0)
      (buildSwitchSourceCases funcs) cases' [nativeRevertZeroZeroStmt] hLower
      (by
        intro tag body bodyNative bodyStart bodyEnd hMem hLowerBody
        simp only [buildSwitchSourceCases, List.mem_map] at hMem
        rcases hMem with ⟨fn, hFnMem, hEq⟩
        cases hEq
        exact hCaseFresh fn bodyNative bodyStart bodyEnd hFnMem hLowerBody)
      (nativeSwitchTempsFreshForWrites_nativeRevertZeroZeroStmt
        (Backends.freshNativeSwitchId reservedNames n0))

set_option linter.unusedSimpArgs false in
/-- A singleton switch whose default is `revert(0,0)` lowers to a singleton
native switch block with concrete `[nativeRevertZeroZeroStmt]` default body. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq
    (reservedNames : List String) (n0 : Nat)
    (expr : YulExpr) (cases : List (Nat × List YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [YulStmt.switch expr cases
              (some [YulStmt.expr (YulExpr.call "revert"
                [YulExpr.lit 0, YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [nativeRevertZeroZeroStmt]] := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rw [lowerStmtsNativeWithSwitchIds_revert_zero_zero] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
        Backends.lowerStmtsNativeWithSwitchIds_nil,
        List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨cases', h.1.symm⟩

set_option linter.unusedSimpArgs false in
/-- Source-lowered companion exposing the case-list lowering equation for a
singleton switch whose default is `revert(0,0)`. -/
theorem lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
    (reservedNames : List String) (n0 : Nat)
    (expr : YulExpr) (cases : List (Nat × List YulStmt))
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [YulStmt.switch expr cases
              (some [YulStmt.expr (YulExpr.call "revert"
                [YulExpr.lit 0, YulExpr.lit 0])])] = .ok (inner, next)) :
    ∃ (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      inner = [Backends.lowerNativeSwitchBlock expr
        (Backends.freshNativeSwitchId reservedNames n0) cases'
        [nativeRevertZeroZeroStmt]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1) cases =
          .ok (cases', midN) := by
  rw [Backends.lowerStmtsNativeWithSwitchIds_cons,
      Backends.lowerStmtGroupNativeWithSwitchIds_switch] at h
  dsimp only [] at h
  cases hCases : Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
      (Backends.freshNativeSwitchId reservedNames n0 + 1) cases with
  | error _ =>
      rw [hCases] at h; simp only [Bind.bind, Except.bind, reduceCtorEq] at h
  | ok casesPair =>
      obtain ⟨cases', midN⟩ := casesPair
      rw [hCases] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      rw [lowerStmtsNativeWithSwitchIds_revert_zero_zero] at h
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
        Backends.lowerStmtsNativeWithSwitchIds_nil,
        List.singleton_append, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨cases', midN, h.1.symm, rfl⟩

/-- Generic native-lowering shape of the no-fallback/no-receive generated
dispatcher.

This theorem peels the actual `buildSwitch funcs none none` source emitted by
codegen: the lowered inner block is the generated selector prologue, the
selector-miss default lowers to native `revert(0,0)`, and the selector-hit
switch is linked to the native lowering of the source case list emitted by
`buildSwitch`. -/
theorem buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (h : Backends.lowerStmtsNative
            [Compiler.CodegenCommon.buildSwitch funcs none none] =
          .ok [.Block inner]) :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (YulExpr.call "iszero"
              [YulExpr.call "lt"
                [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) := by
  obtain ⟨_, hInner⟩ := lowerStmtsNative_block_stmts_eq _ _ h
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', midN, hBody2Eq, hLowerCases⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
      _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, _, cases', midN, hLet, hLowerCases⟩

/-- Reserved-context version of
`buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered`, used when the
generated dispatcher is lowered after helper functions have populated the
native runtime's reserved-name context. -/
theorem buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Compiler.CodegenCommon.buildSwitch funcs none none] =
          .ok ([.Block inner], next)) :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat),
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (YulExpr.call "iszero"
              [YulExpr.call "lt"
                [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) := by
  have hInner :=
    lowerStmtsNativeWithSwitchIds_block_stmts_eq reservedNames n0 _ inner next h
  obtain ⟨_, hLet, hRestLowering⟩ :=
    lowerStmtsNativeWithSwitchIds_let_head_eq _ _ _ _ _ _ _ hInner
  obtain ⟨body1', _, _, hIf1, _, hRest1⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRestLowering
  obtain ⟨_, _, _, hIf2, hBody2, hRest2⟩ :=
    lowerStmtsNativeWithSwitchIds_if_head_eq _ _ _ _ _ _ _ hRest1
  rw [Backends.lowerStmtsNativeWithSwitchIds_nil,
      Except.ok.injEq, Prod.mk.injEq] at hRest2
  obtain ⟨hNil, _⟩ := hRest2
  subst hNil
  obtain ⟨cases', midN, hBody2Eq, hLowerCases⟩ :=
    lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered
      _ _ _ _ _ _ hBody2
  rw [hBody2Eq] at hIf2; rw [hIf2] at hIf1; rw [hIf1] at hLet
  exact ⟨body1', _, cases', midN, hLet, hLowerCases⟩

/-- Selector-hit companion of
`buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered`: opening the
generated dispatcher lowering also lifts an `IRFunction` lookup hit through
the lowered native switch cases. -/
theorem buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (selector : Nat) (fn : IRFunction)
    (h : Backends.lowerStmtsNative
            [Compiler.CodegenCommon.buildSwitch funcs none none] =
          .ok [.Block inner])
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn) :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (YulExpr.call "iszero"
              [YulExpr.call "lt"
                [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames n0 + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered funcs inner h
  obtain ⟨body', bodyStart, bodyEnd, hCase, hBodyLower⟩ :=
    lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function
      reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      selector funcs fn cases' hLowerCases hFind
  exact ⟨body1, reservedNames, n0, cases', midN, body', bodyStart, bodyEnd,
    hInner, hLowerCases, hCase, hBodyLower⟩

/-- Reserved-context selector-hit companion of
`buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds`. -/
theorem buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function_withSwitchIds
    (reservedNames : List String) (n0 : Nat)
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt) (next : Nat)
    (selector : Nat) (fn : IRFunction)
    (h : Backends.lowerStmtsNativeWithSwitchIds reservedNames n0
            [Compiler.CodegenCommon.buildSwitch funcs none none] =
          .ok ([.Block inner], next))
    (hFind : funcs.find? (fun f => f.selector == selector) = some fn) :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (switchStart : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)) (midN : Nat)
      (body' : List EvmYul.Yul.Ast.Stmt) (bodyStart bodyEnd : Nat),
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (YulExpr.call "iszero"
              [YulExpr.call "lt"
                [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames switchStart) cases'
              [nativeRevertZeroZeroStmt]]] ∧
      Backends.lowerSwitchCasesNativeWithSwitchIds reservedNames
        (Backends.freshNativeSwitchId reservedNames switchStart + 1)
        (buildSwitchSourceCases funcs) = .ok (cases', midN) ∧
      cases'.find? (fun entry => entry.1 == selector) =
        some (selector, body') ∧
      Backends.lowerStmtsNativeWithSwitchIds reservedNames bodyStart
        (switchCaseBody fn) = .ok (body', bodyEnd) := by
  obtain ⟨body1, switchStart, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered_withSwitchIds
      reservedNames n0 funcs inner next h
  obtain ⟨body', bodyStart, bodyEnd, hCase, hBodyLower⟩ :=
    lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function
      reservedNames (Backends.freshNativeSwitchId reservedNames switchStart + 1) midN
      selector funcs fn cases' hLowerCases hFind
  exact ⟨body1, switchStart, cases', midN, body', bodyStart, bodyEnd,
    hInner, hLowerCases, hCase, hBodyLower⟩

/-- Selector-miss companion of
`buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered`: opening the
generated dispatcher lowering also lifts an `IRFunction` lookup miss through
the lowered native switch cases. -/
theorem buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function
    (funcs : List IRFunction)
    (inner : List EvmYul.Yul.Ast.Stmt)
    (selector : Nat)
    (h : Backends.lowerStmtsNative
            [Compiler.CodegenCommon.buildSwitch funcs none none] =
          .ok [.Block inner])
    (hFind : funcs.find? (fun f => f.selector == selector) = none) :
    ∃ (body1 : List EvmYul.Yul.Ast.Stmt) (reservedNames : List String) (n0 : Nat)
      (cases' : List (Nat × List EvmYul.Yul.Ast.Stmt)),
      inner =
        [EvmYul.Yul.Ast.Stmt.Let ["__has_selector"]
            (some (Backends.lowerExprNative (YulExpr.call "iszero"
              [YulExpr.call "lt"
                [YulExpr.call "calldatasize" [], YulExpr.lit 4]]))),
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative
              (YulExpr.call "iszero" [YulExpr.ident "__has_selector"])) body1,
         EvmYul.Yul.Ast.Stmt.If
            (Backends.lowerExprNative (YulExpr.ident "__has_selector"))
            [Backends.lowerNativeSwitchBlock
              (YulExpr.call "shr"
                [YulExpr.lit Compiler.Constants.selectorShift,
                 YulExpr.call "calldataload" [YulExpr.lit 0]])
              (Backends.freshNativeSwitchId reservedNames n0) cases'
              [nativeRevertZeroZeroStmt]]] ∧
      cases'.find? (fun entry => entry.1 == selector) = none := by
  obtain ⟨body1, reservedNames, n0, cases', midN, hInner, hLowerCases⟩ :=
    buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered funcs inner h
  have hCase :=
    lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function
      reservedNames (Backends.freshNativeSwitchId reservedNames n0 + 1) midN
      selector funcs cases' hLowerCases hFind
  exact ⟨body1, reservedNames, n0, cases', hInner, hCase⟩

theorem generatedRuntimeDispatcherHasNoFuncDefs_buildSwitch_noFallback_noReceive
    (funcs : List IRFunction)
    (hBodies : ∀ fn, fn ∈ funcs → yulStmtsContainFuncDef fn.body = false) :
    generatedRuntimeDispatcherHasNoFuncDefs
      [Compiler.CodegenCommon.buildSwitch funcs none none] = true := by
  have hNoFunc : ∀ name params rets body,
      Compiler.CodegenCommon.buildSwitch funcs none none ≠
        YulStmt.funcDef name params rets body := by
    intro name params rets body h
    simp [Compiler.CodegenCommon.buildSwitch] at h
  rw [generatedRuntimeDispatcherHasNoFuncDefs_nonFunc_cons
    (Compiler.CodegenCommon.buildSwitch funcs none none) [] hNoFunc]
  simp [generatedRuntimeDispatcherHasNoFuncDefs,
    buildSwitch_noFuncDefs_noFallback_noReceive funcs hBodies]

theorem generatedRuntimeDispatcherHasNoFuncDefs_funcDef_prefix_append
    (funcPrefix suffix : List YulStmt)
    (hFuncDefs : ∀ stmt, stmt ∈ funcPrefix →
      ∃ name params rets body, stmt = YulStmt.funcDef name params rets body) :
    generatedRuntimeDispatcherHasNoFuncDefs (funcPrefix ++ suffix) =
      generatedRuntimeDispatcherHasNoFuncDefs suffix := by
  induction funcPrefix with
  | nil => rfl
  | cons stmt rest ih =>
      rcases hFuncDefs stmt (by simp) with ⟨name, params, rets, body, rfl⟩
      simp [ih (by
        intro stmt hmem
        exact hFuncDefs stmt (by simp [hmem]))]

theorem generatedRuntimeDispatcherHasNoFuncDefs_runtimeCode_noFallback_noReceive
    (contract : IRContract)
    (hInternals : ∀ stmt, stmt ∈ contract.internalFunctions →
      ∃ name params rets body, stmt = YulStmt.funcDef name params rets body)
    (hBodies : ∀ fn, fn ∈ contract.functions →
      yulStmtsContainFuncDef fn.body = false)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    generatedRuntimeDispatcherHasNoFuncDefs (Compiler.runtimeCode contract) = true := by
  let runtimePrefix :=
    (if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
      contract.internalFunctions
  have hPrefix :
      ∀ stmt, stmt ∈ runtimePrefix →
        ∃ name params rets body, stmt = YulStmt.funcDef name params rets body := by
    intro stmt hmem
    simp only [runtimePrefix, List.mem_append] at hmem
    rcases hmem with hMapping | hInternal
    · split at hMapping <;> simp at hMapping
      subst hMapping
      exact ⟨"mappingSlot", ["baseSlot", "key"], ["slot"], _, rfl⟩
    · exact hInternals stmt hInternal
  rw [Compiler.runtimeCode, Compiler.CodegenCommon.runtimeCode]
  simp [hNoFallback, hNoReceive]
  rw [← List.append_assoc]
  change generatedRuntimeDispatcherHasNoFuncDefs
      (runtimePrefix ++ [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch contract.functions none none]) =
    true
  rw [generatedRuntimeDispatcherHasNoFuncDefs_funcDef_prefix_append runtimePrefix
    [Compiler.CodegenCommon.initFreeMemoryPointer,
      Compiler.CodegenCommon.buildSwitch contract.functions none none] hPrefix]
  rw [generatedRuntimeDispatcherHasNoFuncDefs_nonFunc_cons]
  · simp [Compiler.CodegenCommon.initFreeMemoryPointer,
      yulStmtContainsFuncDef,
      generatedRuntimeDispatcherHasNoFuncDefs_buildSwitch_noFallback_noReceive
        contract.functions hBodies]
  · intro name params rets body h
    simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h

theorem generatedRuntimeDispatcherHasNoFuncDefs_emitYul_runtimeCode_noFallback_noReceive
    (contract : IRContract)
    (hInternals : ∀ stmt, stmt ∈ contract.internalFunctions →
      ∃ name params rets body, stmt = YulStmt.funcDef name params rets body)
    (hBodies : ∀ fn, fn ∈ contract.functions →
      yulStmtsContainFuncDef fn.body = false)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    generatedRuntimeDispatcherHasNoFuncDefs
      (Compiler.emitYul contract).runtimeCode = true := by
  simpa [Compiler.emitYul, Compiler.CodegenCommon.emitYul] using
    generatedRuntimeDispatcherHasNoFuncDefs_runtimeCode_noFallback_noReceive
      contract hInternals hBodies hNoFallback hNoReceive

theorem generatedRuntimeFunctionNamesUnique_append_nonFunc_suffix
    (funcPrefix suffix : List YulStmt)
    (hSuffix : ∀ stmt, stmt ∈ suffix →
      ∀ name params rets body, stmt ≠ YulStmt.funcDef name params rets body) :
    generatedRuntimeFunctionNamesUnique (funcPrefix ++ suffix) =
      generatedRuntimeFunctionNamesUnique funcPrefix := by
  simp [generatedRuntimeFunctionNamesUnique,
    yulRuntimeTopLevelFunctionNames_eq_nil_of_all_nonFunc suffix hSuffix]

theorem generatedRuntimeFunctionNamesUnique_buildSwitch_append
    (funcPrefix : List YulStmt)
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) :
    generatedRuntimeFunctionNamesUnique
      (funcPrefix ++ [Compiler.CodegenCommon.buildSwitch funcs fallback receive]) =
      generatedRuntimeFunctionNamesUnique funcPrefix := by
  apply generatedRuntimeFunctionNamesUnique_append_nonFunc_suffix
  intro stmt hmem name params rets body h
  simp only [List.mem_singleton] at hmem
  subst hmem
  cases fallback <;> cases receive <;>
    simp [Compiler.CodegenCommon.buildSwitch] at h

theorem generatedRuntimeFunctionNamesUnique_initFreeMemoryPointer_buildSwitch_append
    (funcPrefix : List YulStmt)
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) :
    generatedRuntimeFunctionNamesUnique
      (funcPrefix ++ [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch funcs fallback receive]) =
      generatedRuntimeFunctionNamesUnique funcPrefix := by
  apply generatedRuntimeFunctionNamesUnique_append_nonFunc_suffix
  intro stmt hmem name params rets body h
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with hInit | hSwitch
  · subst hInit
    simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h
  · rcases hSwitch with hSwitch | hNil
    · subst hSwitch
      cases fallback <;> cases receive <;>
        simp [Compiler.CodegenCommon.buildSwitch] at h
    · cases hNil

theorem generatedRuntimeFunctionNamesUnique_runtimeCode
    (contract : IRContract)
    (hPrefixUnique : generatedRuntimeFunctionNamesUnique
      ((if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions) = true) :
    generatedRuntimeFunctionNamesUnique (Compiler.runtimeCode contract) = true := by
  let runtimePrefix :=
    (if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
      contract.internalFunctions
  rw [Compiler.runtimeCode, Compiler.CodegenCommon.runtimeCode]
  change generatedRuntimeFunctionNamesUnique
      (runtimePrefix ++ [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch contract.functions
        contract.fallbackEntrypoint contract.receiveEntrypoint]) = true
  rw [generatedRuntimeFunctionNamesUnique_initFreeMemoryPointer_buildSwitch_append]
  exact hPrefixUnique

theorem generatedRuntimeFunctionNamesUnique_emitYul_runtimeCode
    (contract : IRContract)
    (hPrefixUnique : generatedRuntimeFunctionNamesUnique
      ((if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions) = true) :
    generatedRuntimeFunctionNamesUnique
      (Compiler.emitYul contract).runtimeCode = true := by
  simpa [Compiler.emitYul, Compiler.CodegenCommon.emitYul] using
    generatedRuntimeFunctionNamesUnique_runtimeCode contract hPrefixUnique

theorem mappingSlotFuncAt_body_noFuncDefs (scratchBase : Nat) :
    yulStmtsContainFuncDef
      (match Compiler.mappingSlotFuncAt scratchBase with
      | YulStmt.funcDef _ _ _ body => body
      | _ => []) = false := by
  simp [Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt,
    yulStmtContainsFuncDef, yulStmtsContainFuncDef]

/-- Native EVMYulLean definition produced by lowering the generated
`mappingSlot` helper at scratch base zero. -/
def nativeMappingSlotFunctionDefinition : EvmYul.Yul.Ast.FunctionDefinition :=
  EvmYul.Yul.Ast.FunctionDefinition.Def ["baseSlot", "key"] ["slot"]
    [ .ExprStmtCall (.Call (.inl EvmYul.Operation.MSTORE)
        [.Lit (EvmYul.UInt256.ofNat 0), .Var "key"])
    , .ExprStmtCall (.Call (.inl EvmYul.Operation.MSTORE)
        [.Lit (EvmYul.UInt256.ofNat 32), .Var "baseSlot"])
    , .Let ["slot"] (some (.Call (.inl EvmYul.Operation.KECCAK256)
        [.Lit (EvmYul.UInt256.ofNat 0), .Lit (EvmYul.UInt256.ofNat 64)]))
    ]

/-- The generated `mappingSlot` helper at scratch base zero lowers to the
corresponding native EVMYulLean helper function definition for any ambient
reserved-name set. -/
theorem lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero
    (globalReservedNames : List String) :
    Backends.lowerFunctionDefinitionNativeWithReserved
      globalReservedNames ["baseSlot", "key"] ["slot"]
      (match Compiler.mappingSlotFuncAt 0 with
      | YulStmt.funcDef _ _ _ body => body
      | _ => []) = .ok nativeMappingSlotFunctionDefinition := by
  simp [Backends.lowerFunctionDefinitionNativeWithReserved,
    Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt,
    Backends.lowerStmtsNativeWithSwitchIds, Backends.lowerExprNative,
    Backends.lowerAssignNative, Backends.lookupRuntimePrimOp,
    nativeMappingSlotFunctionDefinition, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

/-- Body-form variant of
`lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero`, for proof
sites that have already unfolded the generated helper. -/
theorem lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero_body
    (globalReservedNames : List String) :
    Backends.lowerFunctionDefinitionNativeWithReserved
      globalReservedNames ["baseSlot", "key"] ["slot"]
      [YulStmt.expr
        (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "key"]),
       YulStmt.expr
        (YulExpr.call "mstore"
          [YulExpr.lit (0 + 32), YulExpr.ident "baseSlot"]),
       YulStmt.assign "slot"
        (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 64])] =
      .ok nativeMappingSlotFunctionDefinition := by
  simp [Backends.lowerFunctionDefinitionNativeWithReserved,
    Backends.lowerStmtsNativeWithSwitchIds, Backends.lowerExprNative,
    Backends.lowerAssignNative, Backends.lookupRuntimePrimOp,
    nativeMappingSlotFunctionDefinition, Bind.bind, Except.bind, Pure.pure,
    Except.pure]

def nativeMappingSlotFunctionBody : List EvmYul.Yul.Ast.Stmt :=
  [ .ExprStmtCall (.Call (.inl EvmYul.Operation.MSTORE)
      [.Lit (EvmYul.UInt256.ofNat 0), .Var "key"])
  , .ExprStmtCall (.Call (.inl EvmYul.Operation.MSTORE)
      [.Lit (EvmYul.UInt256.ofNat 32), .Var "baseSlot"])
  , .Let ["slot"] (some (.Call (.inl EvmYul.Operation.KECCAK256)
      [.Lit (EvmYul.UInt256.ofNat 0), .Lit (EvmYul.UInt256.ofNat 64)]))
  ]

theorem nativeMappingSlotFunctionDefinition_body :
    nativeMappingSlotFunctionDefinition.body = nativeMappingSlotFunctionBody := by
  rfl

/-- Mapping-helper, no-internal/no-fallback/no-receive emitted runtimes lower
by first packaging the generated `mappingSlot` helper into the native function
map, then lowering the dispatcher in the full emitted-runtime reserved-name
context. -/
theorem lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved
    (contract : IRContract)
    (hMapping : contract.usesMapping = true)
    (hInternals : contract.internalFunctions = [])
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    Backends.lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      match Backends.lowerStmtsNativeWithSwitchIds
          (Backends.yulStmtsIdentifierNames
            (Compiler.emitYul contract).runtimeCode)
          0 [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch contract.functions none none] with
      | .ok (dispatcher, _) =>
          .ok { dispatcher := .Block dispatcher
                functions := ((∅ : Backends.NativeFunctionMap).insert
                  "mappingSlot" nativeMappingSlotFunctionDefinition) }
      | .error err => .error err := by
  unfold Backends.lowerRuntimeContractNative
  simp only [Compiler.emitYul, Compiler.CodegenCommon.emitYul,
    Compiler.CodegenCommon.runtimeCode, hMapping, hInternals, hNoFallback,
    hNoReceive, if_true]
  simp only [List.singleton_append, List.append_nil]
  simp only [Compiler.CodegenCommon.mappingSlotFuncAt]
  rw [Backends.lowerRuntimeContractNativeAux_funcDef_cons_empty_of_lowerFunctionDefinition
    (definition := nativeMappingSlotFunctionDefinition)]
  · rw [lowerRuntimeContractNativeAux_nonFunc_eq_lowerStmtsNativeWithSwitchIds]
    · cases hLower :
        Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames
          [YulStmt.funcDef "mappingSlot" ["baseSlot", "key"] ["slot"]
              [YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "key"]),
                YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, YulExpr.ident "baseSlot"]),
                YulStmt.assign "slot" (YulExpr.call "keccak256" [YulExpr.lit 0, YulExpr.lit 64])],
            Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch contract.functions none none])
        0 [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch contract.functions none none] with
      | error err =>
          simp [hLower, Functor.map, Except.map, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
      | ok pair =>
          cases pair
          simp [hLower, Functor.map, Except.map, Bind.bind, Except.bind,
            Pure.pure, Except.pure]
    · intro stmt hmem name params rets body h
      simp only [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with hInit | hSwitch
      · subst hInit
        simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h
      · rcases hSwitch with hSwitch | hNil
        · subst hSwitch
          simp [Compiler.CodegenCommon.buildSwitch] at h
        · cases hNil
  · exact lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero_body _

/-- If mapping-helper emitted runtime lowering succeeds, the successful
contract is exactly the native dispatcher shell plus the generated native
`mappingSlot` helper. -/
theorem lowerRuntimeContractNative_emitYul_mapping_ok_dispatcher_reserved
    (contract : IRContract)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hMapping : contract.usesMapping = true)
    (hInternals : contract.internalFunctions = [])
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hLower :
      Backends.lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
        .ok nativeContract) :
    ∃ (dispatcher : List EvmYul.Yul.Ast.Stmt) (nextSwitchId : Nat),
      Backends.lowerStmtsNativeWithSwitchIds
          (Backends.yulStmtsIdentifierNames
            (Compiler.emitYul contract).runtimeCode)
          0 [Compiler.CodegenCommon.initFreeMemoryPointer,
            Compiler.CodegenCommon.buildSwitch contract.functions none none] =
        .ok (dispatcher, nextSwitchId) ∧
      nativeContract =
        { dispatcher := .Block dispatcher
          functions := ((∅ : Backends.NativeFunctionMap).insert
            "mappingSlot" nativeMappingSlotFunctionDefinition) } := by
  rw [lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved
    contract hMapping hInternals hNoFallback hNoReceive] at hLower
  cases hDispatcher :
      Backends.lowerStmtsNativeWithSwitchIds
        (Backends.yulStmtsIdentifierNames (Compiler.emitYul contract).runtimeCode)
        0 [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch contract.functions none none] with
  | ok pair =>
      rcases pair with ⟨dispatcher, nextSwitchId⟩
      rw [hDispatcher] at hLower
      simp only [Except.ok.injEq] at hLower
      exact ⟨dispatcher, nextSwitchId, rfl, hLower.symm⟩
  | error err =>
      rw [hDispatcher] at hLower
      simp at hLower

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_append
    (left right : List YulStmt)
    (hLeft : generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs left = true)
    (hRight : generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs right = true) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs (left ++ right) = true := by
  induction left with
  | nil => simpa using hRight
  | cons stmt rest ih =>
      cases stmt <;> simp at hLeft ⊢ <;> try exact ih hLeft
      case funcDef name params rets body =>
        exact ⟨hLeft.1, ih hLeft.2⟩

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_internalFunctions
    (internals : List YulStmt)
    (hBodies : ∀ name params rets body,
      YulStmt.funcDef name params rets body ∈ internals →
        yulStmtsContainFuncDef body = false) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs internals = true := by
  induction internals with
  | nil => rfl
  | cons stmt rest ih =>
      have hRest : ∀ name params rets body,
          YulStmt.funcDef name params rets body ∈ rest →
            yulStmtsContainFuncDef body = false := by
        intro name params rets body hmem
        exact hBodies name params rets body (by simp [hmem])
      cases stmt <;> simp [ih hRest]
      case funcDef name params rets body =>
        exact hBodies name params rets body (by simp)

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
      [Compiler.CodegenCommon.buildSwitch funcs fallback receive] = true := by
  have hNoFunc : ∀ name params rets body,
      Compiler.CodegenCommon.buildSwitch funcs fallback receive ≠
        YulStmt.funcDef name params rets body := by
    intro name params rets body h
    cases fallback <;> cases receive <;>
      simp [Compiler.CodegenCommon.buildSwitch] at h
  rw [generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_nonFunc_cons
    (Compiler.CodegenCommon.buildSwitch funcs fallback receive) [] hNoFunc]
  rfl

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_initFreeMemoryPointer_buildSwitch
    (funcs : List IRFunction)
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
      [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch funcs fallback receive] = true := by
  rw [generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_nonFunc_cons]
  · exact generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_buildSwitch
      funcs fallback receive
  · intro name params rets body h
    simp [Compiler.CodegenCommon.initFreeMemoryPointer] at h

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_runtimeCode
    (contract : IRContract)
    (hInternalBodies : ∀ name params rets body,
      YulStmt.funcDef name params rets body ∈ contract.internalFunctions →
        yulStmtsContainFuncDef body = false) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
      (Compiler.runtimeCode contract) = true := by
  let mapping := if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []
  have hMapping :
      generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs mapping = true := by
    by_cases hUsesMapping : contract.usesMapping
    · simp [mapping, hUsesMapping, generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs,
        Compiler.mappingSlotFuncAt, Compiler.CodegenCommon.mappingSlotFuncAt,
        yulFunctionBodies, yulStmtContainsFuncDef, yulStmtsContainFuncDef]
    · simp [mapping, hUsesMapping, generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs]
  have hInternals :
      generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
        contract.internalFunctions = true :=
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_internalFunctions
      contract.internalFunctions hInternalBodies
  have hSwitch :
      generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
        [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch contract.functions
          contract.fallbackEntrypoint contract.receiveEntrypoint] = true :=
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_initFreeMemoryPointer_buildSwitch
      contract.functions contract.fallbackEntrypoint contract.receiveEntrypoint
  rw [Compiler.runtimeCode, Compiler.CodegenCommon.runtimeCode]
  change generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
      (mapping ++ contract.internalFunctions ++
        [Compiler.CodegenCommon.initFreeMemoryPointer,
          Compiler.CodegenCommon.buildSwitch contract.functions
          contract.fallbackEntrypoint contract.receiveEntrypoint]) = true
  rw [List.append_assoc]
  exact generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_append
    mapping (contract.internalFunctions ++
      [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch contract.functions
        contract.fallbackEntrypoint contract.receiveEntrypoint])
    hMapping
    (generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_append
      contract.internalFunctions
      [Compiler.CodegenCommon.initFreeMemoryPointer,
        Compiler.CodegenCommon.buildSwitch contract.functions
        contract.fallbackEntrypoint contract.receiveEntrypoint]
      hInternals hSwitch)

theorem generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_emitYul_runtimeCode
    (contract : IRContract)
    (hInternalBodies : ∀ name params rets body,
      YulStmt.funcDef name params rets body ∈ contract.internalFunctions →
        yulStmtsContainFuncDef body = false) :
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
      (Compiler.emitYul contract).runtimeCode = true := by
  simpa [Compiler.emitYul, Compiler.CodegenCommon.emitYul] using
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_runtimeCode
      contract hInternalBodies

/-- Executable characterization for the generated runtime shape that the
    native EVMYulLean lowering path currently accepts: top-level `funcDef`
    statements are helpers, dispatcher statements contain no nested function
    definitions, helper names are unique, and helper bodies themselves contain
    no nested function definitions. -/
def generatedRuntimeNativeFragment (runtimeCode : List YulStmt) : Bool :=
  generatedRuntimeFunctionNamesUnique runtimeCode &&
    generatedRuntimeDispatcherHasNoFuncDefs runtimeCode &&
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs runtimeCode

theorem generatedRuntimeNativeFragment_emitYul_runtimeCode_noFallback_noReceive
    (contract : IRContract)
    (hPrefixUnique : generatedRuntimeFunctionNamesUnique
      ((if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions) = true)
    (hInternals : ∀ stmt, stmt ∈ contract.internalFunctions →
      ∃ name params rets body, stmt = YulStmt.funcDef name params rets body)
    (hExternalBodies : ∀ fn, fn ∈ contract.functions →
      yulStmtsContainFuncDef fn.body = false)
    (hInternalBodies : ∀ name params rets body,
      YulStmt.funcDef name params rets body ∈ contract.internalFunctions →
        yulStmtsContainFuncDef body = false)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none) :
    generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = true := by
  have hNames := generatedRuntimeFunctionNamesUnique_emitYul_runtimeCode
    contract hPrefixUnique
  have hDispatcher :=
    generatedRuntimeDispatcherHasNoFuncDefs_emitYul_runtimeCode_noFallback_noReceive
      contract hInternals hExternalBodies hNoFallback hNoReceive
  have hBodies := generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs_emitYul_runtimeCode
    contract hInternalBodies
  simp [generatedRuntimeNativeFragment, hNames, hDispatcher, hBodies]

def unsupportedGeneratedRuntimeNativeFragmentError : NativeLoweringError :=
  "native EVMYulLean generated runtime fragment check failed"

def validateGeneratedRuntimeNativeFragment
    (runtimeCode : List YulStmt) :
    Except NativeLoweringError Unit :=
  if generatedRuntimeNativeFragment runtimeCode then
    .ok ()
  else
    .error unsupportedGeneratedRuntimeNativeFragmentError

@[simp] theorem validateGeneratedRuntimeNativeFragment_ok
    (runtimeCode : List YulStmt)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true) :
    validateGeneratedRuntimeNativeFragment runtimeCode = .ok () := by
  simp [validateGeneratedRuntimeNativeFragment, hFragment]

@[simp] theorem validateGeneratedRuntimeNativeFragment_error
    (runtimeCode : List YulStmt)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = false) :
    validateGeneratedRuntimeNativeFragment runtimeCode =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  simp [validateGeneratedRuntimeNativeFragment, hFragment]

def selectorExprMatchesGeneratedDispatcher : YulExpr → Bool
  | .call "shr" [.lit shift, .call "calldataload" [.lit 0]] =>
      shift == Compiler.Constants.selectorShift
  | _ => false

@[simp] theorem selectorExprMatchesGeneratedDispatcher_selectorExpr :
    selectorExprMatchesGeneratedDispatcher
      Compiler.Proofs.YulGeneration.selectorExpr = true := by
  simp [selectorExprMatchesGeneratedDispatcher,
    Compiler.Proofs.YulGeneration.selectorExpr]

def selectedSwitchBody
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt)) :
    List YulStmt :=
  match cases.find? (fun entry => entry.1 == selector) with
  | some (_, body) => body
  | none => defaultBody.getD []

@[simp] theorem selectedSwitchBody_hit
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt))
    (body : List YulStmt)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (selector, body)) :
    selectedSwitchBody selector cases defaultBody = body := by
  unfold selectedSwitchBody
  rw [hFind]

@[simp] theorem selectedSwitchBody_miss
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt))
    (hFind : cases.find? (fun entry => entry.1 == selector) = none) :
    selectedSwitchBody selector cases defaultBody = defaultBody.getD [] := by
  unfold selectedSwitchBody
  rw [hFind]

def nativeDispatchSelector (tx : YulTransaction) : Nat :=
  tx.functionSelector % Compiler.Constants.selectorModulus

@[simp] theorem nativeDispatchSelector_of_selector_lt
    (tx : YulTransaction)
    (hSelector : tx.functionSelector < Compiler.Constants.selectorModulus) :
    nativeDispatchSelector tx = tx.functionSelector := by
  simp [nativeDispatchSelector, Nat.mod_eq_of_lt hSelector]

partial def yulStmtsUseBuiltinWithCalledFunctions
    (fuel : Nat)
    (builtin : String)
    (functionBodies : List (String × List YulStmt))
    (stmts : List YulStmt) :
    Bool :=
  yulStmtsUseBuiltinExceptFunctions builtin (functionBodies.map Prod.fst) stmts ||
    match fuel with
    | 0 => false
    | fuel' + 1 =>
        (yulStmtsCalledFunctions stmts).any fun name =>
          match functionBodies.find? (fun entry => entry.1 == name) with
          | some (_, body) =>
              yulStmtsUseBuiltinWithCalledFunctions fuel' builtin functionBodies body
          | none => false

mutual
  partial def yulStmtUsesBuiltinOnNativeRuntimePath
      (builtin : String)
      (selector : Nat)
      (functionBodies : List (String × List YulStmt)) :
      YulStmt → Bool
    | .funcDef _ _ _ _ => false
    | .block [
        .let_ "__has_selector" _,
        .if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) _,
        .if_ (YulExpr.ident "__has_selector") [
          .switch discr cases defaultBody
        ]
      ] =>
        if selectorExprMatchesGeneratedDispatcher discr then
          yulExprUsesBuiltinExceptFunctions builtin (functionBodies.map Prod.fst) discr ||
            yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
              builtin functionBodies (selectedSwitchBody selector cases defaultBody)
        else
          yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
            builtin functionBodies [
              .block [
                .let_ "__has_selector" (.lit 0),
                .if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) [],
                .if_ (YulExpr.ident "__has_selector") [
                  .switch discr cases defaultBody
                ]
              ]
            ]
    | .block stmts =>
        yulStmtsUseBuiltinOnNativeRuntimePath builtin selector functionBodies stmts
    | stmt =>
        yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
          builtin functionBodies [stmt]

  partial def yulStmtsUseBuiltinOnNativeRuntimePath
      (builtin : String)
      (selector : Nat)
      (functionBodies : List (String × List YulStmt))
      (stmts : List YulStmt) :
      Bool :=
    stmts.any (yulStmtUsesBuiltinOnNativeRuntimePath builtin selector functionBodies)
end

def nativeRuntimePathUsesBuiltin
    (builtin : String)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  yulStmtsUseBuiltinOnNativeRuntimePath builtin (nativeDispatchSelector tx)
    (yulFunctionBodies runtimeCode) runtimeCode

def unsupportedNativeHeaderBuiltinNames : List String :=
  ["coinbase", "difficulty", "prevrandao", "gaslimit", "basefee", "gasprice",
   "selfbalance"]

def nativeRuntimePathUsesAnyBuiltin
    (builtins : List String)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  builtins.any fun builtin => nativeRuntimePathUsesBuiltin builtin runtimeCode tx

def nativeRuntimePathUsesUnsupportedHeaderBuiltin
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  nativeRuntimePathUsesAnyBuiltin unsupportedNativeHeaderBuiltinNames runtimeCode tx

def nativeBlobBaseFeeRepresentable (fee : Nat) : Bool :=
  fee == EvmYul.MIN_BASE_FEE_PER_BLOB_GAS

def nativeChainIdRepresentable (chainId : Nat) : Bool :=
  chainId == EvmYul.chainId

def unsupportedNativeBlobBaseFeeError : NativeLoweringError :=
  "native EVMYulLean blobbasefee requires representable blobBaseFee; \
  current bridge supports only EVMYulLean minimum blob gas price"

def unsupportedNativeChainIdError : NativeLoweringError :=
  "native EVMYulLean chainid requires representable chainId; \
  current bridge supports only EVMYulLean global chain id"

def unsupportedNativeHeaderBuiltinError : NativeLoweringError :=
  "native EVMYulLean selected runtime path uses a header/account builtin that \
  is not represented in Verity's YulTransaction bridge"

def validateNativeRuntimeEnvironment
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Except NativeLoweringError Unit :=
  if nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx &&
      !nativeChainIdRepresentable tx.chainId then
    .error unsupportedNativeChainIdError
  else if nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx &&
      !nativeBlobBaseFeeRepresentable tx.blobBaseFee then
    .error unsupportedNativeBlobBaseFeeError
  else if nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx then
    .error unsupportedNativeHeaderBuiltinError
  else
    .ok ()

@[simp] theorem nativeChainIdRepresentable_global :
    nativeChainIdRepresentable EvmYul.chainId = true := by
  simp [nativeChainIdRepresentable]

@[simp] theorem nativeBlobBaseFeeRepresentable_minimum :
    nativeBlobBaseFeeRepresentable EvmYul.MIN_BASE_FEE_PER_BLOB_GAS = true := by
  simp [nativeBlobBaseFeeRepresentable]

@[simp] theorem validateNativeRuntimeEnvironment_noChainId_noBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hNoBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = false)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hNoBlobBaseFee, hNoHeader]

@[simp] theorem validateNativeRuntimeEnvironment_representableBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hBlobBaseFee, hNoHeader]

@[simp] theorem validateNativeRuntimeEnvironment_representableEnvironment
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hChainId : nativeChainIdRepresentable tx.chainId = true)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hChainId, hBlobBaseFee, hNoHeader]

@[simp] theorem validateNativeRuntimeEnvironment_ofIR_representableEnvironment
    (runtimeCode : List YulStmt)
    (tx : IRTransaction)
    (hChainId : nativeChainIdRepresentable tx.chainId = true)
    (hBlobBaseFee : nativeBlobBaseFeeRepresentable tx.blobBaseFee = true)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode
        (YulTransaction.ofIR tx) = false) :
    validateNativeRuntimeEnvironment runtimeCode (YulTransaction.ofIR tx) =
      .ok () := by
  simpa [YulTransaction.ofIR] using
    validateNativeRuntimeEnvironment_representableEnvironment
      runtimeCode (YulTransaction.ofIR tx) hChainId hBlobBaseFee hNoHeader

@[simp] theorem validateNativeRuntimeEnvironment_ofIR_globalDefaults
    (runtimeCode : List YulStmt)
    (tx : IRTransaction)
    (hChainId : tx.chainId = EvmYul.chainId)
    (hBlobBaseFee : tx.blobBaseFee = EvmYul.MIN_BASE_FEE_PER_BLOB_GAS)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode
        (YulTransaction.ofIR tx) = false) :
    validateNativeRuntimeEnvironment runtimeCode (YulTransaction.ofIR tx) =
      .ok () := by
  simpa [YulTransaction.ofIR, hChainId, hBlobBaseFee] using
    validateNativeRuntimeEnvironment_ofIR_representableEnvironment
      runtimeCode tx (by simp [hChainId]) (by simp [hBlobBaseFee]) hNoHeader

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedChainId
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hUsesChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = true)
    (hChainId : nativeChainIdRepresentable tx.chainId = false) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeChainIdError := by
  simp [validateNativeRuntimeEnvironment, hUsesChainId, hChainId]

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hUsesBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = true)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = false) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeBlobBaseFeeError := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hUsesBlobBaseFee, hBlobBaseFee]

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedHeaderBuiltin
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hNoBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = false)
    (hUsesHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = true) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeHeaderBuiltinError := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hNoBlobBaseFee, hUsesHeader]

@[simp] theorem initialState_installsExecutionContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.code =
      contract ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.perm =
      true := by
  simp [initialState, EvmYul.Yul.State.sharedState]

@[simp] theorem initialState_installsCurrentAccountContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    ((initialState contract tx storage observableSlots).sharedState.accountMap.find?
        (natToAddress tx.thisAddress)).map (fun account => account.code) =
      some contract := by
  simp only [initialState, EvmYul.Yul.State.sharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  split <;> simp

@[simp] theorem initialState_transactionEnvironment
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.source =
      natToAddress tx.sender ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.sender =
      natToAddress tx.sender ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.codeOwner =
      natToAddress tx.thisAddress ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.timestamp =
      tx.blockTimestamp ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.number =
      tx.blockNumber ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata =
      calldataToByteArray tx.functionSelector tx.args := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_source
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.source =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_sender
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.sender =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_codeOwner
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.codeOwner =
      natToAddress tx.thisAddress := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_weiValue
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockTimestamp
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.timestamp =
      tx.blockTimestamp := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockNumber
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.number =
      tx.blockNumber := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldata
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata =
      calldataToByteArray tx.functionSelector tx.args := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldataSize
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    calldataToByteArray_size]

end Compiler.Proofs.YulGeneration.Backends.Native
