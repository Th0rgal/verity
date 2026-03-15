import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ScopeValidation
import Compiler.CompilationModel.ValidationCalls
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Scope seen by the tail after compiling a single statement. This matches the
statement-list compiler's `collectStmtNames` update. -/
def stmtNextScope (scope : List String) (stmt : Stmt) : List String :=
  collectStmtNames stmt ++ scope

/-- Source names visible to generic statement proofs must stay out of the
compiler-reserved `__` namespace used by scratch temporaries. -/
def scopeAvoidsReservedCompilerPrefix (scope : List String) : Prop :=
  ∀ name ∈ scope, ¬ name.startsWith "__"

/-- Single-step result relation used by the generic statement induction library.
Unlike `stmtResultMatchesIRExecExact`, this tracks the tail scope instead of
requiring exact bindings for every name in the runtime map. -/
def stmtStepMatchesIRExec
    (fields : List Field)
    (nextScope : List String) :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .stop runtime, .stop state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

/-- Helper-aware compiled-side counterpart of `stmtStepMatchesIRExec`. `leave`
is not accepted at the external statement-list boundary. -/
def stmtStepMatchesIRExecWithInternals
    (fields : List Field)
    (nextScope : List String) :
    SourceSemantics.StmtResult → IRExecResultWithInternals → Prop
  | .continue runtime, .continue state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .stop runtime, .stop state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

/-- Helper-aware compiled-side counterpart of
`FunctionBody.stmtResultMatchesIRExec`. `leave` is not accepted at the external
body boundary. -/
def stmtResultMatchesIRExecWithInternals
    (fields : List Field)
    (sourceResult : SourceSemantics.StmtResult) :
    IRExecResultWithInternals → Prop
  | .continue state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.continue state)
  | .return value state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.return value state)
  | .stop state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.stop state)
  | .revert state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.revert state)
  | .leave _ => False

/-- A compiled statement head that preserves the exact-state invariant needed to
continue generic statement-list induction on the remaining tail. -/
structure CompiledStmtStep
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
        execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- Helper-aware single-step result relation for the future generic statement
induction path. The post-state shape is unchanged; only the source-side head step
is evaluated in the helper-aware semantics family. -/
structure CompiledStmtStepWithHelpers
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (helperFuel : Nat)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = sourceResult ∧
        execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- Exact helper-aware single-step interface for future helper-rich proofs: both
the source head step and the compiled head step run in the helper-aware
semantics families. This is the statement-level target needed for helper-rich
bodies because internal-call compilation can emit Yul forms such as `letMany`
that legacy `execIRStmts` rejects. -/
structure CompiledStmtStepWithHelpersAndHelperIR
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (helperFuel : Nat)
      (extraFuel : Nat),
      0 < helperFuel →
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = sourceResult ∧
        execIRStmtsWithInternals runtimeContract
          (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExecWithInternals
          fields (stmtNextScope scope stmt) sourceResult irExec

/-- Any legacy generic statement-step proof remains valid for the helper-aware
source semantics as long as the statement itself is helper-surface closed. This
lets the existing helper-free library discharge the unchanged cases while the
remaining work focuses only on genuinely helper-using statements. -/
theorem CompiledStmtStep.withHelpers_of_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStep fields scope stmt compiledIR)
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    CompiledStmtStepWithHelpers spec fields scope stmt compiledIR := by
      sorry
/-- Statement lists whose heads all admit a generic compiled-step proof. -/
inductive StmtListGenericCore (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericCore fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStep fields scope stmt compiledIR →
      StmtListGenericCore fields (stmtNextScope scope stmt) rest →
      StmtListGenericCore fields scope (stmt :: rest)

/-- Weaker source-side reuse witness for the future helper-rich induction path:
only helper-surface-closed heads must come with the existing helper-free
generic step proof. Helper-surface-positive heads can instead be discharged by a
dedicated exact helper-aware step proof at the point where the exact seam is
assembled. -/
inductive StmtListHelperFreeStepInterface
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeStepInterface fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∃ compiledIR,
          CompiledStmtStep fields scope stmt compiledIR) →
      StmtListHelperFreeStepInterface fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeStepInterface fields scope (stmt :: rest)

/-- Statement lists whose heads all admit a helper-aware generic compiled-step
proof. This is the exact induction-level seam needed to consume helper-summary
soundness and decreasing-rank evidence without reusing the helper-free
`SupportedStmtList` witness. -/
inductive StmtListGenericWithHelpers
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericWithHelpers spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStepWithHelpers spec fields scope stmt compiledIR →
      StmtListGenericWithHelpers spec fields (stmtNextScope scope stmt) rest →
      StmtListGenericWithHelpers spec fields scope (stmt :: rest)

/-- Exact helper-aware statement-list induction seam: both source execution and
compiled execution already target the helper-aware semantics. This is the list
level interface needed once helper-rich statements enter the theorem domain. -/
inductive StmtListGenericWithHelpersAndHelperIR
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope stmt compiledIR →
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope (stmt :: rest)

/-- Compiled-side compatibility witness for lifting existing helper-free generic
statement proofs into the exact helper-aware compiled induction seam. This
records that each compiled head stays inside the already-closed
legacy-compatible external Yul subset, without coupling the witness to any
particular statement-step proof object. -/
inductive StmtListCompiledLegacyCompatible
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListCompiledLegacyCompatible fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (∀ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
          Except.ok compiledIR →
          LegacyCompatibleExternalStmtList compiledIR) →
      StmtListCompiledLegacyCompatible fields (stmtNextScope scope stmt) rest →
      StmtListCompiledLegacyCompatible fields scope (stmt :: rest)

/-- Weaker compiled-side compatibility witness for the exact helper-aware
induction seam: only helper-surface-closed statement heads must stay inside the
legacy-compatible external Yul subset. Helper-positive heads can instead be
discharged by dedicated exact helper-aware step proofs. -/
inductive StmtListHelperFreeCompiledLegacyCompatible
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeCompiledLegacyCompatible fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∀ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
            Except.ok compiledIR →
            LegacyCompatibleExternalStmtList compiledIR) →
      StmtListHelperFreeCompiledLegacyCompatible fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeCompiledLegacyCompatible fields scope (stmt :: rest)

/-- Disjoint-based compiled-side compatibility: helper-surface-closed statement
heads produce compiled IR that is disjoint from the runtime contract's internal
function table.  Unlike `StmtListHelperFreeCompiledLegacyCompatible` this does
**not** require `runtimeContract.internalFunctions = []` downstream. -/
inductive StmtListHelperFreeCompiledCallsDisjoint
    (runtimeContract : IRContract)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∀ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope stmt =
            Except.ok compiledIR →
            YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR) →
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope (stmt :: rest)

/-- List-local exact step interface for the genuinely new helper-surface
statement heads. Helper-free heads remain reusable through the existing
helper-free generic step library plus the helper-free compiled compatibility
witness. -/
inductive StmtListHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for heads that genuinely execute internal helpers under
the helper-aware semantics. This is the new proof work that should consume
helper-summary/rank evidence. -/
inductive StmtListInternalHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListInternalHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for direct statement-position internal-helper heads.
These are the cases that should consume the statement-level helper-summary
soundness lemmas from `SourceSemantics.lean` directly. -/
inductive StmtListDirectInternalHelperCallStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperCallSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for direct statement-position helper-return binding
heads. These are the cases that should consume the `Stmt.internalCallAssign`
summary shape directly instead of sharing one bucket with void helper calls. -/
inductive StmtListDirectInternalHelperAssignStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperAssignSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Coarser direct statement-position helper interface retained as the assembly
point for the two direct helper proof shapes above. -/
inductive StmtListDirectInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for heads whose internal-helper work appears only in
expression position at the current statement head. These are the cases that
should consume the expression-level summary-soundness/world-preservation lemmas
directly. -/
inductive StmtListExprInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesExprInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListExprInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for structural heads whose helper burden is recursive
transport through nested bodies (`ite` / `forEach`) rather than direct helper
summary consumption at the head itself. -/
inductive StmtListStructuralInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesStructuralInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListStructuralInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Residual exact-step interface for heads that still fall on the coarse old
helper surface but do not actually execute internal helpers. Splitting these
out prevents future helper-summary work from having to discharge unrelated
non-helper proof gaps such as broader expression/core cases. -/
inductive StmtListResidualHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = true →
        stmtTouchesInternalHelperSurface stmt = false →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

private theorem legacyCompat_of_all_expr :
    ∀ (stmts : List YulStmt),
    (∀ s ∈ stmts, ∃ e, s = .expr e) →
    LegacyCompatibleExternalStmtList stmts
  | [], _ => .nil
  | s :: rest, h => by
    obtain ⟨e, rfl⟩ := h s (List.mem_cons_self ..)
    exact .expr e rest (legacyCompat_of_all_expr rest
      (fun s hs => h s (List.mem_cons_of_mem _ hs)))

private theorem revertWithMessage_all_expr (message : String) :
    ∀ s ∈ revertWithMessage message, ∃ e, s = .expr e := by
  intro s hs
  unfold revertWithMessage at hs
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, List.mem_map,
             Prod.exists] at hs
  aesop

private theorem legacyCompatibleExternalStmtList_revertWithMessage
    (message : String) :
    LegacyCompatibleExternalStmtList (revertWithMessage message) :=
  legacyCompat_of_all_expr _ (revertWithMessage_all_expr message)

/-- The current helper-free compiled theorem target already accepts the scalar
storage write emitted by `compileSetStorage` when packed-field writes are
excluded. -/
theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.letVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  simp [compileStmt, bind, Except.bind, pure, Except.pure] at hcompile
  split at hcompile
  · exact absurd hcompile (by exact nofun)
  · cases hcompile; exact .let_ _ _ [] .nil
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar
    {fields : List Field}
    {inScopeNames : List String}
    {name : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.assignVar name value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  simp [compileStmt, bind, Except.bind, pure, Except.pure] at hcompile
  split at hcompile
  · exact absurd hcompile (by exact nofun)
  · cases hcompile; exact .assign _ _ [] .nil
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_require
    {fields : List Field}
    {inScopeNames : List String}
    {cond : Expr}
    {message : String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.require cond message) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  simp [compileStmt, bind, Except.bind, pure, Except.pure] at hcompile
  split at hcompile
  · exact absurd hcompile (by exact nofun)
  · cases hcompile
    exact .if_ _ _ [] (legacyCompatibleExternalStmtList_revertWithMessage message) .nil
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_return
    {fields : List Field}
    {inScopeNames : List String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.return value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  simp [compileStmt, bind, Except.bind, pure, Except.pure] at hcompile
  split at hcompile
  · exact absurd hcompile (by exact nofun)
  · cases hcompile; exact .expr _ _ (.expr _ [] .nil)
private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
    {fields : List Field}
    {inScopeNames : List String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames .stop =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  simp [compileStmt, pure, Except.pure] at hcompile
  subst hcompile; exact .expr _ [] .nil
/-- On the current supported contract surface, successful single-statement
compilation stays inside the legacy helper-free external Yul subset. This is
the compiled-side compatibility fact needed to reuse already-proved helper-free
cases inside the exact helper-aware compiled seam. -/
theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
/-- On the current supported contract surface, successful statement-list
compilation stays inside the legacy helper-free external Yul subset. -/
theorem legacyCompatibleExternalStmtList_of_compileStmtList_ok_on_supportedContractSurface
    {fields : List Field}
    {inScopeNames : List String}
    {stmts : List Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
/-- Derive the compiled-side legacy-compatibility witness needed by the exact
helper-aware induction seam from the existing supported contract-surface scan. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
      sorry
/-- Any list-level compiled witness for full legacy compatibility also suffices
for the weaker exact-seam witness that only constrains helper-free heads. -/
theorem stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts := by
  induction hlegacy with
  | nil => exact .nil
  | cons hcomp _ ih => exact .cons (fun _ => hcomp) ih
/-- The current supported contract surface already implies the weaker exact-seam
compiled disjointness witness whenever the runtime contract has no internal
helper table. This lets the active exact helper-aware wrapper target the
generalized calls-disjoint bridge directly instead of routing through the older
helper-free legacy-compatibility witness. -/
theorem stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface
    {runtimeContract : IRContract}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_exprMap
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_letBindings
    (bindings : List (String × YulExpr))
    (rest : List YulStmt)
    (hrest : LegacyCompatibleExternalStmtList rest) :
    LegacyCompatibleExternalStmtList
      (bindings.map (fun binding => YulStmt.let_ binding.1 binding.2) ++ rest) := by
        sorry
private theorem legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok
    {fields : List Field}
    {field : String}
    {keyExpr valueExpr : YulExpr}
    {label : String}
    {wordOffset : Nat}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileMappingSlotWrite fields field keyExpr valueExpr label wordOffset =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
private theorem legacyCompatibleExternalStmtList_of_compileSetMapping2_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2 fields dynamicSource field key1 key2 value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
/-- On the Tier 2 alternate contract surface, successful single-statement
compilation still stays inside the legacy helper-free external Yul subset. This
extends the exact helper-aware compiled seam to the already-proved singleton
mapping-write fragment instead of forcing it back onto the stricter default
surface. -/
theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {inScopeNames : List String}
    {stmt : Stmt}
    {bodyIR : List YulStmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false)
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames stmt = Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
      sorry
/-- Tier 2 list-level legacy-compatibility witness for the alternate singleton
mapping-write surface. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
      sorry
/-- Tier 2 exact-seam helper-free compiled compatibility witness. -/
theorem stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts :=
  stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible
    (stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoPacked
      hsurface)

/-- Tier 2 exact-seam compiled disjointness witness for the alternate singleton
mapping-write surface when the runtime contract has no internal helper table. -/
theorem stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface_exceptMappingWrites
    {runtimeContract : IRContract}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by
      sorry
/-- Any full helper-free generic statement-list proof also gives the weaker
source-side reuse witness needed by the future helper-rich exact seam: only the
helper-free heads retain the old generic-step obligation. -/
theorem stmtListHelperFreeStepInterface_of_core
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts) :
    StmtListHelperFreeStepInterface fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists satisfy the exact helper-surface step
interface vacuously: no head ever needs a genuinely new helper-aware step
proof. -/
theorem stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the narrower exact
internal-helper step interface vacuously. -/
theorem stmtListInternalHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the direct
statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the direct helper-return
binding interface vacuously. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble the coarser direct helper interface from the two source-summary
shapes it still contains: void helper statements and helper-return bindings. -/
theorem stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts) :
    StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the direct
statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the expression-position
internal-helper interface vacuously. -/
theorem stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the structural
internal-helper interface vacuously. -/
theorem stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble the coarse internal-helper interface from the narrower proof-cut
interfaces that match the actual proof obligations: direct helper statements,
expression-position helper calls, and recursive structural transport. -/
theorem stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts) :
    StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Helper-surface-closed statement lists also satisfy the residual non-helper
exact step interface vacuously. -/
theorem stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble the coarse exact helper-surface step interface from the split
interfaces: genuine internal-helper heads are proved through the narrow helper
surface interface, while the residual coarse-surface heads are discharged
separately. -/
theorem stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts) :
    StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Lift an existing helper-free generic statement-list proof into the
helper-aware induction world when the whole list is helper-surface closed. This
is the current fail-closed bridge from the legacy generic library to the new
helper-aware induction seam. -/
theorem stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
      sorry
/-- Lift the weaker helper-free step interface into the helper-aware generic
induction world when the whole list is helper-surface closed. This removes the
need to materialize a full legacy `StmtListGenericCore` witness at callers that
only target the helper-aware body theorem. -/
theorem stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
      sorry
/-- Any helper-aware generic statement-step proof already closes the exact
helper-aware compiled-side step goal when the compiled head stays inside the
legacy-compatible external Yul subset and the runtime contract has no internal
helper table. This is the compiled-side fail-closed bridge from the current
theorem domain to the exact helper-aware induction seam. -/
theorem CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hlegacy : LegacyCompatibleExternalStmtList compiledIR)
    (hinternal : runtimeContract.internalFunctions = []) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope stmt compiledIR := by
        sorry
/-- Disjoint-based bridge: any helper-aware generic statement-step proof closes
the exact helper-aware compiled-side step goal when the compiled IR is disjoint
from the internal function table.  Unlike `withHelperIR_of_legacyCompatible` this
does **not** require `runtimeContract.internalFunctions = []`. -/
theorem CompiledStmtStepWithHelpers.withHelperIR_of_callsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope stmt compiledIR := by
        sorry
/-- Lift helper-aware statement-list proofs into the exact helper-aware compiled
induction seam on the current legacy-compatible compiled subset. This isolates
future helper-summary work to the genuinely new helper-call cases: already
proved helper-free cases can be reused directly once callers supply the
compiled-side legacy-compatibility witness. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge that splits the remaining work cleanly:
helper-free heads still reuse the legacy generic step library plus the weaker
helper-free compiled compatibility witness, while helper-positive heads are
discharged only through a dedicated exact helper-aware step interface. -/
theorem
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Disjoint-based exact helper-aware list bridge: helper-free heads reuse the
legacy generic step library plus the new disjointness witness, while
helper-positive heads are discharged through the dedicated step interface.
Unlike the `_helperFreeCompiledLegacyCompatible` variant, this does **not**
require `runtimeContract.internalFunctions = []`. -/
theorem
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge with the helper-positive work split cleanly:
genuine internal-helper heads are supplied through a narrow helper-specific
interface, while residual coarse helper-surface heads are tracked separately so
future helper-summary proofs do not also inherit unrelated non-helper cases. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge over the fully split helper-positive
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are tracked separately, so future summary/rank proofs
can target the exact source-side obligation they discharge. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge over the fully split helper-positive
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are tracked separately, so future summary/rank proofs
can target the exact source-side obligation they discharge. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge that splits the remaining work cleanly:
helper-free heads still reuse the legacy generic step library plus the weaker
helper-free compiled compatibility witness, while helper-positive heads are
discharged only through a dedicated exact helper-aware step interface. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Disjoint-based exact helper-aware list bridge with `StmtListGenericCore`.
The legacy `StmtListGenericCore` witness is reused for helper-free heads, with
compiled-side disjointness replacing `internalFunctions = []`. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Exact helper-aware list bridge over the split helper-positive interfaces:
the legacy `StmtListGenericCore` witness is still reused for helper-free heads,
while genuine internal-helper heads and residual coarse helper-surface heads are
supplied separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Legacy-core exact helper-aware list bridge over the fully split
helper-positive interfaces. This keeps `StmtListGenericCore` reusable for
helper-free heads while future helper-rich work targets direct helper
statements, expression-position helper heads, and recursive structural heads
separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Legacy-core exact helper-aware list bridge over the fully split
helper-positive interfaces. This keeps `StmtListGenericCore` reusable for
helper-free heads while future helper-rich work targets direct helper
statements, expression-position helper heads, and recursive structural heads
separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Disjoint-based legacy-core exact helper-aware list bridge over the fully
split helper-positive interfaces.  Does **not** require
`runtimeContract.internalFunctions = []`. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- On helper-surface-closed statement lists, the disjoint-based bridge
collapses: no internal function table constraint at all is needed since every
head is helper-free and compiled-disjoint. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- On helper-surface-closed statement lists, the new exact helper-aware list
bridge collapses to the old helper-free lifting path, but only needs the weaker
helper-free compiled compatibility witness. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Combined fail-closed lifting bridge from the existing helper-free generic
statement library to the exact helper-aware compiled induction seam. The only
additional input beyond the already-proved helper-free cases is a
compiled-side legacy-compatibility witness for the statement list. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_compiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
      sorry
/-- Structural scope discipline for statement prefixes used to justify that the
generic induction scope only contains validated source identifiers. -/
inductive StmtListScopeDiscipline (fieldNames : List String) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListScopeDiscipline fieldNames scope []
  | letVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.letVar name value)) rest →
      StmtListScopeDiscipline fieldNames scope (.letVar name value :: rest)
  | assignVar {scope : List String} {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.assignVar name value)) rest →
      StmtListScopeDiscipline fieldNames scope (.assignVar name value :: rest)
  | require {scope : List String} {cond : Expr} {message : String} {rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.require cond message)) rest →
      StmtListScopeDiscipline fieldNames scope (.require cond message :: rest)
  | return_ {scope : List String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.return value)) rest →
      StmtListScopeDiscipline fieldNames scope (.return value :: rest)
  | stop {scope : List String} {rest : List Stmt} :
      StmtListScopeDiscipline fieldNames scope rest →
      StmtListScopeDiscipline fieldNames scope (.stop :: rest)
  | setStorage {scope : List String} {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.setStorage fieldName value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setStorage fieldName value :: rest)
  | setStorageAddr {scope : List String} {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.setStorageAddr fieldName value)) rest →
      StmtListScopeDiscipline fieldNames scope (.setStorageAddr fieldName value :: rest)
  | ite {scope : List String} {cond : Expr} {thenBranch elseBranch rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      FunctionBody.exprBoundNamesInScope cond scope →
      StmtListScopeDiscipline fieldNames scope thenBranch →
      StmtListScopeDiscipline fieldNames scope elseBranch →
      StmtListScopeDiscipline fieldNames (stmtNextScope scope (.ite cond thenBranch elseBranch)) rest →
      StmtListScopeDiscipline fieldNames scope (.ite cond thenBranch elseBranch :: rest)

/-- Syntax-side witness for the current generic statement fragment, before the
scope obligations are discharged from identifier validation. -/
inductive StmtListScopeCore (fieldNames : List String) : List Stmt → Prop where
  | nil :
      StmtListScopeCore fieldNames []
  | letVar {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.letVar name value :: rest)
  | assignVar {name : String} {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.assignVar name value :: rest)
  | require {cond : Expr} {message : String} {rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.require cond message :: rest)
  | return_ {value : Expr} {rest : List Stmt} :
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.return value :: rest)
  | stop {rest : List Stmt} :
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.stop :: rest)
  | setStorage {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setStorage fieldName value :: rest)
  | setStorageAddr {fieldName : String} {value : Expr} {rest : List Stmt} :
      fieldName ∈ fieldNames →
      FunctionBody.ExprCompileCore value →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.setStorageAddr fieldName value :: rest)
  | ite {cond : Expr} {thenBranch elseBranch rest : List Stmt} :
      FunctionBody.ExprCompileCore cond →
      StmtListScopeCore fieldNames thenBranch →
      StmtListScopeCore fieldNames elseBranch →
      StmtListScopeCore fieldNames rest →
      StmtListScopeCore fieldNames (.ite cond thenBranch elseBranch :: rest)

private theorem exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
    {expr : Expr}
    (hsurface : exprTouchesUnsupportedContractSurface expr = false) :
    FunctionBody.ExprCompileCore expr := by
      sorry
private theorem fieldName_mem_fields_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    fieldName ∈ fields.map (·.name) := by
      sorry
private theorem fieldName_mem_fields_of_compileSetStorage_ok
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {requireAddressField : Bool}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStorage
        fields
        .calldata
        fieldName
        value
        requireAddressField = Except.ok compiledIR) :
    fieldName ∈ fields.map (·.name) := by
      sorry
private theorem compileStmt_ite_ok_inv
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false scope (.ite cond thenBranch elseBranch) =
          Except.ok compiledIR) :
    ∃ condIR thenIR elseIR,
      CompilationModel.compileExpr fields .calldata cond = Except.ok condIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope thenBranch = Except.ok thenIR ∧
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope elseBranch = Except.ok elseIR := by
          sorry
theorem stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
    {fields : List Field}
    {scope : List String}
    {pfx suffix : List Stmt}
    {bodyIR : List YulStmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (pfx ++ suffix) = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope (pfx ++ suffix) =
          Except.ok bodyIR) :
    StmtListScopeCore (fields.map (·.name)) pfx := by
      sorry
private theorem stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
    {pfx suffix : List Stmt}
    {stmt : Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (pfx ++ stmt :: suffix) = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
      sorry
private theorem mem_stmtNextScope_of_mem_scope
    {scope : List String}
    {stmt : Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ stmtNextScope scope stmt :=
  List.mem_append.mpr <| Or.inr hmem

private theorem mem_stmtNextScopeList_of_mem_scope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ List.foldl stmtNextScope scope stmts := by
      sorry
private theorem exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
    {context : String}
    {params : List Param}
    {paramScope dynamicParams localScope scope : List String}
    {constructorArgCount : Option Nat}
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hvalidate :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams localScope constructorArgCount expr =
          Except.ok ())
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    FunctionBody.exprBoundNamesInScope expr scope := by
      sorry
private theorem stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
    {fieldNames : List String}
    {context : String}
    {params : List Param}
    {paramScope dynamicParams localScope scope : List String}
    {constructorArgCount : Option Nat}
    {stmts : List Stmt}
    {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams localScope constructorArgCount stmts =
          Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    StmtListScopeDiscipline fieldNames scope stmts := by
      sorry
theorem stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
    {spec : FunctionSpec}
    {fieldNames : List String}
    {pfx suffix : List Stmt}
    (hcore : StmtListScopeCore fieldNames pfx)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = pfx ++ suffix) :
    StmtListScopeDiscipline fieldNames (spec.params.map (·.name)) pfx := by
      sorry
private theorem scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
    {fieldNames : List String}
    {context : String}
    {params : List Param}
    {paramScope dynamicParams localScope scope : List String}
    {constructorArgCount : Option Nat}
    {stmts : List Stmt}
    {finalScope : List String}
    (hcore : StmtListScopeCore fieldNames stmts)
    (hvalidate :
      validateScopedStmtListIdentifiers
        context params paramScope dynamicParams localScope constructorArgCount stmts =
          Except.ok finalScope)
    (hparamsInScope : ∀ name, name ∈ paramScope → name ∈ scope)
    (hlocalsInScope : ∀ name, name ∈ localScope → name ∈ scope) :
    ∀ name, name ∈ finalScope → name ∈ List.foldl stmtNextScope scope stmts := by
      sorry
private theorem exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
    {spec : FunctionSpec}
    {fieldNames : List String}
    {pfx suffix : List Stmt}
    {fieldName : String}
    {value : Expr}
    (hprefixCore : StmtListScopeCore fieldNames pfx)
    (hvalueCore : FunctionBody.ExprCompileCore value)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = pfx ++ .setStorage fieldName value :: suffix) :
    FunctionBody.exprBoundNamesInScope
      value
      (List.foldl stmtNextScope (spec.params.map (·.name)) pfx) := by
        sorry
private theorem collectExprNames_mem_exprBoundNames_of_core
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by
      sorry
private theorem stmtListScopeDiscipline_scope_names
    {fieldNames : List String}
    {scope : List String}
    {stmts : List Stmt}
    (hdisc : StmtListScopeDiscipline fieldNames scope stmts) :
    ∀ name, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈
        (scope ++ collectStmtListBindNames stmts ++
          collectStmtListAssignedNames stmts ++ fieldNames) := by
            sorry
theorem compiledStmtStep_letVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.letVar name value) [YulStmt.let_ name valueIR] := by
      sorry
theorem compiledStmtStep_assignVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.assignVar name value) [YulStmt.assign name valueIR] := by
      sorry
theorem compiledStmtStep_require
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {failCond : YulExpr}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond) :
    CompiledStmtStep fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] := by
        sorry
theorem compiledStmtStep_return
    {fields : List Field}
    {scope : List String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.return value)
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] := by
        sorry
theorem compiledStmtStep_stop
    {fields : List Field}
    {scope : List String} :
    CompiledStmtStep fields scope .stop [YulStmt.expr (YulExpr.call "stop" [])] := by
      sorry
private theorem encodeStorageAt_writeUintSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ slot) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world [slot] value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeUintSlots_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slots : List Nat}
    {query value : Nat}
    (hnotMem : query ∉ slots) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world slots value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key query value : Nat}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {keys : List Nat}
    {query value : Nat}
    (hneq : query ≠ SourceSemantics.mappingSlotChain slot keys) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key + wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    {packed : PackedBits}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key + wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private def findResolvedFieldAtSlotCopy (fields : List Field) (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if resolvedSlot = slot || field.aliasSlots.contains slot then
          some field
        else
          go rest (idx + 1)
  go fields 0

private def findFieldWithResolvedSlotCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (Field × Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
      if field.name == name then
        some (field, field.slot.getD idx)
      else
        findFieldWithResolvedSlotCopyFrom rest (idx + 1) name

private def findFieldWriteSlotsCopyFrom
    (fields : List Field) (idx : Nat) (name : String) : Option (List Nat) :=
  match fields with
  | [] => none
  | field :: rest =>
      if field.name == name then
        some (field.slot.getD idx :: field.aliasSlots)
      else
        findFieldWriteSlotsCopyFrom rest (idx + 1) name

private def findResolvedFieldAtSlotCopyFrom
    (fields : List Field) (idx : Nat) (slot : Nat) : Option Field :=
  match fields with
  | [] => none
  | field :: rest =>
      let resolvedSlot := field.slot.getD idx
      if resolvedSlot = slot || field.aliasSlots.contains slot then
        some field
      else
        findResolvedFieldAtSlotCopyFrom rest (idx + 1) slot

private def fieldWriteEntriesAt
    (idx : Nat) (field : Field) : List (Nat × String × Option PackedBits) :=
  (field.slot.getD idx, field.name, field.packedBits) ::
    (field.aliasSlots.zipIdx.map (fun (slot, aliasIdx) =>
      (slot, s!"{field.name}.aliasSlots[{aliasIdx}]", field.packedBits)))

private def firstInFieldConflictCopy
    (seen : List (Nat × String × Option PackedBits))
    (current : List (Nat × String × Option PackedBits)) :
    Option (Nat × String × String) :=
  match current with
  | [] => none
  | (slot, ownerName, packed) :: tail =>
      match seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
      | some (_, prevName, _) => some (slot, prevName, ownerName)
      | none => firstInFieldConflictCopy ((slot, ownerName, packed) :: seen) tail

private def firstFieldWriteSlotConflictCopyFrom
    (seen : List (Nat × String × Option PackedBits))
    (idx : Nat) (fields : List Field) : Option (Nat × String × String) :=
  match fields with
  | [] => none
  | field :: rest =>
      let writeSlots := fieldWriteEntriesAt idx field
      match firstInFieldConflictCopy seen writeSlots with
      | some conflict => some conflict
      | none => firstFieldWriteSlotConflictCopyFrom (writeSlots.reverse ++ seen) (idx + 1) rest

private theorem list_findSlotPackedNone_ne_none
    {seen : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hmem : slot ∈ seen.map (fun entry => entry.1)) :
    (seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 none)) ≠ none := by
      sorry
private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hcurrent : slot ∈ current.map (fun entry => entry.1))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by
      sorry
private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    (hseen : targetSlot ∈ seen.map (fun entry => entry.1))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
      sorry
private theorem firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_singleton
    {seen : List (Nat × String × Option PackedBits)}
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hfind :
      findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite :
      findFieldWriteSlotsCopyFrom fields idx fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by
      sorry
private theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields targetSlot = some f := by
      sorry
private theorem findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwrite : findFieldWriteSlots fields fieldName = some [slot])
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopy fields slot = some f := by
      sorry
private def findDynamicArrayElementAtSlotCopy
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if Compiler.Proofs.solidityMappingSlot baseSlot idx = targetSlot then
          some value.val
        else
          scanElements baseSlot rest (idx + 1)
  let rec go (remaining : List Field) (idx : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        match field.ty with
        | .dynamicArray _ =>
            match scanElements resolvedSlot (world.storageArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

private def encodeStorageAtCopy
    (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlotCopy fields slot with
  | some field =>
      if SourceSemantics.fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else if SourceSemantics.fieldUsesDynamicArrayStorage field then
        (world.storageArray slot).length
      else
        (world.storage slot).val
  | none =>
      match findDynamicArrayElementAtSlotCopy fields world slot with
      | some value => value
      | none => (world.storage slot).val

private theorem encodeStorageAt_eq_copy
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat} :
    SourceSemantics.encodeStorageAt fields world slot =
      encodeStorageAtCopy fields world slot := by
        sorry
private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by
      sorry
private theorem encodeStorageAt_eq_storageAddr_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storageAddr slot).val := by
      sorry
private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot slot key) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (Compiler.Proofs.abstractMappingSlot slot key) = value := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {keys : List Nat}
    {value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (SourceSemantics.mappingSlotChain slot keys) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.mappingSlotChain slot keys) = value := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = value := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    {packed : PackedBits}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) =
      SourceSemantics.packedWordWrite
        (world.storage (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)).val
        value
        packed := by
          sorry
private theorem encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 query value : Nat}
    (hneq :
      query ≠ Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2) = value := by
          sorry
private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset query value : Nat}
    (hneq :
      query ≠ Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2 + wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
        sorry
private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2 + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2 + wordOffset) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2 + wordOffset) = value := by
          sorry
private def abstractStoreStorageOrMappingMany
    (storage : Nat → Nat) (slots : List Nat) (value : Nat) : Nat → Nat :=
  match slots with
  | [] => storage
  | slot :: rest =>
      abstractStoreStorageOrMappingMany
        (Compiler.Proofs.abstractStoreStorageOrMapping storage slot value)
        rest
        value

private theorem abstractStoreStorageOrMappingMany_eq
    {storage : Nat → Nat}
    {slots : List Nat}
    {value query : Nat} :
    abstractStoreStorageOrMappingMany storage slots value query =
      if slots.contains query then value else storage query := by
        sorry
private theorem runtimeStateMatchesIR_writeUintSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
            sorry
private theorem runtimeStateMatchesIR_writeAddressSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
            sorry
private theorem runtimeStateMatchesIR_writeUintSlots
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : ∀ slot ∈ slots, findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world slots value }
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
            sorry
private theorem runtimeStateMatchesIR_writeUintKeyedMappingSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
            sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot : Nat}
    {keys : List Nat}
    {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (SourceSemantics.mappingSlotChain slot keys) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainSlots
            runtime.world [slot] keys value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (SourceSemantics.mappingSlotChain slot keys)
            value } := by
              sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
            sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordSlots
            runtime.world [slot] key wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)
            value } := by
              sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key wordOffset value : Nat}
    {packed : PackedBits}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingPackedWordSlots
            runtime.world [slot] key wordOffset packed value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)
            (SourceSemantics.packedWordWrite
              (state.storage (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
              value
              packed) } := by
                sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key1 key2 value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2Slots runtime.world [slot] key1 key2 value }
      { state with
          storage :=
            Compiler.Proofs.abstractStoreMappingEntry
              (Compiler.Proofs.abstractStoreMappingEntry state.storage slot key1 0)
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2
              value } := by
                sorry
private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key1 key2 wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2 + wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2 + wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2WordSlots
            runtime.world [slot] key1 key2 wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2 + wordOffset)
            value } := by
              sorry
private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
            sorry
private theorem bindingsExactlyMatchIRVarsOnScope_writeMappingSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot key value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
            sorry
private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlots
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slots : List Nat}
    {value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
            sorry
private theorem execIRStmts_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (name : String)
    (value : Nat)
    (hvalue : IRState.getVar state name = value) :
    execIRStmts (slots.length + fuel + 1) state
      (slots.map (fun slot =>
        YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name]))) =
      .continue
        { state with
            storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
              sorry
private theorem execIRStmts_let_then_sstore_lit_ident_slots_continue
    (fuel : Nat)
    (state : IRState)
    (slots : List Nat)
    (tempName : String)
    (valueIR : YulExpr)
    (value : Nat)
    (hvalue : evalIRExpr state valueIR = some value) :
    execIRStmts (slots.length + fuel + 2) state
      (YulStmt.let_ tempName valueIR ::
        slots.map (fun slot =>
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident tempName]))) =
      .continue
        { state.setVar tempName value with
            storage :=
              abstractStoreStorageOrMappingMany
                (state.setVar tempName value).storage
                slots
                value } := by
                  sorry
private theorem execIRStmts_single_block_of_continue
    (fuel : Nat)
    (state next : IRState)
    (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts (fuel + 2) state [YulStmt.block body] = .continue next := by
      sorry
private theorem compatValue_not_mem_scope_of_reservedPrefix
    {scope : List String}
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope) :
    "__compat_value" ∉ scope := by
      sorry
private theorem validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : name ∈ spec.fields.map (·.name)) :
    ¬ name.startsWith "__" := by
      sorry
private theorem scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {scope : List String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hscopeNames :
      ∀ name, name ∈ scope →
        name ∈
          (fn.params.map (·.name) ++
            collectStmtListBindNames fn.body ++
            collectStmtListAssignedNames fn.body ++
            spec.fields.map (·.name))) :
    scopeAvoidsReservedCompilerPrefix scope := by
      sorry
theorem compiledStmtStep_setStorage_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (halias : f.aliasSlots = [])
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] := by
        sorry
-- private theorem compiledStmtStep_setStorageAddr_singleSlot_preserves
--     {fields : List Field}
--     {scope : List String}
--     {fieldName : String}
--     {value : Expr}
--     {valueIR : YulExpr}
--     {slot : Nat}
--     (hcore : FunctionBody.ExprCompileCore value)
--     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
--     (hfind : findFieldWithResolvedSlot fields fieldName =
--       some ({ name := fieldName, ty := FieldType.address }, slot))
--     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
--     (hnoConflict : firstFieldWriteSlotConflict fields = none)
--     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
--     CompiledStmtStep.preserves fields scope
--       (.setStorageAddr fieldName value)
--       [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] := by
--         sorry
theorem compiledStmtStep_setStorageAddr_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorageAddr fieldName value)
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] := by
        sorry
-- private theorem compiledStmtStep_mstore_single_preserves
--     {fields : List Field}
--     {scope : List String}
--     {offset value : Expr}
--     {offsetIR valueIR : YulExpr}
--     (hcoreOffset : FunctionBody.ExprCompileCore offset)
--     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
--     (hcoreValue : FunctionBody.ExprCompileCore value)
--     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
--     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
--     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
--     CompiledStmtStep.preserves fields scope
--       (.mstore offset value)
--       [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] := by
--         sorry
theorem compiledStmtStep_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.mstore offset value)
      [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] := by
        sorry
-- private theorem compiledStmtStep_tstore_single_preserves
--     {fields : List Field}
--     {scope : List String}
--     {offset value : Expr}
--     {offsetIR valueIR : YulExpr}
--     (hcoreOffset : FunctionBody.ExprCompileCore offset)
--     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
--     (hcoreValue : FunctionBody.ExprCompileCore value)
--     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
--     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
--     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
--     CompiledStmtStep.preserves fields scope
--       (.tstore offset value)
--       [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] := by
--         sorry
theorem compiledStmtStep_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    {offsetIR valueIR : YulExpr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.tstore offset value)
      [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] := by
        sorry
private theorem compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingUint fieldName key value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingUint fieldName key value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingUint fieldName key value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] := by
            sorry
private theorem compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    {keyIRs : List YulExpr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
    (hkeyIRs : CompilationModel.compileExprList fields .calldata keys = Except.ok keyIRs)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [keyIRs.foldl
              (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
              (YulExpr.lit slot), valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingChain fieldName keys value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [keyIRs.foldl
                  (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
                  (YulExpr.lit slot), valueIR])].length + extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [keyIRs.foldl
                  (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
                  (YulExpr.lit slot), valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingChain fieldName keys value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    {keyIRs : List YulExpr}
    {valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
    (hkeyIRs : CompilationModel.compileExprList fields .calldata keys = Except.ok keyIRs)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingChain fieldName keys value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [keyIRs.foldl
            (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            (YulExpr.lit slot), valueIR])] := by
              sorry
private theorem compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping fieldName key value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping fieldName key value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMapping_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping fieldName key value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] := by
            sorry
private theorem compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
             if wordOffset == 0 then mappingBase
             else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMappingWord fieldName key wordOffset value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingWord fieldName key wordOffset value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] := by
             sorry
private theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.block
        [ YulStmt.let_ "__compat_value" valueIR
        , YulStmt.let_ "__compat_packed"
            (YulExpr.call "and" [YulExpr.ident "__compat_value",
              YulExpr.lit (packedMaskNat packed)])
        , YulStmt.let_ "__compat_slot_word"
            (YulExpr.call "sload"
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
        , YulStmt.let_ "__compat_slot_cleared"
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
        , YulStmt.expr
            (YulExpr.call "sstore"
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
               YulExpr.call "or"
                 [YulExpr.ident "__compat_slot_cleared",
                   YulExpr.call "shl"
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] -
        [YulStmt.block
          [ YulStmt.let_ "__compat_value" valueIR
          , YulStmt.let_ "__compat_packed"
              (YulExpr.call "and" [YulExpr.ident "__compat_value",
                YulExpr.lit (packedMaskNat packed)])
          , YulStmt.let_ "__compat_slot_word"
              (YulExpr.call "sload"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
          , YulStmt.let_ "__compat_slot_cleared"
              (YulExpr.call "and"
                [YulExpr.ident "__compat_slot_word",
                  YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
          , YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                 YulExpr.call "or"
                   [YulExpr.ident "__compat_slot_cleared",
                     YulExpr.call "shl"
                       [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime
          (.setMappingPackedWord fieldName key wordOffset packed value) = sourceResult ∧
        execIRStmts
            ([YulStmt.block
              [ YulStmt.let_ "__compat_value" valueIR
              , YulStmt.let_ "__compat_packed"
                  (YulExpr.call "and" [YulExpr.ident "__compat_value",
                    YulExpr.lit (packedMaskNat packed)])
              , YulStmt.let_ "__compat_slot_word"
                  (YulExpr.call "sload"
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
              , YulStmt.let_ "__compat_slot_cleared"
                  (YulExpr.call "and"
                    [YulExpr.ident "__compat_slot_word",
                      YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
              , YulStmt.expr
                  (YulExpr.call "sstore"
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                     YulExpr.call "or"
                       [YulExpr.ident "__compat_slot_cleared",
                         YulExpr.call "shl"
                           [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]].length +
              extraFuel + 1)
            state
            [YulStmt.block
              [ YulStmt.let_ "__compat_value" valueIR
              , YulStmt.let_ "__compat_packed"
                  (YulExpr.call "and" [YulExpr.ident "__compat_value",
                    YulExpr.lit (packedMaskNat packed)])
              , YulStmt.let_ "__compat_slot_word"
                  (YulExpr.call "sload"
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
              , YulStmt.let_ "__compat_slot_cleared"
                  (YulExpr.call "and"
                    [YulExpr.ident "__compat_slot_word",
                      YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
              , YulStmt.expr
                  (YulExpr.call "sstore"
                    [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                     if wordOffset == 0 then mappingBase
                     else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                     YulExpr.call "or"
                       [YulExpr.ident "__compat_slot_cleared",
                         YulExpr.call "shl"
                           [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingPackedWord fieldName key wordOffset packed value)
      [YulStmt.block
        [ YulStmt.let_ "__compat_value" valueIR
        , YulStmt.let_ "__compat_packed"
            (YulExpr.call "and" [YulExpr.ident "__compat_value",
              YulExpr.lit (packedMaskNat packed)])
        , YulStmt.let_ "__compat_slot_word"
            (YulExpr.call "sload"
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
        , YulStmt.let_ "__compat_slot_cleared"
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
        , YulStmt.expr
            (YulExpr.call "sstore"
              [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
               if wordOffset == 0 then mappingBase
               else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
               YulExpr.call "or"
                 [YulExpr.ident "__compat_slot_cleared",
                   YulExpr.call "shl"
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] := by
                       sorry
private theorem compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
             if wordOffset == 0 then mappingBase
             else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setStructMember fieldName key memberName value) =
          sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStructMember fieldName key memberName value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setStructMember_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {keyIR valueIR : YulExpr}
    {slot : Nat}
    (hmapping : isMapping fields fieldName = true)
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember fieldName key memberName value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] := by
             sorry
private theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping2 fieldName key1 key2 value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping2 fieldName key1 key2 value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] := by
              sorry
private theorem compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
             let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
             if wordOffset == 0 then mappingSlot2
             else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setMapping2Word fieldName key1 key2 wordOffset value) =
          sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping2Word fieldName key1 key2 wordOffset value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] := by
             sorry
private theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
             let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
             if wordOffset == 0 then mappingSlot2
             else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime
          (.setStructMember2 fieldName key1 key2 memberName value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
                 let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
                 if wordOffset == 0 then mappingSlot2
                 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStructMember2 fieldName key1 key2 memberName value))
          sourceResult
          irExec := by
            sorry
theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    {members : List StructMember}
    {key1IR key2IR valueIR : YulExpr}
    {slot : Nat}
    (hmapping2 : isMapping2 fields fieldName = true)
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember2 fieldName key1 key2 memberName value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] := by
             sorry
theorem compiledStmtStep_setStorage_aliasSlots
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots fields fieldName = some (slot :: f.aliasSlots))
    (halias : f.aliasSlots ≠ [])
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope)
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.block
        ([YulStmt.let_ "__compat_value" valueIR] ++
          (slot :: f.aliasSlots).map (fun writeSlot =>
            YulStmt.expr
              (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] := by
                sorry
theorem compiledStmtStep_setStorage_of_validateIdentifierShapes
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hscopeNames :
      ∀ name, name ∈ scope →
        name ∈
          (fn.params.map (·.name) ++
            collectStmtListBindNames fn.body ++
            collectStmtListAssignedNames fn.body ++
            spec.fields.map (·.name)))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR, CompiledStmtStep spec.fields scope (.setStorage fieldName value) compiledIR := by
      sorry
theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {pfx suffix : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hprefix :
      StmtListScopeDiscipline
        (spec.fields.map (·.name))
        (fn.params.map (·.name))
        pfx)
    (hbody : fn.body = pfx ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx)
        (.setStorage fieldName value)
        compiledIR := by
          sorry
theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {pfx suffix : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) pfx)
    (hbody : fn.body = pfx ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx)
        (.setStorage fieldName value)
        compiledIR := by
          sorry
theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {pfx suffix : List Stmt}
    {bodyIR : List YulStmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hbodyCompile :
      CompilationModel.compileStmtList
        spec.fields [] [] .calldata [] false (fn.params.map (·.name)) fn.body =
          Except.ok bodyIR)
    (hbody : fn.body = pfx ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx)
        (.setStorage fieldName value)
        compiledIR := by
          sorry
theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {pfx suffix : List Stmt}
    {bodyIR : List YulStmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hbodyCompile :
      CompilationModel.compileStmtList
        spec.fields [] [] .calldata [] false (fn.params.map (·.name)) fn.body =
          Except.ok bodyIR)
    (hbody : fn.body = pfx ++ .setStorage fieldName value :: suffix)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) pfx)
        (.setStorage fieldName value)
        compiledIR := by
          sorry
private theorem terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec)
    (hnotContinue : ∀ next, sourceResult ≠ .continue next) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
      sorry
theorem compiledStmtStep_ite
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by
      sorry
private theorem stmtListTouchesUnsupportedContractSurface_append
    {pfx suffix : List Stmt} :
    stmtListTouchesUnsupportedContractSurface (pfx ++ suffix) =
      (stmtListTouchesUnsupportedContractSurface pfx ||
        stmtListTouchesUnsupportedContractSurface suffix) := by
          sorry
private theorem stmtListCompileCore_of_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    FunctionBody.StmtListCompileCore scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) := by
        sorry
private theorem foldl_stmtNextScope_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    List.foldl stmtNextScope scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) = scope := by
        sorry
private theorem stmtListGenericCore_singleton_setStorage_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {value : Expr}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] := by
      sorry
private theorem stmtListGenericCore_singleton_setStorageAddr_singleSlot
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {value : Expr}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] := by
      sorry
private theorem stmtListGenericCore_singleton_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] := by
      sorry
private theorem stmtListGenericCore_singleton_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] := by
      sorry
private theorem stmtListGenericCore_of_requireClausesOnly
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) := by
        sorry
private theorem stmtListGenericCore_of_requireClausesThenSetStorageLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName : String)
    (slot writeVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.setStorage fieldName (Expr.literal writeVal)]) := by
          sorry
private theorem stmtListGenericCore_of_requireClausesThenReturnLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.return (Expr.literal retVal)]) := by
          sorry
private theorem stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (tmp : String)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)]) := by
          sorry
private theorem stmtListGenericCore_of_requireClausesThenLetSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
          sorry
private theorem stmtListGenericCore_of_requireClausesThenLetAssignSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.literal m),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
           sorry
private theorem stmtListGenericCore_of_requireClausesThenLetAssignAddSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
           sorry
private theorem stmtListGenericCore_of_requireClausesThenLetAssignSubSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
           sorry
private theorem stmtListGenericCore_of_requireClausesThenLetAssignMulSetStorageLocalLiteral
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (fieldName tmp : String)
    (slot n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m)),
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by
           sorry
private theorem stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
    {fields : List Field}
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope [clause.toStmt] := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface
    {fields : List Field}
    {scope : List String} {pfx suffix : List Stmt}
    (hprefix : SupportedStmtList fields scope pfx)
    (hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope pfx) suffix)
    (ihPrefix : stmtListTouchesUnsupportedContractSurface pfx = false →
      StmtListGenericCore fields scope pfx)
    (ihSuffix : stmtListTouchesUnsupportedContractSurface suffix = false →
      StmtListGenericCore fields (List.foldl stmtNextScope scope pfx) suffix)
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (pfx ++ suffix) = false) :
    StmtListGenericCore fields scope (pfx ++ suffix) := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface
    {fields : List Field}
    {scope : List String}
    {rest : List Stmt}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (ihRest : stmtListTouchesUnsupportedContractSurface rest = false →
      StmtListGenericCore fields scope rest)
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (clause.toStmt :: rest) = false) :
    StmtListGenericCore fields scope (clause.toStmt :: rest) := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String} {pfx suffix : List Stmt}
    (hprefix : SupportedStmtList fields scope pfx)
    (hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope pfx) suffix)
    (ihPrefix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites pfx = false →
        StmtListGenericCore fields scope pfx)
    (ihSuffix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites suffix = false →
        StmtListGenericCore fields (List.foldl stmtNextScope scope pfx) suffix)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (pfx ++ suffix) = false) :
    StmtListGenericCore fields scope (pfx ++ suffix) := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {rest : List Stmt}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (ihRest :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false →
        StmtListGenericCore fields scope rest)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (clause.toStmt :: rest) = false) :
    StmtListGenericCore fields scope (clause.toStmt :: rest) := by
      sorry
private theorem false_of_supportedStmtList_ite_surface
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hsurface :
      stmtTouchesUnsupportedContractSurface
        (Stmt.ite cond thenBranch elseBranch) = false) :
    False := by
      sorry
private theorem false_of_supportedStmtList_ite_list_surface
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.ite cond thenBranch elseBranch] = false) :
    False := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {value : Expr}
    {slot : Nat}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.address }, slot))
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] := by
      sorry
private theorem stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] := by
      sorry
private theorem compileExprList_core_ok
    {fields : List Field}
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    ∃ exprIRs, CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs := by
      sorry
private theorem eval_compileExprList_core_of_scope
    {fields : List Field}
    {scope : List String}
    {exprs : List Expr}
    {exprIRs : List YulExpr}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : ∀ expr ∈ exprs, FunctionBody.exprBoundNamesInScope expr scope)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hcompiled : CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs) :
    ∃ values,
      SourceSemantics.evalExprList fields runtime exprs = some values ∧
      List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) exprIRs values := by
        sorry
private theorem evalIRExpr_mappingSlotChain
    {state : IRState}
    {baseSlot : Nat}
    {keyIRs : List YulExpr}
    {keyVals : List Nat}
    (hkeys : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) keyIRs keyVals) :
    evalIRExpr state
      (keyIRs.foldl
        (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
        (YulExpr.lit baseSlot)) =
      some (SourceSemantics.mappingSlotChain baseSlot keyVals) := by
        sorry
/-- Extra Tier 2 assumptions needed to turn the singleton mapping-write
constructors in `SupportedStmtList` into real compiled-step proofs. These are
kept separate from the surface predicate because the remaining obligation is a
layout-specific slot-safety fact, not a syntactic fragment question. -/
structure SupportedStmtListMappingWriteSlotSafety (fields : List Field) : Prop where
  setMappingUintSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  setMappingChainSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {keys : List Expr}
      {value : Expr}
      {slot : Nat},
      (∀ expr ∈ keys, FunctionBody.ExprCompileCore expr) →
      (∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope) →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none)
  setMappingSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
  setMappingWordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
  setMappingPackedWordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key value : Expr}
      {wordOffset slot : Nat}
      {packed : PackedBits},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      "__compat_value" ∉ scope →
      "__compat_packed" ∉ scope →
      "__compat_slot_word" ∉ scope →
      "__compat_slot_cleared" ∉ scope →
      packedBitsValid packed = true →
      findFieldSlot fields fieldName = some slot →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
  setStructMemberSingle :
    ∀ {scope : List String}
      {fieldName memberName : String}
      {key value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember},
      FunctionBody.ExprCompileCore key →
      FunctionBody.exprBoundNamesInScope key scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      isMapping fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
  setMapping2Single :
    ∀ {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {slot : Nat},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none)
  setMapping2WordSingle :
    ∀ {scope : List String}
      {fieldName : String}
      {key1 key2 value : Expr}
      {wordOffset slot : Nat},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)
  setStructMember2Single :
    ∀ {scope : List String}
      {fieldName memberName : String}
      {key1 key2 value : Expr}
      {slot wordOffset : Nat}
      {members : List StructMember},
      FunctionBody.ExprCompileCore key1 →
      FunctionBody.exprBoundNamesInScope key1 scope →
      FunctionBody.ExprCompileCore key2 →
      FunctionBody.exprBoundNamesInScope key2 scope →
      FunctionBody.ExprCompileCore value →
      FunctionBody.exprBoundNamesInScope value scope →
      findFieldSlot fields fieldName = some slot →
      findStructMembers fields fieldName = some members →
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none } →
      isMapping2 fields fieldName = true ∧
      findFieldWriteSlots fields fieldName = some [slot] ∧
      (∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none)

private theorem stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingUint fieldName key value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {keys : List Expr}
    {value : Expr}
    (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
    (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyVals,
        SourceSemantics.evalExprList fields runtime keys = some keyVals →
          findResolvedFieldAtSlotCopy fields
            (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (SourceSemantics.mappingSlotChain slot keyVals) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingChain fieldName keys value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMappingSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping fieldName key value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingWord fieldName key wordOffset value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {packed : PackedBits}
    {key value : Expr}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hcompatValue : "__compat_value" ∉ scope)
    (hcompatPacked : "__compat_packed" ∉ scope)
    (hcompatSlotWord : "__compat_slot_word" ∉ scope)
    (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
    (hpacked : packedBitsValid packed = true)
    (hmapping : isMapping fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingPackedWord fieldName key wordOffset packed value] := by
      sorry
private theorem stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {slot wordOffset : Nat}
    {key value : Expr}
    {members : List StructMember}
    (hcoreKey : FunctionBody.ExprCompileCore key)
    (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping : isMapping fields fieldName = true)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember fieldName key memberName value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {slot : Nat}
    {key1 key2 value : Expr}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping2 fieldName key1 key2 value] := by
      sorry
private theorem stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName : String}
    {wordOffset slot : Nat}
    {key1 key2 value : Expr}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] := by
      sorry
private theorem stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
    {fields : List Field}
    {scope : List String}
    {fieldName memberName : String}
    {slot wordOffset : Nat}
    {key1 key2 value : Expr}
    {members : List StructMember}
    (hcoreKey1 : FunctionBody.ExprCompileCore key1)
    (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
    (hcoreKey2 : FunctionBody.ExprCompileCore key2)
    (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
    (hmapping2 : isMapping2 fields fieldName = true)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat1 keyNat2,
        SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
        SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
          findResolvedFieldAtSlotCopy fields
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (Compiler.Proofs.abstractMappingSlot
              (Compiler.Proofs.abstractMappingSlot slot keyNat1)
              keyNat2 + wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember2 fieldName key1 key2 memberName value] := by
      sorry
private theorem false_of_supportedStmtList_singleton_stmt_surface
    {stmt : Stmt}
    (hunsupported : stmtTouchesUnsupportedContractSurface stmt = true)
    (hsurface : stmtListTouchesUnsupportedContractSurface [stmt] = false) :
    False := by
      sorry
private theorem false_of_supportedStmtList_returnMapping_surface
    {fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.return (Expr.mapping fieldName key)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.return (Expr.mapping fieldName key))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letStorageField_surface
    {tmp fieldName : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.storage fieldName)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.storage fieldName))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMapping_surface
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mapping fieldName key)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mapping fieldName key))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMapping2_surface
    {tmp fieldName : String}
    {key1 key2 : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_letMappingUint_surface
    {tmp fieldName : String}
    {key : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.letVar tmp (Expr.mappingUint fieldName key))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingUintSingle_surface
    {fieldName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingUint fieldName key value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingUint fieldName key value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingChainSingle_surface
    {fieldName : String}
    {keys : List Expr}
    {value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingChain fieldName keys value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingChain fieldName keys value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingSingle_surface
    {fieldName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping fieldName key value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping fieldName key value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingWordSingle_surface
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingWord fieldName key wordOffset value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingWord fieldName key wordOffset value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMappingPackedWordSingle_surface
    {fieldName : String}
    {key value : Expr}
    {wordOffset : Nat}
    {packed : PackedBits}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMappingPackedWord fieldName key wordOffset packed value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMappingPackedWord fieldName key wordOffset packed value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setStructMemberSingle_surface
    {fieldName memberName : String}
    {key value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setStructMember fieldName key memberName value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setStructMember fieldName key memberName value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMapping2Single_surface
    {fieldName : String}
    {key1 key2 value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping2 fieldName key1 key2 value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping2 fieldName key1 key2 value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setMapping2WordSingle_surface
    {fieldName : String}
    {key1 key2 value : Expr}
    {wordOffset : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setMapping2Word fieldName key1 key2 wordOffset value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_setStructMember2Single_surface
    {fieldName memberName : String}
    {key1 key2 value : Expr}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.setStructMember2 fieldName key1 key2 memberName value] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.setStructMember2 fieldName key1 key2 memberName value)
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface])
    hsurface

private theorem false_of_supportedStmtList_rawLogLiterals_surface
    {topics : List Nat}
    {dataOffset dataSize : Nat}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)] = false) :
    False :=
  false_of_supportedStmtList_singleton_stmt_surface
    (stmt := Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize))
    (by simp [stmtTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedContractSurface,
      exprTouchesUnsupportedCoreSurface,
      exprTouchesUnsupportedStateSurface,
      exprTouchesUnsupportedCallSurface,
      stmtTouchesUnsupportedEffectSurface])
    hsurface

private theorem false_of_supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_surface
    {ownerField senderVar ownerVar paramName msg1 msg2 : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [ Stmt.letVar senderVar Expr.caller
        , Stmt.letVar ownerVar (Expr.storage ownerField)
        , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
        , Stmt.setStorage ownerField (Expr.param paramName)
        , Stmt.stop
        ] = false) :
    False := by
      sorry
private theorem false_of_supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_surface
    {ownerField targetField senderVar ownerVar targetVar paramName msg1 msg2 : String}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [ Stmt.letVar senderVar Expr.caller
        , Stmt.letVar ownerVar (Expr.storage ownerField)
        , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
        , Stmt.letVar targetVar (Expr.storage targetField)
        , Stmt.require
            (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
        , Stmt.setStorage targetField (Expr.param paramName)
        , Stmt.stop
        ] = false) :
    False := by
      sorry
theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by
      sorry
theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListGenericCore fields scope stmts := by
      sorry
/-- The current supported statement-list witness already suffices for the
weaker helper-free source-step interface consumed by the exact helper-aware
seam. This keeps helper-free reuse derivable directly from the proof-layer
fragment witness without exposing the stronger full generic-core theorem at the
supported-body boundary. -/
theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  stmtListHelperFreeStepInterface_of_core
    (stmtListGenericCore_of_supportedStmtList_of_surface
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoConflict
      hSupported
      hsurface)

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListHelperFreeStepInterface fields scope stmts :=
  stmtListHelperFreeStepInterface_of_core
    (stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      hnoConflict
      hSupported
      hsafety
      hsurface)

theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
    (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
    (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
    (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false)
    (hsafety : SupportedStmtListMappingWriteSlotSafety fields) :
    StmtListHelperFreeStepInterface fields scope stmts := by
      sorry
/-- The supported-body interface also derives the weaker source-side reuse
witness needed by the exact helper-aware seam: helper-free heads retain the
legacy generic-step obligation, while helper-positive heads can be discharged
separately. -/
theorem SupportedBodyInterface.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by
      sorry
theorem SupportedBodyInterfaceExceptMappingWrites.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety spec.fields) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by
      sorry
private theorem exprBoundNamesInScope_of_scopeNamesIncluded
    {expr : Expr}
    {scope largerScope : List String}
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.exprBoundNamesInScope expr largerScope := by
      sorry
private theorem stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
      sorry
private theorem stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
      sorry
theorem stmtListGenericCore_of_stmtListCompileCore
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    StmtListGenericCore fields scope stmts :=
  stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    hcore
    FunctionBody.scopeNamesIncluded_refl

theorem stmtListGenericCore_of_stmtListTerminalCore
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts) :
    StmtListGenericCore fields scope stmts :=
  stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    hterminal
    FunctionBody.scopeNamesIncluded_refl

theorem stmtListGenericCore_append
    {fields : List Field}
    {scope : List String}
    {pfx suffix : List Stmt}
    (hprefix : StmtListGenericCore fields scope pfx)
    (hsuffix :
      StmtListGenericCore
        fields
        (List.foldl stmtNextScope scope pfx)
        suffix) :
    StmtListGenericCore fields scope (pfx ++ suffix) := by
      sorry
private theorem scopeNamesIncluded_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt} :
    FunctionBody.scopeNamesIncluded scope (List.foldl stmtNextScope scope stmts) := by
      sorry
theorem compileStmtList_ok_of_stmtListGenericCore
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
          sorry
theorem compileStmtList_ok_of_stmtListGenericWithHelpers
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
          sorry
theorem compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
          sorry
theorem stmtStepMatchesIRExec_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
      sorry
theorem stmtStepMatchesIRExecWithInternals_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch : stmtStepMatchesIRExecWithInternals fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec := by
      sorry
theorem stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields scope sourceResult irExec) :
    FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
      sorry
theorem stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch :
      stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec) :
    stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
      sorry
private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by
      sorry
private theorem scopeNamesIncluded_stmtNextScope
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope stmt)
      (collectStmtNames stmt ++ inScopeNames) := by
        sorry
private theorem execIRStmts_append_of_continue
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead : execIRStmts fuel state head = .continue next) :
    execIRStmts fuel state (head ++ tail) =
      execIRStmts (fuel - head.length) next tail := by
        sorry
private theorem execIRStmts_append_of_not_continue
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResult)
    (hhead : execIRStmts fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmts fuel state (head ++ tail) = irExec := by
      sorry
private theorem execIRStmtsWithInternals_append_of_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) =
      execIRStmtsWithInternals runtimeContract (fuel - head.length) next tail := by
        sorry
private theorem execIRStmtsWithInternals_append_of_not_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResultWithInternals)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) = irExec := by
      sorry
theorem exec_compileStmtList_generic_sizeOf_extraFuel_step
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
          sorry
theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
          sorry
theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec :=
        execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExecWithInternals
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
          sorry
theorem exec_compileStmtList_generic_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
        sorry
theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
        sorry
theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec :=
        execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
        sorry
theorem supported_function_body_correct_from_exact_state_generic
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
          sorry
/-- Exact helper-aware body theorem for a helper-aware generic statement
induction witness. This is the induction-level target needed to replace the
current helper-free `SupportedStmtList` gate with compositional helper-step
proofs. -/
private theorem supported_function_body_correct_from_exact_state_generic_helper_steps_raw
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hgeneric :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtListWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body = sourceResult ∧
      execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
          sorry
-- /-- Exact helper-aware body theorem for an exact helper-aware generic
-- statement-induction witness. Unlike the transitional legacy-compiled-body
-- theorem, this already targets `execIRStmtsWithInternals`, so future helper-call
-- cases can be proved against the compiled semantics that actually executes
-- helper-rich Yul. -/
-- private theorem
--     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
--     (runtimeContract : IRContract)
--     (model : CompilationModel)
--     (fn : FunctionSpec)
--     (bodyStmts : List YulStmt)
--     (helperFuel : Nat)
--     (tx : IRTransaction)
--     (initialWorld : Verity.ContractState)
--     (state : IRState)
--     (bindings : List (String × Nat))
--     (extraFuel : Nat)
--     (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
--     (hfuelPos : 0 < helperFuel)
--     (hnormalized : SourceSemantics.effectiveFields model = model.fields)
--     (hnoEvents : model.events = [])
--     (hnoErrors : model.errors = [])
--     (hgeneric :
--       StmtListGenericWithHelpersAndHelperIR
--         runtimeContract
--         model
--         (SourceSemantics.effectiveFields model)
--         (fn.params.map (·.name))
--         fn.body)
--     (hbodyCompile :
--       compileStmtList model.fields model.events model.errors .calldata [] false
--         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
--     (hscope :
--       FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
--     (hbounded : FunctionBody.bindingsBounded bindings)
--     (hstateRuntime :
--       FunctionBody.runtimeStateMatchesIR
--         (SourceSemantics.effectiveFields model)
--         { world := SourceSemantics.withTransactionContext initialWorld tx
--           bindings := [] }
--         state)
--     (hstateBindings :
--       FunctionBody.bindingsExactlyMatchIRVars bindings state) :
--     SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
--       runtimeContract
--       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
--         sorry
/-- Transitional helper-aware body/IR preservation target for the non-core
generic body theorem. This already moves the source side onto helper-aware
semantics, but the compiled side still runs through legacy `execIRStmts`, so it
only matches the current helper-free compiled-body boundary. -/
def SupportedFunctionBodyWithHelpersIRPreservationGoal
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmtListWithHelpers
      model
      (SourceSemantics.effectiveFields model)
      helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings }
      fn.body = sourceResult ∧
    execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
    FunctionBody.stmtResultMatchesIRExec
      (SourceSemantics.effectiveFields model) sourceResult irExec

/-- Exact future helper-aware body theorem target: helper-aware source semantics
against helper-aware compiled-body semantics. This is the body-level theorem
shape needed once helper-rich statements enter the proved domain, because raw
`execIRStmts` rejects Yul constructs such as `letMany` that represent internal
helper calls. -/
def SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmtListWithHelpers
      model
      (SourceSemantics.effectiveFields model)
      helperFuel
      { world := SourceSemantics.withTransactionContext initialWorld tx
        bindings := bindings }
      fn.body = sourceResult ∧
    execIRStmtsWithInternals runtimeContract
      (bodyStmts.length + extraFuel + 1) state bodyStmts = irExec ∧
    stmtResultMatchesIRExecWithInternals
      (SourceSemantics.effectiveFields model) sourceResult irExec

/-- Disjoint-based body-level bridge: the helper-free compiled-body goal lifts to
the exact helper-aware compiled-body target when the compiled body is disjoint
from the runtime contract's internal function table.  Does **not** require
`runtimeContract.internalFunctions = []`. -/
theorem supported_function_body_with_helpers_and_helper_ir_goal_of_legacy_ir_goal_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hbody :
      SupportedFunctionBodyWithHelpersIRPreservationGoal
        model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Under compiled-body disjointness, the exact helper-aware body goal can also
be collapsed back to the legacy compiled-body goal. This keeps the new exact
helper-aware seam reusable with the existing function-level theorem surface
until callers are ready to retarget all the way to `execIRFunctionWithInternals`. -/
theorem supported_function_body_with_helpers_ir_goal_of_helper_ir_goal_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hbody :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract
        model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract bodyStmts) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Exact helper-aware body theorem for a helper-aware generic statement
induction witness. This is the induction-level target needed to replace the
current helper-free `SupportedStmtList` gate with compositional helper-step
proofs. -/
theorem supported_function_body_correct_from_exact_state_generic_helper_steps
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hgeneric :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Exact helper-aware body theorem for an exact helper-aware generic
statement-induction witness. This is the future-proof induction-level theorem
surface for helper-rich bodies because it already targets
`SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`. -/
theorem supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Body-level exact helper-aware bridge for the future helper-rich theorem
path: helper-free heads only need the weaker helper-free source/compiled reuse
witnesses, while helper-surface-positive heads are supplied directly by the
exact helper-step interface. This removes the structural requirement that the
whole body already satisfy `StmtListGenericCore` before helper-rich cases can
enter the exact compiled theorem target. -/
theorem supported_function_body_correct_from_exact_state_generic_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hsteps :
      StmtListHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Body-level exact helper-aware bridge over the split helper-positive
interfaces: genuine internal-helper heads are discharged separately from the
residual coarse helper-surface heads, so future helper-summary work does not
also need to prove unrelated non-helper exact-step cases. -/
theorem supported_function_body_correct_from_exact_state_generic_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hinternalSteps :
      StmtListInternalHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidualSteps :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Body-level exact helper-aware bridge over the fully split genuine-helper
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are supplied separately, so the next helper-rich
proof step can land at the exact source-side obligation it discharges. -/
theorem supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Body-level exact helper-aware bridge over the fully split genuine-helper
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are supplied separately, so the next helper-rich
proof step can land at the exact source-side obligation it discharges. -/
theorem supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdirect :
      StmtListDirectInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
private theorem
    generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    StmtListGenericWithHelpersAndHelperIR
      runtimeContract
      model
      (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name))
      fn.body :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    (runtimeContract := runtimeContract)
    (spec := model)
    (hhelperFree := hhelperFree)
    (hsteps :=
      stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
        (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
            hcall
            hassign)
          hexpr
          hstruct)
        hresidual)
    (hdisjoint := hdisjoint)

/-- Disjoint-based body-level exact helper-aware bridge over the fully split
genuine-helper interfaces.  Replaces `StmtListHelperFreeCompiledLegacyCompatible`
+ `runtimeContract.internalFunctions = []` with the weaker
`StmtListHelperFreeCompiledCallsDisjoint`.  This is the entry point for
function bodies that live in a contract with an internal helper table. -/
theorem supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hexpr :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Current-fragment disjointness-based wrapper that lands directly in the exact
helper-aware compiled body goal. This keeps the existing helper-free step
library reusable while exposing the weaker compiled-side condition that later
helper-table work actually needs. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Current-fragment wrapper that lands directly in the exact helper-aware
compiled body goal. This keeps the existing helper-free step library reusable,
but removes the need for callers to supply a separate
`StmtListCompiledLegacyCompatible` witness when the body already lies on the
current supported contract surface. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Tier 2 disjointness-based exact helper-aware wrapper for the alternate
singleton mapping-write contract surface. This keeps the helper-aware
compiled-body seam available even before those writes are promoted onto the
default support path, without assuming the runtime helper table is empty. -/
theorem
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes_callsDisjoint
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Tier 2 exact helper-aware wrapper for the alternate singleton
mapping-write contract surface. This keeps the helper-aware compiled-body seam
available even before those writes are promoted onto the default support path. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes
    (runtimeContract : IRContract)
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hfuelPos : 0 < helperFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hnoPacked : ∀ field ∈ model.fields, field.packedBits = none)
    (hcontractSurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Goal-based helper-aware wrapper around the generic body/IR preservation
theorem. This keeps the current helper-free collapse available as a corollary,
while making the direct helper-aware body/IR target explicit in Lean. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers_goal
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperGoal :
      SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal
        model
        (SourceSemantics.effectiveFields model)
        helperFuel
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        fn.body)
    (hgeneric :
      StmtListGenericCore
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Helper-aware wrapper around the generic body/IR preservation theorem.
This theorem now consumes the exact source-side helper-conservative-extension
goal rather than baking in the temporary fail-closed helper scan directly.
Today that goal is still discharged from `stmtListTouchesUnsupportedHelperSurface
= false`; later helper-summary/rank composition should target the same named
goal surface without another theorem-shape change. -/
theorem supported_function_body_correct_from_exact_state_generic_with_helpers
    (model : CompilationModel)
    (fn : FunctionSpec)
    (bodyStmts : List YulStmt)
    (helperFuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (state : IRState)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
    (hnormalized : SourceSemantics.effectiveFields model = model.fields)
    (hnoEvents : model.events = [])
    (hnoErrors : model.errors = [])
    (hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false)
    (hhelperFree :
      StmtListHelperFreeStepInterface
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
    (hscope :
      FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (hbounded : FunctionBody.bindingsBounded bindings)
    (hstateRuntime :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := [] }
        state)
    (hstateBindings :
      FunctionBody.bindingsExactlyMatchIRVars bindings state) :
    SupportedFunctionBodyWithHelpersIRPreservationGoal
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
        sorry
/-- Constructor for the helper-aware single-step interface when the head
statement is `Stmt.internalCallAssign`. The proof is parameterised by a single
source-to-IR alignment bridge that the rank-decreasing callee induction will
supply. The bridge captures the end-to-end obligation: given matching
preconditions, the source and IR execution results for this statement match
through `stmtStepMatchesIRExecWithInternals`.

The bridge is quantified over an extra `irFuel` so that the proof can
instantiate it at the right fuel level derived from `extraFuel`.

The `compileOk` obligation is passed through from the compilation hypothesis. -/
theorem compiledStmtStepWithHelpersAndHelperIR_internalCallAssign
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false scope
      (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    -- End-to-end source↔IR alignment bridge.
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope
      (Stmt.internalCallAssign names calleeName args)
      compiledIR := by
        sorry
/-- Generic `CompiledStmtStepWithHelpersAndHelperIR` constructor for
`Stmt.internalCall` (void internal helper calls).  Analogous to
`compiledStmtStepWithHelpersAndHelperIR_internalCallAssign` but for the
void-call case where the compiled IR is `[.expr (.call yulName argExprs)]`.

The caller supplies a `bridge` hypothesis that ties the source-level
`execStmtWithHelpers` result to the IR-level `execIRStmtsWithInternals` result
on the singleton IR list with `irFuel + 3` fuel. -/
theorem compiledStmtStepWithHelpersAndHelperIR_internalCall
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false scope
      (Stmt.internalCall calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    -- End-to-end source↔IR alignment bridge.
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.expr (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope
      (Stmt.internalCall calleeName args)
      compiledIR := by
        sorry
/-- Non-vacuous list-level constructor for a direct helper-return-binding head.
This packages `compiledStmtStepWithHelpersAndHelperIR_internalCallAssign` into
the split direct-helper step interface expected by the exact helper-aware list
induction seam. -/
theorem stmtListDirectInternalHelperAssignStepInterface_cons_internalCallAssign
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope
        (Stmt.internalCallAssign names calleeName args)
        compiledIR)
    (hrest :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        rest) :
    StmtListDirectInternalHelperAssignStepInterface
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCallAssign names calleeName args :: rest) := by
        sorry
/-- Exact Tier 4 head-step proof object for a function body's direct internal
helper surface. Future helper-rank induction should construct this single
catalog once, then reuse the mechanical list-interface assembly theorems
downstream. -/
structure DirectInternalHelperHeadStepCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCall calleeName args)
          compiledIR
  assign :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCallAssign names calleeName args)
          compiledIR

/-- Mid-level Tier 4 seam: future rank induction can package direct-helper
singletons here by proving compilation succeeds for the head and that the exact
singleton IR execution matches the source helper-aware step. The mechanical
`CompiledStmtStepWithHelpersAndHelperIR` construction into
`DirectInternalHelperHeadStepCatalog` is then shared. -/
structure DirectInternalHelperCallHeadStepBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCall calleeName args) = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCall calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.expr (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

structure DirectInternalHelperAssignHeadStepBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {names : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {names : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

structure DirectInternalHelperHeadStepBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  callCompile :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCall calleeName args) = Except.ok compiledIR
  callBridge :
    ∀ {scope : List String} {calleeName : String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      calleeName ∈ helperCallNames fn →
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCall calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.expr (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])
  assignCompile :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR
  assignBridge :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      calleeName ∈ helperCallNames fn →
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

/-- Callee-local Tier 4 bridge inventory. This matches
`SupportedBodyHelperInterface.calleeRanksDecrease` directly: future rank
induction can construct one reusable bridge object per referenced helper callee,
and the body-level head-step bridge catalog is assembled mechanically. -/
structure DirectInternalHelperPerCalleeBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName

/-- Assign-only half of the callee-local Tier 4 bridge inventory. This isolates
the roadmap's current blocker, namely helper-return-binding steps, while the
void-call half remains mechanically vacuous under the current fragment. -/
structure DirectInternalHelperPerCalleeAssignBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName

/-- Reassemble the full callee-local bridge catalog from the current supported
body witness plus the assign-only bridge half. The call half is vacuous because
`SupportedStmtList` still excludes direct helper calls from the fragment. -/
theorem directInternalHelperPerCalleeBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn := by
      sorry
/-- Split compile-side Tier 4 inventory. This isolates the purely compilation
obligations from the semantic bridge obligations so future fragment widening can
discharge compile success generically once direct helper calls are admitted into
the supported statement witness. -/
structure DirectInternalHelperPerCalleeCallCompileCatalog
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope
            (Stmt.internalCall calleeName args) = Except.ok compiledIR

/-- Assign-only half of the compile-side Tier 4 inventory. This isolates the
current fragment-widening blocker once direct helper return-binding calls are
admitted into the supported statement witness. -/
structure DirectInternalHelperPerCalleeAssignCompileCatalog
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {names : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope
            (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR

-- /-- Reassemble the full compile-side Tier 4 inventory from independently
-- constructed call and assign halves. -/
-- theorem directInternalHelperPerCalleeCompileCatalog_of_callCatalog_and_assignCatalog
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hcall : DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn)
--     (hassign : DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn) :
--     DirectInternalHelperPerCalleeCompileCatalog spec fields fn := by
--       sorry
/-- Under the current supported statement fragment, every direct helper void
call compile obligation is vacuous because `SupportedStmtList` contains no
helper-call syntax at all. This lets the public Tier 4 seam keep only the
assign-side compile inventory explicit. -/
theorem directInternalHelperPerCalleeCallCompileCatalog_of_supportedBody
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn) :
    DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn := by
      sorry
/-- Split compile-side Tier 4 inventory. This isolates the purely compilation
obligations from the semantic bridge obligations so future fragment widening can
discharge compile success generically once direct helper calls are admitted into
the supported statement witness. -/
structure DirectInternalHelperPerCalleeCompileCatalog
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope
            (Stmt.internalCall calleeName args) = Except.ok compiledIR
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {names : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope
            (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR

-- /-- Callee-local runtime-helper witness inventory. This isolates the part of the
-- Tier 4 seam that is already discharged by the compiled runtime helper table, so
-- future helper-rank induction does not need to thread lookup/presence facts
-- through every direct-helper singleton proof. -/
-- structure DirectInternalHelperPerCalleeRuntimeWitnessCatalog
--     (runtimeContract : IRContract)
--     (spec : CompilationModel)
--     (fn : FunctionSpec) : Prop where
--   witness :
--     ∀ {calleeName : String},
--       calleeName ∈ helperCallNames fn →
--       SupportedCompiledInternalHelperWitness spec runtimeContract calleeName

-- /-- Build the callee-local runtime-helper witness inventory directly from the
-- global runtime helper table and the body's existing helper witness inventory. -/
-- theorem directInternalHelperPerCalleeRuntimeWitnessCatalog_of_runtimeHelperTable
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fn : FunctionSpec}
--     (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
--     (hHelpers : SupportedBodyHelperInterface spec fn) :
--     DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn := by
--       sorry
-- /-- Split semantic Tier 4 core. This keeps the end-to-end source/IR step
-- alignment separate from both compile-success obligations and runtime helper
-- lookup obligations, matching the eventual division between helper-rank
-- induction and contract-level helper-table construction. -/
-- structure DirectInternalHelperPerCalleeSemanticCoreCatalog
--     (runtimeContract : IRContract)
--     (spec : CompilationModel)
--     (fields : List Field)
--     (fn : FunctionSpec) : Prop where
--   call :
--     ∀ {calleeName : String},
--       calleeName ∈ helperCallNames fn →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCall calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCall calleeName args))
--             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--               [YulStmt.expr (YulExpr.call
--                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])
--   assign :
--     ∀ {calleeName : String},
--       calleeName ∈ helperCallNames fn →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {names : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCallAssign names calleeName args))
--             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--               [YulStmt.letMany names (YulExpr.call
--                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- /-- Irreducible semantic Tier 4 kernel. This is the part future helper-rank
-- induction should actually construct: source helper witnesses and summary
-- soundness are supplied explicitly, so callers that already carry
-- `SupportedBodyHelperInterface` plus helper-summary proofs can reassemble the
-- full semantic core mechanically. -/
-- structure DirectInternalHelperPerCalleeSemanticKernelCatalog
--     (runtimeContract : IRContract)
--     (spec : CompilationModel)
--     (fields : List Field)
--     (fn : FunctionSpec) : Prop where
--   call :
--     ∀ {calleeName : String},
--       (hmem : calleeName ∈ helperCallNames fn) →
--       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
--       InternalHelperSummarySound spec
--         sourceWitness.callee
--         sourceWitness.summary.contract →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCall calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCall calleeName args))
--             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--               [YulStmt.expr (YulExpr.call
--                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])
--   assign :
--     ∀ {calleeName : String},
--       (hmem : calleeName ∈ helperCallNames fn) →
--       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
--       InternalHelperSummarySound spec
--         sourceWitness.callee
--         sourceWitness.summary.contract →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {names : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCallAssign names calleeName args))
--             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--               [YulStmt.letMany names (YulExpr.call
--                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- /-- Call-only half of the irreducible semantic Tier 4 kernel. This lets future
-- helper-rank induction discharge statement-position void helper calls
-- independently from helper-return-binding calls. -/
-- structure DirectInternalHelperPerCalleeCallSemanticKernelCatalog
--     (runtimeContract : IRContract)
--     (spec : CompilationModel)
--     (fields : List Field)
--     (fn : FunctionSpec) : Prop where
--   call :
--     ∀ {calleeName : String},
--       (hmem : calleeName ∈ helperCallNames fn) →
--       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
--       InternalHelperSummarySound spec
--         sourceWitness.callee
--         sourceWitness.summary.contract →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCall calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCall calleeName args))
--             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--               [YulStmt.expr (YulExpr.call
--                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- /-- Assign-only half of the irreducible semantic Tier 4 kernel. This isolates
-- the roadmap's current strategic blocker, namely direct helper-return-binding
-- steps, from the void-call half. -/
-- structure DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--     (runtimeContract : IRContract)
--     (spec : CompilationModel)
--     (fields : List Field)
--     (fn : FunctionSpec) : Prop where
--   assign :
--     ∀ {calleeName : String},
--       (hmem : calleeName ∈ helperCallNames fn) →
--       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
--       InternalHelperSummarySound spec
--         sourceWitness.callee
--         sourceWitness.summary.contract →
--       ∀ (compiledHelper :
--           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--         {scope : List String} {names : List String} {args : List Expr}
--         {compiledIR : List YulStmt} {argExprs : List YulExpr},
--         CompilationModel.compileStmt fields [] [] .calldata [] false scope
--           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
--         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
--         ∀ (runtime : SourceSemantics.RuntimeState)
--           (state : IRState)
--           (helperFuel : Nat)
--           (irFuel : Nat),
--           0 < helperFuel →
--           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
--           FunctionBody.scopeNamesPresent scope runtime.bindings →
--           FunctionBody.bindingsBounded runtime.bindings →
--           FunctionBody.runtimeStateMatchesIR fields runtime state →
--           stmtStepMatchesIRExecWithInternals fields
--             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
--             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
--               (Stmt.internalCallAssign names calleeName args))
--           (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
--             [YulStmt.letMany names (YulExpr.call
--               (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- /-- Under the current supported statement fragment, every direct helper call
-- kernel obligation is vacuous because `SupportedStmtList` contains no helper-call
-- syntax at all. This lets the public Tier 4 seam focus on the assign side, which
-- is the actual roadmap blocker. -/
-- theorem directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hbody : SupportedBodyInterface spec fn) :
--     DirectInternalHelperPerCalleeCallSemanticKernelCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Reassemble the full semantic kernel from independently constructed call and
-- assign halves. This lets future helper-rank induction target the assign side
-- first without changing the downstream bridge machinery. -/
-- theorem directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hcall :
--       DirectInternalHelperPerCalleeCallSemanticKernelCatalog
--         runtimeContract spec fields fn)
--     (hassign :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Reassemble the split semantic Tier 4 core from helper witnesses and summary
-- soundness already carried by `SupportedBodyHelperInterface`, plus the smaller
-- semantic kernel future rank induction actually needs to construct. -/
-- theorem
--     directInternalHelperPerCalleeSemanticCoreCatalog_of_supportedBodyHelpers_and_helperSummariesSound_and_semanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hHelpers : SupportedBodyHelperInterface spec fn)
--     (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the assign-only callee-local Tier 4 bridge inventory directly from
-- the assign compile catalog, callee-local runtime helper witnesses, the
-- supported body's helper-summary inventory, and the irreducible assign semantic
-- kernel. This packages the exact assign-side proof object future rank induction
-- should ultimately construct. -/
-- theorem
--     directInternalHelperPerCalleeAssignBridgeCatalog_of_assignCompileCatalog_and_runtimeWitnessCatalog_and_supportedBodyHelpers_and_helperSummariesSound_and_assignSemanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hcompile :
--       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hHelpers : SupportedBodyHelperInterface spec fn)
--     (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split assign-side Tier 4 ingredients plus the current supported-body
-- witness. This keeps downstream theorem seams on the reusable head-step catalog
-- that future rank induction should ultimately construct, instead of forcing them
-- to route through the intermediate assign-bridge layer. -/
-- theorem
--     directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hbody : SupportedBodyInterface spec fn)
--     (hcompile :
--       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hsummaries :
--       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split assign-side Tier 4 ingredients plus the current supported-body
-- witness. This keeps downstream theorem seams on the reusable head-step catalog
-- that future rank induction should ultimately construct, and now lands first on
-- the exact body-level bridge catalog rather than the derived per-callee
-- assign-bridge layer. -/
-- theorem
--     directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hbody : SupportedBodyInterface spec fn)
--     (hcompile :
--       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hsummaries :
--       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split assign-side compile/runtime-helper-table/semantic-kernel Tier 4
-- ingredients plus the current supported-body witness. This removes the last
-- runtime-witness repackaging step on the assign-first theorem chain. -/
-- theorem
--     directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_assignSemanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hbody : SupportedBodyInterface spec fn)
--     (hcompile :
--       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
--     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
--     (hsummaries :
--       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
--         runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
/-- Split semantic Tier 4 inventory. This keeps the end-to-end source/IR step
alignment separate from the compile-success obligations, matching the eventual
division between helper-rank induction and fragment-widening compile lemmas. -/
structure DirectInternalHelperPerCalleeSemanticBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {args : List Expr}
          {compiledIR : List YulStmt} {argExprs : List YulExpr},
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCall calleeName args) = Except.ok compiledIR →
        CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
        ∀ (runtime : SourceSemantics.RuntimeState)
          (state : IRState)
          (helperFuel : Nat)
          (irFuel : Nat),
          0 < helperFuel →
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
          FunctionBody.scopeNamesPresent scope runtime.bindings →
          FunctionBody.bindingsBounded runtime.bindings →
          FunctionBody.runtimeStateMatchesIR fields runtime state →
          stmtStepMatchesIRExecWithInternals fields
            (stmtNextScope scope (Stmt.internalCall calleeName args))
            (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
              (Stmt.internalCall calleeName args))
            (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
              [YulStmt.expr (YulExpr.call
                (CompilationModel.internalFunctionYulName calleeName) argExprs)])
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {names : List String} {args : List Expr}
          {compiledIR : List YulStmt} {argExprs : List YulExpr},
        CompilationModel.compileStmt fields [] [] .calldata [] false scope
          (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
        CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
        ∀ (runtime : SourceSemantics.RuntimeState)
          (state : IRState)
          (helperFuel : Nat)
          (irFuel : Nat),
          0 < helperFuel →
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
          FunctionBody.scopeNamesPresent scope runtime.bindings →
          FunctionBody.bindingsBounded runtime.bindings →
          FunctionBody.runtimeStateMatchesIR fields runtime state →
          stmtStepMatchesIRExecWithInternals fields
            (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
            (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
              (Stmt.internalCallAssign names calleeName args))
            (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
              [YulStmt.letMany names (YulExpr.call
                (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- /-- Reassemble the existing semantic bridge inventory once runtime helper
-- witnesses are available callee-locally. This leaves future rank induction with
-- just the genuinely semantic work while contract compilation can discharge the
-- runtime witness side independently. -/
-- theorem
--     directInternalHelperPerCalleeSemanticBridgeCatalog_of_runtimeWitnessCatalog_and_semanticCoreCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hsemantic :
--       DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn) :
--     DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn := by
--       sorry
/-- Reassemble the existing callee-local Tier 4 bridge object after splitting the
compile and semantic obligations. This is the intended future landing point for
independent fragment-widening and helper-rank-induction developments. -/
theorem directInternalHelperPerCalleeBridgeCatalog_of_compileCatalog_and_semanticBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
    (hsemantic :
      DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn := by
      sorry
/-- Assemble the existing body-level direct-helper bridge catalog from the more
rank-induction-friendly per-callee bridge inventory. -/
theorem directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcallee : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
      sorry
/-- Assemble the body-level direct-helper bridge catalog directly from the
current helper-free supported-body witness plus the assign-only per-callee
bridge inventory. This keeps downstream theorems on the exact assign-only Tier 4
boundary instead of routing through the vacuous per-callee void-call layer. -/
theorem directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
      sorry
private theorem directInternalHelperHeadStepCatalog_call_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCall calleeName args)
          compiledIR := by
            sorry
private theorem directInternalHelperHeadStepCatalog_assign_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCallAssign names calleeName args)
          compiledIR := by
            sorry
/-- Build the reusable direct-helper head-step catalog from the lighter bridge
catalog seam. This keeps future helper-rank induction focused on exact singleton
bridges instead of reconstructing `CompiledStmtStepWithHelpersAndHelperIR`
objects by hand at every theorem layer. -/
theorem directInternalHelperHeadStepCatalog_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
      sorry
/-- Assemble the reusable direct-helper head-step catalog directly from the more
rank-induction-friendly per-callee bridge inventory. This lets downstream
wrapper theorems consume the exact catalog object future rank induction should
build, without routing through the intermediate body-level bridge catalog. -/
theorem directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcallee : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
      sorry
/-- Assemble the exact body-level direct-helper head-step catalog directly from
the split compile/semantic Tier 4 inventories. This removes the last per-callee
bridge detour once callers already provide the compile catalog and semantic
bridge data separately. -/
theorem directInternalHelperHeadStepCatalog_of_compileCatalog_and_semanticBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
    (hsemantic :
      DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
      sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split compile/runtime-witness/semantic-core Tier 4 inventories. This keeps
-- the theorem seam on the precise head-step catalog even before helper-summary
-- facts are reintroduced. -/
-- theorem directInternalHelperHeadStepCatalog_of_compileCatalog_and_runtimeWitnessCatalog_and_semanticCoreCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hsemantic :
--       DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split compile/runtime-witness/semantic-kernel Tier 4 inventories plus the
-- current supported-body helper summaries. This is the direct landing point for
-- future helper-rank induction once the semantic kernel is all that remains
-- non-vacuous. -/
-- theorem directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_semanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hhelpers : SupportedBodyHelpersInterface spec fn)
--     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
--     (hruntime :
--       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
--     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split compile/runtime-helper-table/semantic-kernel Tier 4 inventories plus
-- the current supported-body helper summaries. This removes the remaining
-- runtime-witness repackaging step once callers already provide the compiled
-- runtime helper table. -/
-- theorem
--     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_semanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hhelpers : SupportedBodyHelpersInterface spec fn)
--     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
--     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
--     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
--     (hkernel :
--       DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
-- /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- the split compile/runtime-helper-table/call-kernel/assign-kernel Tier 4
-- inventories plus the current supported-body helper summaries. This keeps the
-- wrapper seam on the exact future rank-induction target even when call and
-- assign semantic kernels are still supplied separately. -/
-- theorem
--     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_callSemanticKernelCatalog_and_assignSemanticKernelCatalog
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {fn : FunctionSpec}
--     (hhelpers : SupportedBodyHelpersInterface spec fn)
--     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
--     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
--     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
--     (hcall :
--       DirectInternalHelperPerCalleeCallSemanticKernelCatalog runtimeContract spec fields fn)
--     (hassign :
--       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog runtimeContract spec fields fn) :
--     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
--       sorry
/-- Assemble the reusable direct-helper head-step catalog directly from the
current helper-free supported-body witness plus the assign-only per-callee
bridge inventory. This removes one more derived Tier 4 seam while preserving the
same eventual rank-induction target. -/
theorem directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
      sorry
/-- Assemble the exact direct-helper-assign list interface from a reusable
single-head constructor. This pushes future helper-rank induction down to the
only genuinely new work: constructing the `Stmt.internalCallAssign` head step
itself. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble the exact direct-helper-assign list interface from head-step
constructors indexed only by helper callees that actually occur in the current
statement list. This is the precise seam future helper-rank induction should
target: it no longer needs to quantify over arbitrary helper names unrelated to
the body under proof. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Non-vacuous list-level constructor for a direct helper statement head.
This packages `compiledStmtStepWithHelpersAndHelperIR_internalCall` into the
split direct-helper call interface expected by the exact helper-aware list
induction seam. -/
theorem stmtListDirectInternalHelperCallStepInterface_cons_internalCall
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope
        (Stmt.internalCall calleeName args)
        compiledIR)
    (hrest :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        rest) :
    StmtListDirectInternalHelperCallStepInterface
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCall calleeName args :: rest) := by
        sorry
/-- Assemble the exact direct-helper-call list interface from a reusable
single-head constructor. This is the theorem future helper-rank induction
should target: once it can build `CompiledStmtStepWithHelpersAndHelperIR` for
an arbitrary `Stmt.internalCall` head, the surrounding list recursion is
mechanical. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble the exact direct-helper-call list interface from head-step
constructors indexed only by helper callees that actually occur in the current
statement list. This matches the `helperCallNames`-based rank inventory carried
by `SupportedBodyHelperInterface`, avoiding arbitrary-name quantification at the
function theorem boundary. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
      sorry
/-- Assemble both exact direct-helper list interfaces from a single body-local
head-step catalog. This keeps the list recursion mechanical so future
rank-decreasing helper proofs can focus on constructing one catalog object. -/
theorem stmtListDirectInternalHelperStepInterfaces_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec} :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn →
    StmtListDirectInternalHelperCallStepInterface
      runtimeContract
      spec
      fields
      scope
      fn.body ∧
    StmtListDirectInternalHelperAssignStepInterface
      runtimeContract
      spec
      fields
      scope
      fn.body := by
        sorry
private theorem internalFunctionYulName_ne_stop (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "stop" := by
  intro h; have := congrArg String.data h
  simp only [internalFunctionYulName, internalFunctionPrefix,
    show ∀ s : String, toString s = s from fun _ => rfl] at this
  simp at this
private theorem internalFunctionYulName_ne_sstore (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "sstore" := by
  intro h; have := congrArg String.data h
  simp only [internalFunctionYulName, internalFunctionPrefix,
    show ∀ s : String, toString s = s from fun _ => rfl] at this
  simp at this
private theorem internalFunctionYulName_ne_mstore (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "mstore" := by
  intro h; have := congrArg String.data h
  simp only [internalFunctionYulName, internalFunctionPrefix,
    show ∀ s : String, toString s = s from fun _ => rfl] at this
  simp at this
private theorem internalFunctionYulName_ne_revert (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "revert" := by
  intro h; have := congrArg String.data h
  simp only [internalFunctionYulName, internalFunctionPrefix,
    show ∀ s : String, toString s = s from fun _ => rfl] at this
  simp at this
private theorem internalFunctionYulName_ne_return (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "return" := by
  intro h; have := congrArg String.data h
  simp only [internalFunctionYulName, internalFunctionPrefix,
    show ∀ s : String, toString s = s from fun _ => rfl] at this
  simp at this
-- /-- Runtime-helper-table packaged version of
-- `execIRStmtsWithInternals_of_internalCallAssign_compile`: the caller no longer
-- threads a raw `findInternalFunction?` hypothesis by hand, only the compiled
-- helper witness coming from `SupportedRuntimeHelperTableInterface`. -/
-- theorem execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {scope : List String}
--     {names : List String}
--     {calleeName : String}
--     {args : List Expr}
--     {compiledIR : List YulStmt}
--     (compiledHelper :
--       SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--     (state : IRState)
--     (irFuel : Nat)
--     {argVals : List Nat}
--     {state' : IRState}
--     (hcompile :
--       CompilationModel.compileStmt fields [] [] .calldata [] false scope
--         (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
--     (argExprs : List YulExpr)
--     (hargCompile :
--       CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
--     (hargs :
--       evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
--         .values argVals state') :
--     ∃ helper,
--       compiledIR = [YulStmt.letMany names
--         (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
--       findInternalFunction? runtimeContract
--         (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
--       execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
--         match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
--         | .values values state'' =>
--             if names.length = values.length then
--               .continue (state''.setVars (names.zip values))
--             else .revert state''
--         | .stop state'' => .stop state''
--         | .return value' state'' => .return value' state''
--         | .revert state'' => .revert state'' := by
--           sorry
-- /-- Runtime-helper-table packaged version of
-- `execIRStmtsWithInternals_of_internalCall_compile`: the caller no longer threads
-- raw helper lookup or builtin-name side conditions by hand. -/
-- theorem execIRStmtsWithInternals_of_internalCall_compiledHelperWitness
--     {runtimeContract : IRContract}
--     {spec : CompilationModel}
--     {fields : List Field}
--     {scope : List String}
--     {calleeName : String}
--     {args : List Expr}
--     {compiledIR : List YulStmt}
--     (compiledHelper :
--       SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
--     (state : IRState)
--     (irFuel : Nat)
--     {argVals : List Nat}
--     {state' : IRState}
--     (hcompile :
--       CompilationModel.compileStmt fields [] [] .calldata [] false scope
--         (Stmt.internalCall calleeName args) = Except.ok compiledIR)
--     (argExprs : List YulExpr)
--     (hargCompile :
--       CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
--     (hargs :
--       evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
--         .values argVals state') :
--     ∃ helper,
--       compiledIR = [YulStmt.expr
--         (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
--       findInternalFunction? runtimeContract
--         (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
--       execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
--         match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
--         | .values _ state'' => .continue state''
--         | .stop state'' => .stop state''
--         | .return value' state'' => .return value' state''
--         | .revert state'' => .revert state'' := by
--           sorry
end Compiler.Proofs.IRGeneration
