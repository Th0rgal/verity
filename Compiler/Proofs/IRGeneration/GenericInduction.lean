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

private def externalIRExecResultToWithInternals : IRExecResult → IRExecResultWithInternals
  | .continue next => .continue next
  | .return value next => .return value next
  | .stop next => .stop next
  | .revert next => .revert next

private theorem stmtStepMatchesIRExecWithInternals_of_stmtStepMatchesIRExec
    {fields : List Field}
    {nextScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields nextScope sourceResult irExec) :
    stmtStepMatchesIRExecWithInternals fields nextScope sourceResult
      (externalIRExecResultToWithInternals irExec) := by
  cases sourceResult <;> cases irExec <;>
    simp [externalIRExecResultToWithInternals, stmtStepMatchesIRExec,
      stmtStepMatchesIRExecWithInternals] at hmatch ⊢ <;>
    exact hmatch

private abbrev compiledIRWithInternalsCompat
    (runtimeContract : IRContract)
    (compiledIR : List YulStmt) : Prop :=
  ∀ state extraFuel,
    execIRStmtsWithInternals runtimeContract
        (compiledIR.length + extraFuel + 1) state compiledIR =
      externalIRExecResultToWithInternals
        (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR)

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
    CompiledStmtStepWithHelpers spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    intro runtime state helperFuel extraFuel hexact hscope hbounded hruntime hslack
    rcases hstep.preserves runtime state extraFuel
        hexact hscope hbounded hruntime hslack with
      ⟨sourceResult, irExec, hsource, hir, hmatch⟩
    refine ⟨sourceResult, irExec, ?_, hir, hmatch⟩
    simpa [SourceSemantics.execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
      (spec := spec)
      (fields := fields)
      (fuel := helperFuel)
      (state := runtime)
      (stmt := stmt)
      hsurface] using hsource

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

private theorem legacyCompatibleExternalStmtList_append
    {before after : List YulStmt}
    (hbefore : LegacyCompatibleExternalStmtList before)
    (hafter : LegacyCompatibleExternalStmtList after) :
    LegacyCompatibleExternalStmtList (before ++ after) := by
  induction hbefore generalizing after with
  | nil =>
      simpa using hafter
  | comment msg rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.comment msg (rest ++ after) (ih hafter)
  | let_ name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.let_ name value (rest ++ after) (ih hafter)
  | assign name value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.assign name value (rest ++ after) (ih hafter)
  | expr value rest hrest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr value (rest ++ after) (ih hafter)
  | if_ cond body rest hbody hrest ihBody ihRest =>
      simpa using LegacyCompatibleExternalStmtList.if_ cond body (rest ++ after) hbody (ihRest hafter)
  | block body rest hbody hrest ihBody ihRest =>
      simpa using LegacyCompatibleExternalStmtList.block body (rest ++ after) hbody (ihRest hafter)
  | funcDef name params rets body rest hbody hrest ihBody ihRest =>
      simpa using
        LegacyCompatibleExternalStmtList.funcDef name params rets body (rest ++ after) hbody (ihRest hafter)

private theorem legacyCompatibleExternalStmtList_of_exprStmtExprs
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact LegacyCompatibleExternalStmtList.nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

private theorem legacyCompatibleExternalStmtList_revertWithMessage
    (message : String) :
    LegacyCompatibleExternalStmtList (CompilationModel.revertWithMessage message) := by
  unfold CompilationModel.revertWithMessage
  let headerExprs :=
    [ YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex errorStringSelectorWord]
    , YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]
    , YulExpr.call "mstore"
        [YulExpr.lit 36, YulExpr.lit (CompilationModel.bytesFromString message).length]
    ]
  let dataExprs :=
    (((CompilationModel.chunkBytes32 (CompilationModel.bytesFromString message)).zipIdx).map
      (fun (chunk, idx) =>
        let offset := 68 + idx * 32
        let word := CompilationModel.wordFromBytes chunk
        YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word]))
  let revertStmt :=
    YulStmt.expr
      (YulExpr.call "revert"
        [ YulExpr.lit 0
        , YulExpr.lit
            (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
        ])
  simpa [headerExprs, dataExprs, revertStmt, List.append_assoc] using
    legacyCompatibleExternalStmtList_append
      (before := headerExprs.map YulStmt.expr)
      (after := dataExprs.map YulStmt.expr ++ [revertStmt])
      (legacyCompatibleExternalStmtList_of_exprStmtExprs headerExprs)
      (legacyCompatibleExternalStmtList_append
        (before := dataExprs.map YulStmt.expr)
        (after := [revertStmt])
        (legacyCompatibleExternalStmtList_of_exprStmtExprs dataExprs)
        (LegacyCompatibleExternalStmtList.expr
          (YulExpr.call "revert"
            [ YulExpr.lit 0
            , YulExpr.lit
                (68 + (((CompilationModel.bytesFromString message).length + 31) / 32) * 32)
            ])
          []
          LegacyCompatibleExternalStmtList.nil))

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
    LegacyCompatibleExternalStmtList bodyIR := by sorry

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
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.let_ name valueIR [] LegacyCompatibleExternalStmtList.nil

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
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.assign name valueIR [] LegacyCompatibleExternalStmtList.nil

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
  unfold CompilationModel.compileStmt at hcompile
  rcases hfail : CompilationModel.compileRequireFailCond fields .calldata cond with _ | failCond
  · simp [hfail] at hcompile
  · simp [hfail] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.if_
      failCond
      (CompilationModel.revertWithMessage message)
      []
      (legacyCompatibleExternalStmtList_revertWithMessage message)
      LegacyCompatibleExternalStmtList.nil

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
  unfold CompilationModel.compileStmt at hcompile
  rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
  · simp [hvalue] at hcompile
  · simp [hvalue] at hcompile
    cases hcompile
    exact LegacyCompatibleExternalStmtList.expr
      (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])]
      (LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        []
        LegacyCompatibleExternalStmtList.nil)

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_stop
    {fields : List Field}
    {inScopeNames : List String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames .stop =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  injection hcompile with hbody
  subst hbody
  exact LegacyCompatibleExternalStmtList.expr
    (YulExpr.call "stop" [])
    []
    LegacyCompatibleExternalStmtList.nil

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
    LegacyCompatibleExternalStmtList bodyIR := by sorry

-- SORRY'D: /-- On the current supported contract surface, successful statement-list
-- SORRY'D: compilation stays inside the legacy helper-free external Yul subset. -/
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
  induction stmts generalizing inScopeNames bodyIR with
  | nil =>
      simp [CompilationModel.compileStmtList] at hcompile
      cases hcompile
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      rcases FunctionBody.compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      exact legacyCompatibleExternalStmtList_append
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked hstmtSurface hhead)
        (ih hrestSurface htail)

-- SORRY'D: /-- Derive the compiled-side legacy-compatibility witness needed by the exact
-- SORRY'D: helper-aware induction seam from the existing supported contract-surface scan. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro compiledIR hcompile
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked hstmtSurface hcompile

-- SORRY'D: /-- Any list-level compiled witness for full legacy compatibility also suffices
-- SORRY'D: for the weaker exact-seam witness that only constrains helper-free heads. -/
theorem stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts := by
  induction hlegacy with
  | nil =>
      exact .nil
  | @cons scope stmt rest hhead htail ih =>
      refine .cons ?_ ih
      intro _ compiledIR hcompile
      exact hhead compiledIR hcompile

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp hsurface
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro _ compiledIR hcompile
      exact YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
        runtimeContract
        hinternal
        compiledIR
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked
          hstmtSurface
          hcompile)

private theorem legacyCompatibleExternalStmtList_of_exprMap
    (exprs : List YulExpr) :
    LegacyCompatibleExternalStmtList (exprs.map YulStmt.expr) := by
  induction exprs with
  | nil =>
      exact .nil
  | cons expr rest ih =>
      simpa using LegacyCompatibleExternalStmtList.expr expr (rest.map YulStmt.expr) ih

private theorem legacyCompatibleExternalStmtList_of_letBindings
    (bindings : List (String × YulExpr))
    (rest : List YulStmt)
    (hrest : LegacyCompatibleExternalStmtList rest) :
    LegacyCompatibleExternalStmtList
      (bindings.map (fun binding => YulStmt.let_ binding.1 binding.2) ++ rest) := by
  revert hrest
  induction bindings with
  | nil =>
      intro hrest
      simpa using hrest
  | cons binding restBindings ih =>
      intro hrest
      simpa using LegacyCompatibleExternalStmtList.let_ binding.1 binding.2
        ((restBindings.map (fun inner => YulStmt.let_ inner.1 inner.2)) ++ rest)
        (ih hrest)

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
    LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileMappingSlotWrite at hcompile
-- SORRY'D:   by_cases hmapping : isMapping fields field
-- SORRY'D:   · simp [hmapping] at hcompile
-- SORRY'D:     cases hslots : findFieldWriteSlots fields field <;> simp [hslots] at hcompile
-- SORRY'D:     case some slots =>
-- SORRY'D:       cases slots with
-- SORRY'D:       | nil =>
-- SORRY'D:           simp at hcompile
-- SORRY'D:       | cons slot rest =>
-- SORRY'D:           cases rest with
-- SORRY'D:           | nil =>
-- SORRY'D:               injection hcompile with hbody
-- SORRY'D:               subst hbody
-- SORRY'D:               exact LegacyCompatibleExternalStmtList.expr _ [] .nil
-- SORRY'D:           | cons slot' rest' =>
-- SORRY'D:               injection hcompile with hbody
-- SORRY'D:               subst hbody
-- SORRY'D:               refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
-- SORRY'D:               exact legacyCompatibleExternalStmtList_of_letBindings
-- SORRY'D:                 [("__compat_key", keyExpr), ("__compat_value", valueExpr)]
-- SORRY'D:                 ((slot :: slot' :: rest').map (fun writeSlot =>
-- SORRY'D:                   YulStmt.expr
-- SORRY'D:                     (YulExpr.call "sstore"
-- SORRY'D:                       [let mappingBase :=
-- SORRY'D:                           YulExpr.call "mappingSlot"
-- SORRY'D:                             [YulExpr.lit writeSlot, YulExpr.ident "__compat_key"]
-- SORRY'D:                         if wordOffset == 0 then mappingBase
-- SORRY'D:                         else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
-- SORRY'D:                         YulExpr.ident "__compat_value"])))
-- SORRY'D:                 (legacyCompatibleExternalStmtList_of_exprMap _)
-- SORRY'D:   · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetMapping2_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2 fields dynamicSource field key1 key2 value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   unfold CompilationModel.compileSetMapping2 at hcompile
-- SORRY'D:   by_cases hmapping2 : isMapping2 fields field
-- SORRY'D:   · simp [hmapping2] at hcompile
-- SORRY'D:     cases hslots : findFieldWriteSlots fields field <;> simp [hslots] at hcompile
-- SORRY'D:     case some slots =>
-- SORRY'D:       rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr <;>
-- SORRY'D:         simp [hkey1] at hcompile
-- SORRY'D:       rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr <;>
-- SORRY'D:         simp [hkey2] at hcompile
-- SORRY'D:       rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr <;>
-- SORRY'D:         simp [hvalue] at hcompile
-- SORRY'D:       cases slots with
-- SORRY'D:       | nil =>
-- SORRY'D:           simp at hcompile
-- SORRY'D:       | cons slot rest =>
-- SORRY'D:           cases rest with
-- SORRY'D:           | nil =>
-- SORRY'D:               injection hcompile with hbody
-- SORRY'D:               subst hbody
-- SORRY'D:               exact LegacyCompatibleExternalStmtList.expr _ [] .nil
-- SORRY'D:           | cons slot' rest' =>
-- SORRY'D:               injection hcompile with hbody
-- SORRY'D:               subst hbody
-- SORRY'D:               refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
-- SORRY'D:               exact legacyCompatibleExternalStmtList_of_letBindings
-- SORRY'D:                 [("__compat_key1", key1Expr), ("__compat_key2", key2Expr),
-- SORRY'D:                   ("__compat_value", valueExpr)]
-- SORRY'D:                 ((slot :: slot' :: rest').map (fun writeSlot =>
-- SORRY'D:                   let innerSlot := YulExpr.call "mappingSlot"
-- SORRY'D:                     [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
-- SORRY'D:                   YulStmt.expr (YulExpr.call "sstore"
-- SORRY'D:                     [YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
-- SORRY'D:                       YulExpr.ident "__compat_value"])))
-- SORRY'D:                 (legacyCompatibleExternalStmtList_of_exprMap _)
-- SORRY'D:   · simp [hmapping2] at hcompile

-- SORRY'D: /-- On the Tier 2 alternate contract surface, successful single-statement
-- SORRY'D: compilation still stays inside the legacy helper-free external Yul subset. This
-- SORRY'D: extends the exact helper-aware compiled seam to the already-proved singleton
-- SORRY'D: mapping-write fragment instead of forcing it back onto the stricter default
-- SORRY'D: surface. -/
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
    LegacyCompatibleExternalStmtList bodyIR := by sorry
-- SORRY'D:   cases stmt with
-- SORRY'D:   | setMapping field key value =>
-- SORRY'D:       unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:       rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
-- SORRY'D:         simp [hkey] at hcompile
-- SORRY'D:       rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
-- SORRY'D:         simp [hvalue] at hcompile
-- SORRY'D:       exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
-- SORRY'D:   | setMappingUint field key value =>
-- SORRY'D:       unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:       rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
-- SORRY'D:         simp [hkey] at hcompile
-- SORRY'D:       rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
-- SORRY'D:         simp [hvalue] at hcompile
-- SORRY'D:       exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
-- SORRY'D:   | setMapping2 field key1 key2 value =>
-- SORRY'D:       unfold CompilationModel.compileStmt at hcompile
-- SORRY'D:       exact legacyCompatibleExternalStmtList_of_compileSetMapping2_ok hcompile
-- SORRY'D:   | stmt =>
-- SORRY'D:       exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
-- SORRY'D:         hnoPacked
-- SORRY'D:         (by simpa [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface)
-- SORRY'D:         hcompile

-- SORRY'D: /-- Tier 2 list-level legacy-compatibility witness for the alternate singleton
-- SORRY'D: mapping-write surface. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by sorry
-- SORRY'D:   induction stmts generalizing scope with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact .nil
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       have hstmtSurface :
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).1
-- SORRY'D:       have hrestSurface :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).2
-- SORRY'D:       refine .cons ?_ (ih hrestSurface)
-- SORRY'D:       intro compiledIR hcompile
-- SORRY'D:       exact
-- SORRY'D:         legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
-- SORRY'D:           hnoPacked hstmtSurface hcompile

-- SORRY'D: /-- Tier 2 exact-seam helper-free compiled compatibility witness. -/
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
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by sorry
-- SORRY'D:   induction stmts generalizing scope with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact .nil
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       have hstmtSurface :
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).1
-- SORRY'D:       have hrestSurface :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).2
-- SORRY'D:       refine .cons ?_ (ih hrestSurface)
-- SORRY'D:       intro _ compiledIR hcompile
-- SORRY'D:       exact
-- SORRY'D:         YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
-- SORRY'D:           runtimeContract
-- SORRY'D:           hinternal
-- SORRY'D:           compiledIR
-- SORRY'D:           (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
-- SORRY'D:             hnoPacked
-- SORRY'D:             hstmtSurface
-- SORRY'D:             hcompile)

-- SORRY'D: /-- Any full helper-free generic statement-list proof also gives the weaker
-- SORRY'D: source-side reuse witness needed by the future helper-rich exact seam: only the
-- SORRY'D: helper-free heads retain the old generic-step obligation. -/
theorem stmtListHelperFreeStepInterface_of_core
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts) :
    StmtListHelperFreeStepInterface fields scope stmts := by
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep htail ih =>
      refine .cons ?_ ih
      intro _
      exact ⟨compiledIR, hstep⟩

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the narrower exact
-- SORRY'D: internal-helper step interface vacuously. -/
theorem stmtListInternalHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtInternal : stmtTouchesInternalHelperSurface stmt = false :=
        stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtInternal] at hhelper
      cases hhelper

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the direct
-- SORRY'D: statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtDirect : stmtTouchesDirectInternalHelperCallSurface stmt = false :=
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the direct helper-return
-- SORRY'D: binding interface vacuously. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtDirect : stmtTouchesDirectInternalHelperAssignSurface stmt = false :=
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

-- SORRY'D: /-- Assemble the coarser direct helper interface from the two source-summary
-- SORRY'D: shapes it still contains: void helper statements and helper-return bindings. -/
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
  induction hcall with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadCall htailCall ih =>
      cases hassign with
      | cons hheadAssign htailAssign =>
          refine .cons ?_ (ih htailAssign)
          intro hdirect
          by_cases hcallFalse : stmtTouchesDirectInternalHelperCallSurface stmt = false
          · have hassignTrue : stmtTouchesDirectInternalHelperAssignSurface stmt = true := by
              simpa [stmtTouchesDirectInternalHelperSurface_eq_split, hcallFalse] using hdirect
            exact hheadAssign hassignTrue
          · have hcallTrue : stmtTouchesDirectInternalHelperCallSurface stmt = true := by
              cases hcallStmt : stmtTouchesDirectInternalHelperCallSurface stmt <;>
                simp [hcallStmt] at hcallFalse ⊢
            exact hheadCall hcallTrue

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the direct
-- SORRY'D: statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := stmts)
        hsurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := stmts)
        hsurface)

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtExpr : stmtTouchesExprInternalHelperSurface stmt = false :=
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtExpr] at hhelper
      cases hhelper

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the structural
-- SORRY'D: internal-helper interface vacuously. -/
theorem stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtStructural : stmtTouchesStructuralInternalHelperSurface stmt = false :=
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtStructural] at hhelper
      cases hhelper

-- SORRY'D: /-- Assemble the coarse internal-helper interface from the narrower proof-cut
-- SORRY'D: interfaces that match the actual proof obligations: direct helper statements,
-- SORRY'D: expression-position helper calls, and recursive structural transport. -/
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
  induction hdirect with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadDirect htailDirect ih =>
      cases hexpr with
      | cons hheadExpr htailExpr =>
          cases hstruct with
          | cons hheadStruct htailStruct =>
              refine .cons ?_ (ih htailExpr htailStruct)
              intro hhelper
              by_cases hdirectFalse : stmtTouchesDirectInternalHelperSurface stmt = false
              · by_cases hexprFalse : stmtTouchesExprInternalHelperSurface stmt = false
                · have hstructTrue : stmtTouchesStructuralInternalHelperSurface stmt = true := by
                    simpa [stmtTouchesInternalHelperSurface_eq_split, hdirectFalse, hexprFalse]
                      using hhelper
                  exact hheadStruct hstructTrue
                · have hexprTrue : stmtTouchesExprInternalHelperSurface stmt = true := by
                    cases hexprStmt : stmtTouchesExprInternalHelperSurface stmt <;>
                      simp [hexprStmt] at hexprFalse ⊢
                  exact hheadExpr hexprTrue
              · have hdirectTrue : stmtTouchesDirectInternalHelperSurface stmt = true := by
                  cases hdirectStmt : stmtTouchesDirectInternalHelperSurface stmt <;>
                    simp [hdirectStmt] at hdirectFalse ⊢
                exact hheadDirect hdirectTrue

-- SORRY'D: /-- Helper-surface-closed statement lists also satisfy the residual non-helper
-- SORRY'D: exact step interface vacuously. -/
theorem stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper _
      rw [hstmtSurface] at hhelper
      cases hhelper

-- SORRY'D: /-- Assemble the coarse exact helper-surface step interface from the split
-- SORRY'D: interfaces: genuine internal-helper heads are proved through the narrow helper
-- SORRY'D: surface interface, while the residual coarse-surface heads are discharged
-- SORRY'D: separately. -/
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
  induction hinternal with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadInternal htailInternal ih =>
      cases hresidual with
      | cons hheadResidual htailResidual =>
          refine .cons ?_ (ih htailResidual)
          intro hhelper
          by_cases hactual : stmtTouchesInternalHelperSurface stmt = true
          · exact hheadInternal hactual
          · have hactualFalse : stmtTouchesInternalHelperSurface stmt = false := by
              cases hactual' : stmtTouchesInternalHelperSurface stmt <;>
                simp [hactual'] at hactual ⊢
            exact hheadResidual hhelper hactualFalse

-- SORRY'D: /-- Lift an existing helper-free generic statement-list proof into the
-- SORRY'D: helper-aware induction world when the whole list is helper-surface closed. This
-- SORRY'D: is the current fail-closed bridge from the legacy generic library to the new
-- SORRY'D: helper-aware induction seam. -/
theorem stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
        (ih hsurface.2)
-- SORRY'D:   induction hgeneric generalizing hsurface with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact .nil
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       simp [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false] at hsurface
-- SORRY'D:       exact .cons
-- SORRY'D:         (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
-- SORRY'D:         (ih hsurface.2)

-- SORRY'D: /-- Lift the weaker helper-free step interface into the helper-aware generic
-- SORRY'D: induction world when the whole list is helper-surface closed. This removes the
-- SORRY'D: need to materialize a full legacy `StmtListGenericCore` witness at callers that
-- SORRY'D: only target the helper-aware body theorem. -/
theorem stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
  induction hhelperFree with
  | nil =>
      exact .nil
  | @cons scope stmt rest hhead htail ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rcases hhead hsurface.1 with ⟨compiledIR, hstep⟩
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
        (ih hsurface.2)

private theorem compiledStmtStepWithHelpers_preserves_withCompat
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hcompat : compiledIRWithInternalsCompat runtimeContract compiledIR) :
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
          fields (stmtNextScope scope stmt) sourceResult irExec := by
  intro runtime state helperFuel extraFuel _ hexact hscope hbounded hruntime hslack
  rcases hstep.preserves runtime state helperFuel extraFuel
      hexact hscope hbounded hruntime hslack with
    ⟨sourceResult, irExec, hsource, hir, hmatch⟩
  refine ⟨sourceResult, externalIRExecResultToWithInternals irExec, hsource, ?_, ?_⟩
  · simpa [externalIRExecResultToWithInternals, hir] using hcompat state extraFuel
  · exact stmtStepMatchesIRExecWithInternals_of_stmtStepMatchesIRExec hmatch
-- SORRY'D:       rcases hhead hsurface.1 with ⟨compiledIR, hstep⟩
-- SORRY'D:       exact .cons
-- SORRY'D:         (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
-- SORRY'D:         (ih hsurface.2)

-- SORRY'D: /-- Any helper-aware generic statement-step proof already closes the exact
-- SORRY'D: helper-aware compiled-side step goal when the compiled head stays inside the
-- SORRY'D: legacy-compatible external Yul subset and the runtime contract has no internal
-- SORRY'D: helper table. This is the compiled-side fail-closed bridge from the current
-- TYPESIG_SORRY: theorem domain to the exact helper-aware induction seam. -/
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
      runtimeContract spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    apply compiledStmtStepWithHelpers_preserves_withCompat hstep
    intro state extraFuel
    exact
      execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility runtimeContract
        (execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals
          runtimeContract
          (interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed
            runtimeContract))
        hinternal
        (compiledIR.length + extraFuel + 1)
        state
        compiledIR
        hlegacy

-- SORRY'D: /-- Disjoint-based bridge: any helper-aware generic statement-step proof closes
-- SORRY'D: the exact helper-aware compiled-side step goal when the compiled IR is disjoint
-- SORRY'D: from the internal function table.  Unlike `withHelperIR_of_legacyCompatible` this
-- SORRY'D: does **not** require `runtimeContract.internalFunctions = []`. -/
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
      runtimeContract spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    apply compiledStmtStepWithHelpers_preserves_withCompat hstep
    intro state extraFuel
    exact
      execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
        (compiledIR.length + extraFuel + 1)
        state
        compiledIR
        hdisjoint

-- SORRY'D: /-- Lift helper-aware statement-list proofs into the exact helper-aware compiled
-- SORRY'D: induction seam on the current legacy-compatible compiled subset. This isolates
-- SORRY'D: future helper-summary work to the genuinely new helper-call cases: already
-- SORRY'D: proved helper-free cases can be reused directly once callers supply the
-- SORRY'D: compiled-side legacy-compatibility witness. -/
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
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hlegacy with
      | cons hhead htail =>
          exact .cons
            (hstep.withHelperIR_of_legacyCompatible (hhead compiledIR hstep.compileOk) hinternal)
            (ih htail)

-- SORRY'D: /-- Exact helper-aware list bridge that splits the remaining work cleanly:
-- SORRY'D: helper-free heads still reuse the legacy generic step library plus the weaker
-- SORRY'D: helper-free compiled compatibility witness, while helper-positive heads are
-- SORRY'D: discharged only through a dedicated exact helper-aware step interface. -/
-- SORRY'D: theorem
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {scope : List String}
-- SORRY'D:     {stmts : List Stmt}
-- SORRY'D:     (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
-- SORRY'D:     (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
-- SORRY'D:     (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
-- SORRY'D:     (hinternal : runtimeContract.internalFunctions = []) :
-- SORRY'D:     StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
-- SORRY'D:   induction hsteps generalizing hhelperFree hlegacy with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact .nil
-- SORRY'D:   | @cons scope stmt rest hheadStep htailSteps ih =>
-- SORRY'D:       cases hhelperFree with
-- SORRY'D:       | cons hheadFree htailFree =>
-- SORRY'D:           cases hlegacy with
-- SORRY'D:           | cons hheadLegacy htailLegacy =>
-- SORRY'D:               by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
-- SORRY'D:               · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
-- SORRY'D:                 exact .cons
-- SORRY'D:                   ((hcore.withHelpers_of_helperSurfaceClosed hsurface)
-- SORRY'D:                     .withHelperIR_of_legacyCompatible
-- SORRY'D:                       (hheadLegacy hsurface compiledIR hcore.compileOk)
-- SORRY'D:                       hinternal)
-- SORRY'D:                   (ih htailFree htailLegacy)
-- SORRY'D:               · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
-- SORRY'D:                   cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
-- SORRY'D:                 rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
-- SORRY'D:                 exact .cons hcompiled (ih htailFree htailLegacy)

-- SORRY'D: /-- Disjoint-based exact helper-aware list bridge: helper-free heads reuse the
-- SORRY'D: legacy generic step library plus the new disjointness witness, while
-- SORRY'D: helper-positive heads are discharged through the dedicated step interface.
-- SORRY'D: Unlike the `_helperFreeCompiledLegacyCompatible` variant, this does **not**
-- SORRY'D: require `runtimeContract.internalFunctions = []`. -/
-- SORRY'D: theorem
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {scope : List String}
-- SORRY'D:     {stmts : List Stmt}
-- SORRY'D:     (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
-- SORRY'D:     (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
-- SORRY'D:     (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
-- SORRY'D:     StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
-- SORRY'D:   induction hsteps generalizing hhelperFree hdisjoint with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact .nil
-- SORRY'D:   | @cons scope stmt rest hheadStep htailSteps ih =>
-- SORRY'D:       cases hhelperFree with
-- SORRY'D:       | cons hheadFree htailFree =>
-- SORRY'D:           cases hdisjoint with
-- SORRY'D:           | cons hheadDisjoint htailDisjoint =>
-- SORRY'D:               by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
-- SORRY'D:               · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
-- SORRY'D:                 exact .cons
-- SORRY'D:                   ((hcore.withHelpers_of_helperSurfaceClosed hsurface)
-- SORRY'D:                     .withHelperIR_of_callsDisjoint
-- SORRY'D:                       (hheadDisjoint hsurface compiledIR hcore.compileOk))
-- SORRY'D:                   (ih htailFree htailDisjoint)
-- SORRY'D:               · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
-- SORRY'D:                   cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
-- SORRY'D:                 rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
-- SORRY'D:                 exact .cons hcompiled (ih htailFree htailDisjoint)

-- SORRY'D: /-- Exact helper-aware list bridge with the helper-positive work split cleanly:
-- SORRY'D: genuine internal-helper heads are supplied through a narrow helper-specific
-- SORRY'D: interface, while residual coarse helper-surface heads are tracked separately so
-- SORRY'D: future helper-summary proofs do not also inherit unrelated non-helper cases. -/
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by sorry
-- SORRY'D:   exact
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (hhelperFree := hhelperFree)
-- SORRY'D:       (hsteps :=
-- SORRY'D:         stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
-- SORRY'D:           hinternal
-- SORRY'D:           hresidual)
-- SORRY'D:       (hlegacy := hlegacy)
-- SORRY'D:       hnoInternalFunctions

-- SORRY'D: /-- Exact helper-aware list bridge over the fully split helper-positive
-- SORRY'D: interfaces: direct helper statements, expression-position helper heads, and
-- SORRY'D: recursive structural heads are tracked separately, so future summary/rank proofs
-- SORRY'D: can target the exact source-side obligation they discharge. -/
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by sorry
-- SORRY'D:   exact
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (hhelperFree := hhelperFree)
-- SORRY'D:       (hdirect :=
-- SORRY'D:         stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
-- SORRY'D:           hcall
-- SORRY'D:           hassign)
-- SORRY'D:       (hexpr := hexpr)
-- SORRY'D:       (hstruct := hstruct)
-- SORRY'D:       (hresidual := hresidual)
-- SORRY'D:       (hlegacy := hlegacy)
-- SORRY'D:       hnoInternalFunctions

-- SORRY'D: /-- Exact helper-aware list bridge over the fully split helper-positive
-- SORRY'D: interfaces: direct helper statements, expression-position helper heads, and
-- SORRY'D: recursive structural heads are tracked separately, so future summary/rank proofs
-- SORRY'D: can target the exact source-side obligation they discharge. -/
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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hinternal :=
        stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          hdirect
          hexpr
          hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by sorry
-- SORRY'D:   exact
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
-- SORRY'D:       (hsteps := hsteps)
-- SORRY'D:       (hlegacy := hlegacy)
-- SORRY'D:       hinternal

-- SORRY'D: /-- Disjoint-based exact helper-aware list bridge with `StmtListGenericCore`.
-- SORRY'D: The legacy `StmtListGenericCore` witness is reused for helper-free heads, with
-- SORRY'D: compiled-side disjointness replacing `internalFunctions = []`. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by sorry
-- SORRY'D:   exact
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
-- SORRY'D:       (hsteps := hsteps)
-- SORRY'D:       (hdisjoint := hdisjoint)

-- SORRY'D: /-- Exact helper-aware list bridge over the split helper-positive interfaces:
-- SORRY'D: the legacy `StmtListGenericCore` witness is still reused for helper-free heads,
-- SORRY'D: while genuine internal-helper heads and residual coarse helper-surface heads are
-- SORRY'D: supplied separately. -/
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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hinternal := hinternal)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hcall := hcall)
      (hassign := hassign)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hdirect := hdirect)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (stmts := stmts)
          hsurface)
      (hdisjoint := hdisjoint)

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (stmts := stmts)
          hsurface)
      (hlegacy := hlegacy)
      hinternal

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsurface := hsurface)
      (hlegacy :=
        stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible hlegacy)
      hinternal

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
    FunctionBody.ExprCompileCore expr := by sorry
-- SORRY'D:   induction expr with
-- SORRY'D:   | literal value =>
-- SORRY'D:       exact .literal value
-- SORRY'D:   | param name =>
-- SORRY'D:       exact .param name
-- SORRY'D:   | storage field =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | storageAddr field =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | localVar name =>
-- SORRY'D:       exact .localVar name
-- SORRY'D:   | caller =>
-- SORRY'D:       exact .caller
-- SORRY'D:   | contractAddress =>
-- SORRY'D:       exact .contractAddress
-- SORRY'D:   | chainid =>
-- SORRY'D:       exact .chainid
-- SORRY'D:   | msgValue =>
-- SORRY'D:       exact .msgValue
-- SORRY'D:   | blockTimestamp =>
-- SORRY'D:       exact .blockTimestamp
-- SORRY'D:   | blockNumber =>
-- SORRY'D:       exact .blockNumber
-- SORRY'D:   | constructorArg idx =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | blobbasefee =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | calldatasize =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | returndataSize =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | arrayLength name =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | storageArrayLength field =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | returnDataOptionalBoolAt outOffset =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mload offset =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | tload offset =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | calldataload offset =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | extcodesize addr =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | dynamicBytesEq lhs rhs =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | bitNot expr ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | logicalNot expr ih =>
-- SORRY'D:       exact .logicalNot <| ih (by simpa [exprTouchesUnsupportedContractSurface] using hsurface)
-- SORRY'D:   | add lhs rhs ihL ihR =>
-- SORRY'D:       exact .add
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | sub lhs rhs ihL ihR =>
-- SORRY'D:       exact .sub
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | mul lhs rhs ihL ihR =>
-- SORRY'D:       exact .mul
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | div lhs rhs ihL ihR =>
-- SORRY'D:       exact .div
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | sdiv lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mod lhs rhs ihL ihR =>
-- SORRY'D:       exact .mod
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | smod lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | bitAnd lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | bitOr lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | bitXor lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | shl lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | shr lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | sar lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | signextend lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | eq lhs rhs ihL ihR =>
-- SORRY'D:       exact .eq
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | ge lhs rhs ihL ihR =>
-- SORRY'D:       exact .ge
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | gt lhs rhs ihL ihR =>
-- SORRY'D:       exact .gt
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | sgt lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | lt lhs rhs ihL ihR =>
-- SORRY'D:       exact .lt
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | slt lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | le lhs rhs ihL ihR =>
-- SORRY'D:       exact .le
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | logicalAnd lhs rhs ihL ihR =>
-- SORRY'D:       exact .logicalAnd
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | logicalOr lhs rhs ihL ihR =>
-- SORRY'D:       exact .logicalOr
-- SORRY'D:         (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
-- SORRY'D:         (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
-- SORRY'D:   | ite cond thenVal elseVal ihCond ihThen ihElse =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | min lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | max lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | wMulDown lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | wDivUp lhs rhs ihL ihR =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mulDivDown a b c ihA ihB ihC =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mulDivUp a b c ihA ihB ihC =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mapping field key ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mappingWord field key offset ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mappingPackedWord field key offset packed ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mapping2 field key1 key2 ih1 ih2 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mapping2Word field key1 key2 offset ih1 ih2 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mappingUint field key ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | mappingChain field keys ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | structMember field key memberName ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | structMember2 field key1 key2 memberName ih1 ih2 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | arrayElement name index ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | storageArrayElement field index ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | call gas target value inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | staticcall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | delegatecall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | externalCall name args ih =>
-- SORRY'D:       cases hsurface
-- SORRY'D:   | internalCall name args ih =>
-- SORRY'D:       cases hsurface

private theorem fieldName_mem_fields_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    fieldName ∈ fields.map (·.name) := by sorry

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
  unfold CompilationModel.compileSetStorage at hcompile
  split at hcompile
  · simp at hcompile
  · cases hfind : findFieldWithResolvedSlot fields fieldName with
    | none =>
        simp [hfind] at hcompile
    | some resolved =>
        exact fieldName_mem_fields_of_findFieldWithResolvedSlot_some hfind

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
  unfold CompilationModel.compileStmt at hcompile
  cases hcond : CompilationModel.compileExpr fields .calldata cond with
  | error err =>
      simp [hcond] at hcompile
      cases hcompile
  | ok condIR =>
      cases hthen :
          CompilationModel.compileStmtList fields [] [] .calldata [] false scope thenBranch with
      | error err =>
          simp [hcond, hthen] at hcompile
          cases hcompile
      | ok thenIR =>
          cases helse :
              CompilationModel.compileStmtList fields [] [] .calldata [] false scope elseBranch with
          | error err =>
              simp [hcond, hthen, helse] at hcompile
              cases hcompile
          | ok elseIR =>
              by_cases helseEmpty : elseBranch.isEmpty
              · simp [hcond, hthen, helse, helseEmpty] at hcompile
                exact ⟨condIR, thenIR, elseIR, rfl, rfl, rfl⟩
              · simp [hcond, hthen, helse, helseEmpty] at hcompile
                exact ⟨condIR, thenIR, elseIR, rfl, rfl, rfl⟩

-- TYPESIG_SORRY: theorem stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurface (prefix ++ suffix) = false)
-- TYPESIG_SORRY:     (hcompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         fields [] [] .calldata [] false scope (prefix ++ suffix) =
-- TYPESIG_SORRY:           Except.ok bodyIR) :
-- TYPESIG_SORRY:     StmtListScopeCore (fields.map (·.name)) prefix := by sorry
-- SORRY'D:   induction prefix generalizing scope suffix bodyIR with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact StmtListScopeCore.nil
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       rcases compileStmtList_cons_ok_inv hcompile with
-- SORRY'D:         ⟨headIR, tailIR, hhead, htail, rfl⟩
-- SORRY'D:       have hstmtSurface :
-- SORRY'D:           stmtTouchesUnsupportedContractSurface stmt = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurface] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).1
-- SORRY'D:       have hrestSurface :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface (rest ++ suffix) = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurface] using
-- SORRY'D:           (Bool.or_eq_false.mp hsurface).2
-- SORRY'D:       cases stmt with
-- SORRY'D:       | letVar name value =>
-- SORRY'D:           exact StmtListScopeCore.letVar
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:               (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | assignVar name value =>
-- SORRY'D:           exact StmtListScopeCore.assignVar
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:               (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | setStorage fieldName value =>
-- SORRY'D:           have hfield :
-- SORRY'D:               fieldName ∈ fields.map (·.name) := by
-- SORRY'D:             simp [CompilationModel.compileStmt] at hhead
-- SORRY'D:             exact fieldName_mem_fields_of_compileSetStorage_ok hhead
-- SORRY'D:           exact StmtListScopeCore.setStorage
-- SORRY'D:             hfield
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:               (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | setStorageAddr fieldName value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | require cond message =>
-- SORRY'D:           exact StmtListScopeCore.require
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:               (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | return value =>
-- SORRY'D:           exact StmtListScopeCore.return_
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:               (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | stop =>
-- SORRY'D:           exact StmtListScopeCore.stop (ih hrestSurface htail)
-- SORRY'D:       | ite cond thenBranch elseBranch =>
-- SORRY'D:           have hcondSurface :
-- SORRY'D:               exprTouchesUnsupportedContractSurface cond = false := by
-- SORRY'D:             have hfalse1 := (Bool.or_eq_false.mp hstmtSurface).1
-- SORRY'D:             simpa [stmtTouchesUnsupportedContractSurface] using hfalse1
-- SORRY'D:           have hbranchesSurface :
-- SORRY'D:               stmtListTouchesUnsupportedContractSurface thenBranch ||
-- SORRY'D:                 stmtListTouchesUnsupportedContractSurface elseBranch = false := by
-- SORRY'D:             have hfalse2 := (Bool.or_eq_false.mp hstmtSurface).2
-- SORRY'D:             simpa [stmtTouchesUnsupportedContractSurface] using hfalse2
-- SORRY'D:           have hthenSurface :
-- SORRY'D:               stmtListTouchesUnsupportedContractSurface thenBranch = false :=
-- SORRY'D:             (Bool.or_eq_false.mp hbranchesSurface).1
-- SORRY'D:           have helseSurface :
-- SORRY'D:               stmtListTouchesUnsupportedContractSurface elseBranch = false :=
-- SORRY'D:             (Bool.or_eq_false.mp hbranchesSurface).2
-- SORRY'D:           rcases compileStmt_ite_ok_inv hhead with ⟨condIR, thenIR, elseIR, _, hthen, helse⟩
-- SORRY'D:           exact StmtListScopeCore.ite
-- SORRY'D:             (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hcondSurface)
-- SORRY'D:             (stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
-- SORRY'D:               (scope := scope) (prefix := thenBranch) (suffix := [])
-- SORRY'D:               (bodyIR := thenIR) (by simpa using hthenSurface) hthen)
-- SORRY'D:             (stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
-- SORRY'D:               (scope := scope) (prefix := elseBranch) (suffix := [])
-- SORRY'D:               (bodyIR := elseIR) (by simpa using helseSurface) helse)
-- SORRY'D:             (ih hrestSurface htail)
-- SORRY'D:       | mstore offset value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | tstore offset value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | storageArrayPush field value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | storageArrayPop field =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setStorageArrayElement field index value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMapping field key value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMappingWord field key wordOffset value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMappingPackedWord field key wordOffset packed value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMapping2 field key1 key2 value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMapping2Word field key1 key2 wordOffset value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMappingUint field key value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setMappingChain field keys value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setStructMember field key memberName value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | setStructMember2 field key1 key2 memberName value =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | requireError cond errorName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | revertError errorName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | returnValues values =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | returnArray name =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | returnBytes name =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | returnStorageWords name =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | calldatacopy destOffset sourceOffset size =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | returndataCopy destOffset sourceOffset size =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | revertReturndata =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | forEach varName count body =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | emit eventName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | internalCall functionName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | internalCallAssign names functionName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | rawLog topics dataOffset dataSize =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | externalCallBind resultVars externalName args =>
-- SORRY'D:           cases hstmtSurface
-- SORRY'D:       | ecm mod args =>
-- SORRY'D:           cases hstmtSurface

-- TYPESIG_SORRY: private theorem stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {stmt : Stmt}
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurface (prefix ++ stmt :: suffix) = false) :
-- TYPESIG_SORRY:     stmtTouchesUnsupportedContractSurface stmt = false := by sorry
-- SORRY'D:   induction prefix with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa [stmtListTouchesUnsupportedContractSurface] using
-- SORRY'D:         (Bool.or_eq_false.mp hsurface).1
-- SORRY'D:   | cons head rest ih =>
-- SORRY'D:       simp [stmtListTouchesUnsupportedContractSurface] at hsurface
-- SORRY'D:       exact ih hsurface.2

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
  induction stmts generalizing scope with
  | nil =>
      simpa using hmem
  | cons stmt rest ih =>
      exact ih (mem_stmtNextScope_of_mem_scope hmem)

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
    FunctionBody.exprBoundNamesInScope expr scope := by sorry
-- SORRY'D:   induction hcore with
-- SORRY'D:   | literal =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:   | param name0 =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp [validateScopedExprIdentifiers] at hvalidate
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:       subst name
-- SORRY'D:       exact hparamsInScope name0 hvalidate
-- SORRY'D:   | localVar name0 =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp [validateScopedExprIdentifiers] at hvalidate
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:       subst name
-- SORRY'D:       exact hlocalsInScope name0 hvalidate
-- SORRY'D:   | caller | contractAddress | msgValue | blockTimestamp | blockNumber | chainid =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:   | add hL hR ihL ihR
-- SORRY'D:   | sub hL hR ihL ihR
-- SORRY'D:   | mul hL hR ihL ihR
-- SORRY'D:   | div hL hR ihL ihR
-- SORRY'D:   | mod hL hR ihL ihR
-- SORRY'D:   | eq hL hR ihL ihR
-- SORRY'D:   | lt hL hR ihL ihR
-- SORRY'D:   | gt hL hR ihL ihR
-- SORRY'D:   | ge hL hR ihL ihR
-- SORRY'D:   | le hL hR ihL ihR =>
-- SORRY'D:       simp [validateScopedExprIdentifiers] at hvalidate
-- SORRY'D:       intro name hmem
-- SORRY'D:       rcases List.mem_append.mp hmem with hmem | hmem
-- SORRY'D:       · exact ihL hvalidate.1 hparamsInScope hlocalsInScope _ hmem
-- SORRY'D:       · exact ihR hvalidate.2 hparamsInScope hlocalsInScope _ hmem
-- SORRY'D:   | logicalNot h ih =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa [FunctionBody.exprBoundNames] using
-- SORRY'D:         ih (by simpa [validateScopedExprIdentifiers] using hvalidate)
-- SORRY'D:           hparamsInScope hlocalsInScope name hmem
-- SORRY'D:   | logicalAnd hL hR ihL ihR
-- SORRY'D:   | logicalOr hL hR ihL ihR =>
-- SORRY'D:       simp [validateScopedExprIdentifiers] at hvalidate
-- SORRY'D:       intro name hmem
-- SORRY'D:       rcases List.mem_append.mp hmem with hmem | hmem
-- SORRY'D:       · exact ihL hvalidate.2.1 hparamsInScope hlocalsInScope _ hmem
-- SORRY'D:       · exact ihR hvalidate.2.2 hparamsInScope hlocalsInScope _ hmem

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
    StmtListScopeDiscipline fieldNames scope stmts := by sorry
-- SORRY'D:   induction hcore generalizing localScope scope finalScope with
-- SORRY'D:   | nil =>
-- SORRY'D:       cases hvalidate
-- SORRY'D:       exact StmtListScopeDiscipline.nil
-- SORRY'D:   | letVar hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, _, _, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.letVar
-- SORRY'D:         hvalueCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             simp at hmem
-- SORRY'D:             rcases hmem with rfl | hmem
-- SORRY'D:             · exact List.mem_append.mpr <| Or.inl <| by simp [stmtNextScope, collectStmtNames]
-- SORRY'D:             · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | assignVar hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨_, hvalueValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.assignVar
-- SORRY'D:         hvalueCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | require hcondCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hcondValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.require
-- SORRY'D:         hcondCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hcondCore hcondValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | return_ hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.return_
-- SORRY'D:         hvalueCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with rfl
-- SORRY'D:       refine StmtListScopeDiscipline.stop ?_
-- SORRY'D:       exact ih hrestValidate hparamsInScope hlocalsInScope
-- SORRY'D:   | setStorage hfield hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.setStorage
-- SORRY'D:         hfield
-- SORRY'D:         hvalueCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | setStorageAddr hfield hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.setStorageAddr
-- SORRY'D:         hfield
-- SORRY'D:         hvalueCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ih hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
-- SORRY'D:   | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hcondValidate, hthenValidate, helseValidate, rfl⟩
-- SORRY'D:       exact StmtListScopeDiscipline.ite
-- SORRY'D:         hcondCore
-- SORRY'D:         (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:           hcondCore hcondValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ihThen hthenValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ihElse helseValidate hparamsInScope hlocalsInScope)
-- SORRY'D:         (ihRest hrestValidate
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
-- SORRY'D:           (by
-- SORRY'D:             intro other hmem
-- SORRY'D:             exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))

-- TYPESIG_SORRY: theorem stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
-- TYPESIG_SORRY:     {spec : FunctionSpec}
-- TYPESIG_SORRY:     {fieldNames : List String}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     (hcore : StmtListScopeCore fieldNames prefix)
-- TYPESIG_SORRY:     (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
-- TYPESIG_SORRY:     (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
-- TYPESIG_SORRY:     (hbody : spec.body = prefix ++ suffix) :
-- TYPESIG_SORRY:     StmtListScopeDiscipline fieldNames (spec.params.map (·.name)) prefix := by sorry
-- SORRY'D:   rcases validateFunctionIdentifierReferences_prefix_ok hvalidate hbody with
-- SORRY'D:     ⟨finalLocalScope, hprefixValidate⟩
-- SORRY'D:   apply stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
-- SORRY'D:     (paramScope := paramScopeNames spec.params)
-- SORRY'D:     (dynamicParams := dynamicParamBases spec.params)
-- SORRY'D:     (localScope := [])
-- SORRY'D:     (finalScope := finalLocalScope)
-- SORRY'D:     hcore
-- SORRY'D:     hprefixValidate
-- SORRY'D:   · intro name hmem
-- SORRY'D:     rw [hparamScope] at hmem
-- SORRY'D:     simpa using hmem
-- SORRY'D:   · intro name hmem
-- SORRY'D:     simp at hmem

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
    ∀ name, name ∈ finalScope → name ∈ List.foldl stmtNextScope scope stmts := by sorry
-- SORRY'D:   induction hcore generalizing localScope scope finalScope with
-- SORRY'D:   | nil =>
-- SORRY'D:       cases hvalidate
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa using hmem
-- SORRY'D:   | letVar hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, _, _, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           simp at hname
-- SORRY'D:           rcases hname with rfl | hname
-- SORRY'D:           · simp [stmtNextScope, collectStmtNames]
-- SORRY'D:           · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | assignVar hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨_, hvalueValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | require hcondCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hcondValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | return_ hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with rfl
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate hparamsInScope hlocalsInScope other hmem
-- SORRY'D:   | setStorage hfield hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | setStorageAddr hfield hvalueCore hrest ih =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hvalueValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ih hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem
-- SORRY'D:   | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
-- SORRY'D:       rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
-- SORRY'D:         ⟨nextLocalScope, hstmt, hrestValidate⟩
-- SORRY'D:       simp [validateScopedStmtIdentifiers] at hstmt
-- SORRY'D:       rcases hstmt with ⟨hcondValidate, hthenValidate, helseValidate, rfl⟩
-- SORRY'D:       intro other hmem
-- SORRY'D:       exact ihRest hrestValidate
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
-- SORRY'D:         (by
-- SORRY'D:           intro name hname
-- SORRY'D:           exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
-- SORRY'D:         other hmem

-- TYPESIG_SORRY: private theorem exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
-- TYPESIG_SORRY:     {spec : FunctionSpec}
-- TYPESIG_SORRY:     {fieldNames : List String}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     (hprefixCore : StmtListScopeCore fieldNames prefix)
-- TYPESIG_SORRY:     (hvalueCore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
-- TYPESIG_SORRY:     (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
-- TYPESIG_SORRY:     (hbody : spec.body = prefix ++ .setStorage fieldName value :: suffix) :
-- TYPESIG_SORRY:     FunctionBody.exprBoundNamesInScope
-- TYPESIG_SORRY:       value
-- TYPESIG_SORRY:       (List.foldl stmtNextScope (spec.params.map (·.name)) prefix) := by sorry
-- SORRY'D:   rcases validateFunctionIdentifierReferences_prefix_stmt_ok hvalidate hbody with
-- SORRY'D:     ⟨localScope, nextScope, hprefixValidate, hstmtValidate⟩
-- SORRY'D:   simp [validateScopedStmtIdentifiers] at hstmtValidate
-- SORRY'D:   rcases hstmtValidate with ⟨hvalueValidate, rfl⟩
-- SORRY'D:   apply exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
-- SORRY'D:     (paramScope := paramScopeNames spec.params)
-- SORRY'D:     (dynamicParams := dynamicParamBases spec.params)
-- SORRY'D:     (localScope := localScope)
-- SORRY'D:     (scope := List.foldl stmtNextScope (spec.params.map (·.name)) prefix)
-- SORRY'D:     hvalueCore
-- SORRY'D:     hvalueValidate
-- SORRY'D:   · intro name hname
-- SORRY'D:     rw [hparamScope] at hname
-- SORRY'D:     exact mem_stmtNextScopeList_of_mem_scope hname
-- SORRY'D:   · intro name hname
-- SORRY'D:     exact scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
-- SORRY'D:       hprefixCore
-- SORRY'D:       hprefixValidate
-- SORRY'D:       (by
-- SORRY'D:         intro other hmem
-- SORRY'D:         rw [hparamScope] at hmem
-- SORRY'D:         simpa using hmem)
-- SORRY'D:       (by
-- SORRY'D:         intro other hmem
-- SORRY'D:         simp at hmem)
-- SORRY'D:       name
-- SORRY'D:       hname

private theorem collectExprNames_mem_exprBoundNames_of_core
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by sorry
-- SORRY'D:   induction hcore with
-- SORRY'D:   | literal value =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp at hmem
-- SORRY'D:   | param name0 =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
-- SORRY'D:   | localVar name0 =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
-- SORRY'D:   | caller | contractAddress | msgValue | blockTimestamp | blockNumber | chainid =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simp at hmem
-- SORRY'D:   | add hL hR ihL ihR
-- SORRY'D:   | sub hL hR ihL ihR
-- SORRY'D:   | mul hL hR ihL ihR
-- SORRY'D:   | div hL hR ihL ihR
-- SORRY'D:   | mod hL hR ihL ihR
-- SORRY'D:   | eq hL hR ihL ihR
-- SORRY'D:   | lt hL hR ihL ihR
-- SORRY'D:   | gt hL hR ihL ihR
-- SORRY'D:   | ge hL hR ihL ihR
-- SORRY'D:   | le hL hR ihL ihR
-- SORRY'D:   | logicalAnd hL hR ihL ihR
-- SORRY'D:   | logicalOr hL hR ihL ihR =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       rcases List.mem_append.mp hmem with hmem | hmem
-- SORRY'D:       · exact List.mem_append.mpr <| Or.inl <| ihL _ hmem
-- SORRY'D:       · exact List.mem_append.mpr <| Or.inr <| ihR _ hmem
-- SORRY'D:   | logicalNot h ih =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa [collectExprNames, FunctionBody.exprBoundNames] using ih _ hmem

private theorem stmtListScopeDiscipline_scope_names
    {fieldNames : List String}
    {scope : List String}
    {stmts : List Stmt}
    (hdisc : StmtListScopeDiscipline fieldNames scope stmts) :
    ∀ name, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈
        (scope ++ collectStmtListBindNames stmts ++
          collectStmtListAssignedNames stmts ++ fieldNames) := by sorry
-- SORRY'D:   induction hdisc with
-- SORRY'D:   | nil =>
-- SORRY'D:       intro name hmem
-- SORRY'D:       simpa using hmem
-- SORRY'D:   | letVar hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hname | htail
-- SORRY'D:       · exact Or.inr <| Or.inl hname
-- SORRY'D:       rcases htail with hvalue | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
-- SORRY'D:       · exact Or.inr <| Or.inr htail
-- SORRY'D:   | assignVar hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hname | htail
-- SORRY'D:       · exact Or.inr <| Or.inr <| Or.inl hname
-- SORRY'D:       rcases htail with hvalue | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
-- SORRY'D:       · exact Or.inr <| Or.inr <| Or.inr htail
-- SORRY'D:   | require hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hcond | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
-- SORRY'D:       · exact Or.inr htail
-- SORRY'D:   | return_ hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hvalue | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
-- SORRY'D:       · exact Or.inr htail
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       simpa [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] using ih other hmem
-- SORRY'D:   | setStorage hfield hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hfieldMem | htail
-- SORRY'D:       · exact Or.inr <| Or.inr <| Or.inr <| by simpa using hfieldMem
-- SORRY'D:       rcases htail with hvalue | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
-- SORRY'D:       · exact Or.inr htail
-- SORRY'D:   | setStorageAddr hfield hcore hinScope hrest ih =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ih other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hfieldMem | htail
-- SORRY'D:       · exact Or.inr <| Or.inr <| Or.inr <| by simpa using hfieldMem
-- SORRY'D:       rcases htail with hvalue | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
-- SORRY'D:       · exact Or.inr htail
-- SORRY'D:   | ite hcore hinScope hthen helse hrest ihThen ihElse ihRest =>
-- SORRY'D:       intro other hmem
-- SORRY'D:       have htail := ihRest other hmem
-- SORRY'D:       simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
-- SORRY'D:         collectStmtListAssignedNames] at htail ⊢
-- SORRY'D:       rcases htail with hcond | htail
-- SORRY'D:       · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
-- SORRY'D:       rcases htail with hthenMem | htail
-- SORRY'D:       · have hthenNames :=
-- SORRY'D:           ihThen other (by
-- SORRY'D:             simpa using (List.mem_append.mpr (Or.inl hthenMem)))
-- SORRY'D:         simpa [collectStmtListBindNames, collectStmtListAssignedNames] using hthenNames
-- SORRY'D:       rcases htail with helseMem | htail
-- SORRY'D:       · have helseNames :=
-- SORRY'D:           ihElse other (by
-- SORRY'D:             simpa using (List.mem_append.mpr (Or.inl helseMem)))
-- SORRY'D:         simpa [collectStmtListBindNames, collectStmtListAssignedNames] using helseNames
-- SORRY'D:       · exact Or.inr htail

-- TYPESIG_SORRY: theorem compiledStmtStep_letVar
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.letVar name value) [YulStmt.let_ name valueIR] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hvalueIR]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let slack := sizeOf [YulStmt.let_ name valueIR] - [YulStmt.let_ name valueIR].length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf [YulStmt.let_ name valueIR] + wholeExtraFuel + 1 =
-- SORRY'D:           [YulStmt.let_ name valueIR].length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack] using hslack
-- SORRY'D:       omega
-- SORRY'D:     rcases FunctionBody.execIRStmts_compiled_let_core_append_wholeFuel_of_scope
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (runtime := runtime)
-- SORRY'D:         (state := state)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (name := name)
-- SORRY'D:         (value := value)
-- SORRY'D:         (tailIR := [])
-- SORRY'D:         (extraFuel := wholeExtraFuel)
-- SORRY'D:         hcore hexact hinScope hscope hbounded hruntime with
-- SORRY'D:       ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:     rw [hvalueIR] at hvalueIR'
-- SORRY'D:     injection hvalueIR' with hEq
-- SORRY'D:     subst hEq
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt]
-- SORRY'D:     · simpa [hwholeFuel] using hwhole
-- SORRY'D:     · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
-- SORRY'D:         And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

-- TYPESIG_SORRY: theorem compiledStmtStep_assignVar
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {name : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.assignVar name value) [YulStmt.assign name valueIR] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hvalueIR]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let slack := sizeOf [YulStmt.assign name valueIR] - [YulStmt.assign name valueIR].length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf [YulStmt.assign name valueIR] + wholeExtraFuel + 1 =
-- SORRY'D:           [YulStmt.assign name valueIR].length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack] using hslack
-- SORRY'D:       omega
-- SORRY'D:     rcases FunctionBody.execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (runtime := runtime)
-- SORRY'D:         (state := state)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (name := name)
-- SORRY'D:         (value := value)
-- SORRY'D:         (tailIR := [])
-- SORRY'D:         (extraFuel := wholeExtraFuel)
-- SORRY'D:         hcore hexact hinScope hscope hbounded hruntime with
-- SORRY'D:       ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:     rw [hvalueIR] at hvalueIR'
-- SORRY'D:     injection hvalueIR' with hEq
-- SORRY'D:     subst hEq
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt]
-- SORRY'D:     · simpa [hwholeFuel] using hwhole
-- SORRY'D:     · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
-- SORRY'D:         And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

-- TYPESIG_SORRY: theorem compiledStmtStep_require
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {cond : Expr}
-- TYPESIG_SORRY:     {message : String}
-- TYPESIG_SORRY:     {failCond : YulExpr}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore cond)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
-- TYPESIG_SORRY:     (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.require cond message)
-- TYPESIG_SORRY:       [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hfailCompile]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let slack :=
-- SORRY'D:       sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] -
-- SORRY'D:         [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] + wholeExtraFuel + 1 =
-- SORRY'D:           [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack] using hslack
-- SORRY'D:       omega
-- SORRY'D:     by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
-- SORRY'D:     · rcases FunctionBody.execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (cond := cond)
-- SORRY'D:           (message := message)
-- SORRY'D:           (tailIR := [])
-- SORRY'D:           (extraFuel := wholeExtraFuel)
-- SORRY'D:           hcore hexact hinScope hscope hbounded hruntime hcondZero with
-- SORRY'D:         ⟨failCond', revState, hfailCompile', hwhole⟩
-- SORRY'D:       rw [hfailCompile] at hfailCompile'
-- SORRY'D:       injection hfailCompile' with hEq
-- SORRY'D:       subst hEq
-- SORRY'D:       refine ⟨_, _, ?_⟩
-- SORRY'D:       · simp [SourceSemantics.execStmt, hcondZero]
-- SORRY'D:       · simpa [hwholeFuel] using hwhole
-- SORRY'D:       · simp [stmtStepMatchesIRExec]
-- SORRY'D:     · have hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0 := hcondZero
-- SORRY'D:       have hwhole :=
-- SORRY'D:         FunctionBody.execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (cond := cond)
-- SORRY'D:           (message := message)
-- SORRY'D:           (tailIR := [])
-- SORRY'D:           (extraFuel := wholeExtraFuel)
-- SORRY'D:           hcore hexact hinScope hscope hbounded hruntime hcondNeZero
-- SORRY'D:       refine ⟨_, _, ?_⟩
-- SORRY'D:       · simp [SourceSemantics.execStmt, hcondNeZero]
-- SORRY'D:       · simpa [hwholeFuel] using hwhole
-- SORRY'D:       · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
-- SORRY'D:           And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope

-- TYPESIG_SORRY: theorem compiledStmtStep_return
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.return value)
-- TYPESIG_SORRY:       [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- TYPESIG_SORRY:       , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hvalueIR]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let compiledIR :=
-- SORRY'D:       [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
-- SORRY'D:       , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]
-- SORRY'D:     let slack := sizeOf compiledIR - compiledIR.length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf compiledIR + wholeExtraFuel + 1 =
-- SORRY'D:           compiledIR.length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack, compiledIR]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack, compiledIR] using hslack
-- SORRY'D:       omega
-- SORRY'D:     rcases FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (runtime := runtime)
-- SORRY'D:         (state := state)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (value := value)
-- SORRY'D:         (tailIR := [])
-- SORRY'D:         (extraFuel := wholeExtraFuel)
-- SORRY'D:         hcore hexact hinScope hbounded
-- SORRY'D:         (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
-- SORRY'D:         hruntime with
-- SORRY'D:       ⟨valueIR', hvalueIR', hwhole⟩
-- SORRY'D:     rw [hvalueIR] at hvalueIR'
-- SORRY'D:     injection hvalueIR' with hEq
-- SORRY'D:     subst hEq
-- SORRY'D:     let retVal := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:     let retState := { state with memory := fun o => if o = 0 then retVal else state.memory o }
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt]
-- SORRY'D:     · simpa [hwholeFuel, compiledIR, retVal, retState] using hwhole
-- SORRY'D:     · refine ⟨rfl, ?_⟩
-- SORRY'D:       exact FunctionBody.runtimeStateMatchesIR_setMemory hruntime 0 retVal

-- TYPESIG_SORRY: theorem compiledStmtStep_stop
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String} :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope .stop [YulStmt.expr (YulExpr.call "stop" [])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let compiledIR := [YulStmt.expr (YulExpr.call "stop" [])]
-- SORRY'D:     let slack := sizeOf compiledIR - compiledIR.length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf compiledIR + wholeExtraFuel + 1 =
-- SORRY'D:           compiledIR.length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack, compiledIR]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack, compiledIR] using hslack
-- SORRY'D:       omega
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt]
-- SORRY'D:     · simpa [compiledIR, hwholeFuel] using
-- SORRY'D:         (FunctionBody.execIRStmts_compiled_stop_core_append_wholeFuel
-- SORRY'D:           (state := state) (tailIR := []) (extraFuel := wholeExtraFuel))
-- SORRY'D:     · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using hruntime

private theorem encodeStorageAt_writeUintSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ slot) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world [slot] value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots, hneq]

private theorem encodeStorageAt_writeUintSlots_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slots : List Nat}
    {query value : Nat}
    (hnotMem : query ∉ slots) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world slots value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots,
-- SORRY'D:     List.contains_eq_false.mpr hnotMem]

private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key query value : Nat}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintKeyedMappingSlots,
-- SORRY'D:     Compiler.Proofs.abstractStoreMappingEntry_eq, Compiler.Proofs.abstractMappingSlot_eq_solidity,
-- SORRY'D:     hneq]

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
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeAddressKeyedMappingChainSlots,
-- SORRY'D:     SourceSemantics.mappingSlotChain, hneq]

private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key + wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeAddressKeyedMappingWordSlots,
-- SORRY'D:     List.contains_eq_true, hneq]

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
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt,
-- SORRY'D:     SourceSemantics.writeAddressKeyedMappingPackedWordSlots,
-- SORRY'D:     List.contains_eq_true, hneq]

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
    (seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 none)) ≠ none := by sorry
-- SORRY'D:   induction seen with
-- SORRY'D:   | nil =>
-- SORRY'D:       cases hmem
-- SORRY'D:   | cons entry rest ih =>
-- SORRY'D:       simp at hmem ⊢
-- SORRY'D:       by_cases hEq : entry.1 = slot
-- SORRY'D:       · subst hEq
-- SORRY'D:         simp [packedSlotsConflict]
-- SORRY'D:       · simp [hEq, ih hmem]

private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hcurrent : slot ∈ current.map (fun entry => entry.1))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by sorry
-- SORRY'D:   induction current generalizing seen with
-- SORRY'D:   | nil =>
-- SORRY'D:       cases hcurrent
-- SORRY'D:   | cons entry rest ih =>
-- SORRY'D:       simp at hcurrent
-- SORRY'D:       have hpnone : entry.2.2 = none := hunpacked entry.2.2 (by simp)
-- SORRY'D:       rcases hcurrent with hEq | hrest
-- SORRY'D:       · subst hEq
-- SORRY'D:         have hfindSeen :
-- SORRY'D:             (seen.find? (fun seenEntry => seenEntry.1 == entry.1 &&
-- SORRY'D:               packedSlotsConflict seenEntry.2.2 entry.2.2)) ≠ none := by
-- SORRY'D:           simpa [hpnone] using list_findSlotPackedNone_ne_none hseen
-- SORRY'D:         intro hnone
-- SORRY'D:         simp [firstInFieldConflictCopy, hpnone, hfindSeen] at hnone
-- SORRY'D:       · have hunpackedRest :
-- SORRY'D:             ∀ packed ∈ rest.map (fun restEntry => restEntry.2.2), packed = none := by
-- SORRY'D:           intro packed hmem
-- SORRY'D:           exact hunpacked packed (by simp [hmem])
-- SORRY'D:         intro hnone
-- SORRY'D:         cases hfind : seen.find? (fun seenEntry => seenEntry.1 == entry.1 &&
-- SORRY'D:             packedSlotsConflict seenEntry.2.2 entry.2.2)
-- SORRY'D:         · have htailNone :
-- SORRY'D:               firstInFieldConflictCopy ((entry.1, entry.2.1, entry.2.2) :: seen) rest = none := by
-- SORRY'D:             simpa [firstInFieldConflictCopy, hfind] using hnone
-- SORRY'D:           have hseen' :
-- SORRY'D:               slot ∈ (((entry.1, entry.2.1, entry.2.2) :: seen).map (fun seenEntry => seenEntry.1)) := by
-- SORRY'D:             simp [hseen]
-- SORRY'D:           exact (ih hseen' hrest hunpackedRest) htailNone
-- SORRY'D:         · simp [firstInFieldConflictCopy, hfind] at hnone

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
    firstFieldWriteSlotConflictCopyFrom seen idx fields ≠ none := by sorry
-- SORRY'D:   induction fields generalizing seen idx with
-- SORRY'D:   | nil =>
-- SORRY'D:       cases hfind
-- SORRY'D:   | cons field rest ih =>
-- SORRY'D:       by_cases hname : field.name == fieldName
-- SORRY'D:       · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
-- SORRY'D:         injection hfind with hf hslotEq
-- SORRY'D:         subst hf
-- SORRY'D:         subst hslotEq
-- SORRY'D:         injection hwrite with hwriteEq
-- SORRY'D:         subst hwriteEq
-- SORRY'D:         have hcurrent :
-- SORRY'D:             targetSlot ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
-- SORRY'D:           simpa [fieldWriteEntriesAt] using hslot
-- SORRY'D:         have hunpackedCurrent :
-- SORRY'D:             ∀ packed ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.2.2), packed = none := by
-- SORRY'D:           intro packed hmem
-- SORRY'D:           simpa [fieldWriteEntriesAt, hunpacked] using hmem
-- SORRY'D:         exact firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
-- SORRY'D:           hseen hcurrent hunpackedCurrent
-- SORRY'D:       · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
-- SORRY'D:         intro hnone
-- SORRY'D:         cases hfirst : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field)
-- SORRY'D:         · have htailNone :
-- SORRY'D:               firstFieldWriteSlotConflictCopyFrom
-- SORRY'D:                 ((fieldWriteEntriesAt idx field).reverse ++ seen)
-- SORRY'D:                 (idx + 1)
-- SORRY'D:                 rest = none := by
-- SORRY'D:             simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnone
-- SORRY'D:           have hseen' :
-- SORRY'D:               targetSlot ∈
-- SORRY'D:                 (((fieldWriteEntriesAt idx field).reverse ++ seen).map
-- SORRY'D:                   (fun entry => entry.1)) := by
-- SORRY'D:             simp [hseen]
-- SORRY'D:           exact (ih hseen' hfind hwrite hslot hunpacked) htailNone
-- SORRY'D:         · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnone

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
  exact
    firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
      hseen hfind hwrite (by simp) hunpacked

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
    findResolvedFieldAtSlotCopy fields targetSlot = some f := by sorry
-- SORRY'D:   have hnoConflictCopy :
-- SORRY'D:       firstFieldWriteSlotConflictCopyFrom [] 0 fields = none := by
-- SORRY'D:     simpa [firstFieldWriteSlotConflict, firstFieldWriteSlotConflictCopyFrom,
-- SORRY'D:       fieldWriteEntriesAt, firstInFieldConflictCopy] using hnoConflict
-- SORRY'D:   have hfindCopy :
-- SORRY'D:       findFieldWithResolvedSlotCopyFrom fields 0 fieldName = some (f, slot) := by
-- SORRY'D:     simpa [findFieldWithResolvedSlot, findFieldWithResolvedSlotCopyFrom] using hfind
-- SORRY'D:   have hwriteCopy :
-- SORRY'D:       findFieldWriteSlotsCopyFrom fields 0 fieldName = some writeSlots := by
-- SORRY'D:     simpa [findFieldWriteSlots, findFieldWriteSlotsCopyFrom] using hwrite
-- SORRY'D:   have hresolved :
-- SORRY'D:       findResolvedFieldAtSlotCopyFrom fields 0 targetSlot = some f := by
-- SORRY'D:     induction fields generalizing targetSlot with
-- SORRY'D:     | nil =>
-- SORRY'D:         cases hfindCopy
-- SORRY'D:     | cons field rest ih =>
-- SORRY'D:         by_cases hname : field.name == fieldName
-- SORRY'D:         · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
-- SORRY'D:             hfindCopy hwriteCopy
-- SORRY'D:           injection hfindCopy with hf hslotEq
-- SORRY'D:           subst hf
-- SORRY'D:           subst hslotEq
-- SORRY'D:           injection hwriteCopy with hwriteEq
-- SORRY'D:           subst hwriteEq
-- SORRY'D:           rcases List.mem_cons.mp hslot with htargetEq | htargetAlias
-- SORRY'D:           · simp [findResolvedFieldAtSlotCopyFrom, htargetEq]
-- SORRY'D:           · have hcontains : field.aliasSlots.contains targetSlot = true :=
-- SORRY'D:               List.contains_eq_true.mpr htargetAlias
-- SORRY'D:             simp [findResolvedFieldAtSlotCopyFrom, hcontains]
-- SORRY'D:         · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
-- SORRY'D:             hfindCopy hwriteCopy
-- SORRY'D:           cases hfirst : firstInFieldConflictCopy [] (fieldWriteEntriesAt 0 field)
-- SORRY'D:           · have htailNoConflict :
-- SORRY'D:                 firstFieldWriteSlotConflictCopyFrom
-- SORRY'D:                   (fieldWriteEntriesAt 0 field).reverse
-- SORRY'D:                   1
-- SORRY'D:                   rest = none := by
-- SORRY'D:               simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnoConflictCopy
-- SORRY'D:             have hheadNotOwn :
-- SORRY'D:                 targetSlot ∉ (fieldWriteEntriesAt 0 field).map (fun entry => entry.1) := by
-- SORRY'D:               intro hmem
-- SORRY'D:               have hmemRev :
-- SORRY'D:                   targetSlot ∈ ((fieldWriteEntriesAt 0 field).reverse.map (fun entry => entry.1)) := by
-- SORRY'D:                 simpa [List.map_reverse] using (List.mem_reverse.mpr hmem)
-- SORRY'D:               exact
-- SORRY'D:                 (firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
-- SORRY'D:                   hmemRev hfindCopy hwriteCopy hslot hunpacked) htailNoConflict
-- SORRY'D:             have hresolvedNe : field.slot.getD 0 ≠ targetSlot := by
-- SORRY'D:               have hheadNotOwn' := hheadNotOwn
-- SORRY'D:               simp [fieldWriteEntriesAt] at hheadNotOwn'
-- SORRY'D:               exact hheadNotOwn'.1
-- SORRY'D:             have haliasNotMem : targetSlot ∉ field.aliasSlots := by
-- SORRY'D:               have hheadNotOwn' := hheadNotOwn
-- SORRY'D:               simp [fieldWriteEntriesAt] at hheadNotOwn'
-- SORRY'D:               exact hheadNotOwn'.2
-- SORRY'D:             have haliasNe : field.aliasSlots.contains targetSlot = false :=
-- SORRY'D:               List.contains_eq_false.mpr haliasNotMem
-- SORRY'D:             simpa [findResolvedFieldAtSlotCopyFrom, hresolvedNe, haliasNe] using
-- SORRY'D:               ih (targetSlot := targetSlot) htailNoConflict hfindCopy hwriteCopy hslot hunpacked
-- SORRY'D:           · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnoConflictCopy
-- SORRY'D:   simpa [findResolvedFieldAtSlotCopy, findResolvedFieldAtSlotCopyFrom] using hresolved

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
  exact
    findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
      hnoConflict hfind hwrite (by simp) hunpacked

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
      encodeStorageAtCopy fields world slot := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, encodeStorageAtCopy,
-- SORRY'D:     findResolvedFieldAtSlotCopy, findDynamicArrayElementAtSlotCopy]

private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hnotAddr, hnotDyn]

private theorem encodeStorageAt_eq_storageAddr_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storageAddr slot).val := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, haddr, hnotDyn]

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
      (Compiler.Proofs.abstractMappingSlot slot key) = value := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeUintKeyedMappingSlots, Compiler.Proofs.abstractStoreMappingEntry_eq,
-- SORRY'D:     Compiler.Proofs.abstractMappingSlot_eq_solidity]

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
      (SourceSemantics.mappingSlotChain slot keys) = value := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeAddressKeyedMappingChainSlots, SourceSemantics.mappingSlotChain]

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
      (Compiler.Proofs.abstractMappingSlot slot key + wordOffset) = value := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeAddressKeyedMappingWordSlots]

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
        packed := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots,
-- SORRY'D:     SourceSemantics.packedWordWrite]

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
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeAddressKeyedMapping2Slots,
-- SORRY'D:     Compiler.Proofs.abstractStoreMappingEntry_eq, Compiler.Proofs.abstractMappingSlot_eq_solidity,
-- SORRY'D:     hneq]

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
        key2) = value := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeAddressKeyedMapping2Slots, Compiler.Proofs.abstractStoreMappingEntry_eq,
-- SORRY'D:     Compiler.Proofs.abstractMappingSlot_eq_solidity]

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
      SourceSemantics.encodeStorageAt fields world query := by sorry
-- SORRY'D:   simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeAddressKeyedMapping2WordSlots, hneq]

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
        key2 + wordOffset) = value := by sorry
-- SORRY'D:   rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hdyn]
-- SORRY'D:   simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]

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
      if slots.contains query then value else storage query := by sorry
-- SORRY'D:   induction slots generalizing storage with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [abstractStoreStorageOrMappingMany]
-- SORRY'D:   | cons slot rest ih =>
-- SORRY'D:       by_cases hEq : query = slot
-- SORRY'D:       · subst hEq
-- SORRY'D:         simp [abstractStoreStorageOrMappingMany, Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:       · simp [abstractStoreStorageOrMappingMany, ih,
-- SORRY'D:           Compiler.Proofs.abstractStoreStorageOrMapping_eq, hEq]

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
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = slot
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage,
-- SORRY'D:       encodeStorageAt_eq_storage_of_resolvedSlot hresolved hnotAddr hnotDyn]
-- SORRY'D:     simp [SourceSemantics.writeUintSlots]
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeUintSlots_singleton_other]

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
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = slot
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage,
-- SORRY'D:       encodeStorageAt_eq_storageAddr_of_resolvedSlot hresolved haddr hnotDyn]
-- SORRY'D:     simp [SourceSemantics.writeAddressSlots]
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, SourceSemantics.writeAddressSlots]

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
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hmem : query ∈ slots
-- SORRY'D:   · rw [abstractStoreStorageOrMappingMany_eq, hstorage,
-- SORRY'D:       encodeStorageAt_eq_storage_of_resolvedSlot (hresolved query hmem) hnotAddr hnotDyn]
-- SORRY'D:     simp [SourceSemantics.writeUintSlots, List.contains_eq_true.mpr hmem]
-- SORRY'D:   · rw [abstractStoreStorageOrMappingMany_eq, hstorage]
-- SORRY'D:     simp [List.contains_eq_false.mpr hmem, encodeStorageAt_writeUintSlots_other hmem]

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
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = Compiler.Proofs.abstractMappingSlot slot key
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     simp
-- SORRY'D:     exact encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key) (value := value)
-- SORRY'D:       hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreMappingEntry_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
-- SORRY'D:       (world := runtime.world) (slot := slot) (key := key) (query := query) (value := value) hEq]

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
            value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = SourceSemantics.mappingSlotChain slot keys
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simp
-- SORRY'D:     exact encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (keys := keys) (value := value)
-- SORRY'D:       hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_other
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (keys := keys)
-- SORRY'D:       (query := query) (value := value) hEq]

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
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = Compiler.Proofs.abstractMappingSlot slot key
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     simp
-- SORRY'D:     exact encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key) (value := value)
-- SORRY'D:       hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreMappingEntry_eq, hstorage]
-- SORRY'D:     simp [hEq, SourceSemantics.writeAddressKeyedMappingSlots,
-- SORRY'D:       encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
-- SORRY'D:         (world := runtime.world) (slot := slot) (key := key) (query := query) (value := value) hEq]

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
            value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = Compiler.Proofs.abstractMappingSlot slot key + wordOffset
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simp
-- SORRY'D:     exact encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key)
-- SORRY'D:       (wordOffset := wordOffset) (value := value) hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key)
-- SORRY'D:       (wordOffset := wordOffset) (query := query) (value := value) hEq]

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
              packed) } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query = Compiler.Proofs.abstractMappingSlot slot key + wordOffset
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simp [hstorage]
-- SORRY'D:     exact encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key)
-- SORRY'D:       (wordOffset := wordOffset) (packed := packed) (value := value) hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key := key)
-- SORRY'D:       (wordOffset := wordOffset) (packed := packed) (query := query) (value := value) hEq]

-- TYPESIG_SORRY: private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {slot key1 key2 value : Nat}
-- TYPESIG_SORRY:     (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
-- TYPESIG_SORRY:     (hresolved :
-- TYPESIG_SORRY:       findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:         (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:           (Compiler.Proofs.abstractMappingSlot slot key1)
-- TYPESIG_SORRY:           key2) = none)
-- TYPESIG_SORRY:     (hdyn :
-- TYPESIG_SORRY:       findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:         (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:           (Compiler.Proofs.abstractMappingSlot slot key1)
-- TYPESIG_SORRY:           key2) = none) :
-- TYPESIG_SORRY:     FunctionBody.runtimeStateMatchesIR fields
-- TYPESIG_SORRY:       { runtime with
-- TYPESIG_SORRY:           world := SourceSemantics.writeAddressKeyedMapping2Slots runtime.world [slot] key1 key2 value }
-- TYPESIG_SORRY:       { state with
-- TYPESIG_SORRY:           storage := by sorry
-- SORRY'D:             Compiler.Proofs.abstractStoreMappingEntry
-- SORRY'D:               (Compiler.Proofs.abstractStoreMappingEntry state.storage slot key1 0)
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot key1)
-- SORRY'D:               key2
-- SORRY'D:               value } := by
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query =
-- SORRY'D:       Compiler.Proofs.abstractMappingSlot
-- SORRY'D:         (Compiler.Proofs.abstractMappingSlot slot key1)
-- SORRY'D:         key2
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     simp [Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     exact encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world)
-- SORRY'D:       (slot := slot) (key1 := key1) (key2 := key2) (value := value)
-- SORRY'D:       hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreMappingEntry_eq, hstorage]
-- SORRY'D:     simp [hEq, Compiler.Proofs.abstractStoreMappingEntry_eq,
-- SORRY'D:       encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_other (fields := fields)
-- SORRY'D:         (world := runtime.world) (slot := slot) (key1 := key1) (key2 := key2)
-- SORRY'D:         (query := query) (value := value) hEq]

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
            value } := by sorry
-- SORRY'D:   rcases hruntime with
-- SORRY'D:     ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
-- SORRY'D:   funext query
-- SORRY'D:   by_cases hEq : query =
-- SORRY'D:       Compiler.Proofs.abstractMappingSlot
-- SORRY'D:         (Compiler.Proofs.abstractMappingSlot slot key1)
-- SORRY'D:         key2 + wordOffset
-- SORRY'D:   · subst hEq
-- SORRY'D:     rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simp
-- SORRY'D:     exact encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
-- SORRY'D:       (fields := fields) (world := runtime.world)
-- SORRY'D:       (slot := slot) (key1 := key1) (key2 := key2) (wordOffset := wordOffset)
-- SORRY'D:       (value := value) hresolved hdyn
-- SORRY'D:   · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
-- SORRY'D:     simp [hEq, encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
-- SORRY'D:       (fields := fields) (world := runtime.world) (slot := slot) (key1 := key1)
-- SORRY'D:       (key2 := key2) (wordOffset := wordOffset) (query := query) (value := value) hEq]

private theorem bindingsExactlyMatchIRVarsOnScope_writeUintSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  intro name hname
  simpa [IRState.getVar, Compiler.Proofs.abstractStoreStorageOrMapping_eq] using
    hexact name hname

private theorem bindingsExactlyMatchIRVarsOnScope_writeMappingSlot
    {scope : List String}
    {bindings : List (String × Nat)}
    {state : IRState}
    {slot key value : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings state) :
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope bindings
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  intro name hname
  simpa [IRState.getVar, Compiler.Proofs.abstractStoreMappingEntry_eq] using
    hexact name hname

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
  intro name hname
  simpa [IRState.getVar, abstractStoreStorageOrMappingMany_eq] using
    hexact name hname

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
            storage := abstractStoreStorageOrMappingMany state.storage slots value } := by sorry
-- SORRY'D:   induction slots generalizing state fuel with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [execIRStmts, abstractStoreStorageOrMappingMany]
-- SORRY'D:   | cons slot rest ih =>
-- SORRY'D:       let nextState :=
-- SORRY'D:         { state with
-- SORRY'D:             storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value }
-- SORRY'D:       have hstmt :
-- SORRY'D:           execIRStmt (rest.length + fuel + 1) state
-- SORRY'D:             (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name])) =
-- SORRY'D:               .continue nextState := by
-- SORRY'D:         apply execIRStmt_sstore_lit_expr_succ_of_eval
-- SORRY'D:         simpa [evalIRExpr, IRState.getVar, hvalue]
-- SORRY'D:       have hvalueNext : IRState.getVar nextState name = value := by
-- SORRY'D:         simpa [nextState, IRState.getVar] using hvalue
-- SORRY'D:       have htail :=
-- SORRY'D:         ih (fuel := fuel) (state := nextState) (name := name) (value := value) hvalueNext
-- SORRY'D:       simpa [execIRStmts, abstractStoreStorageOrMappingMany, nextState] using htail

-- TYPESIG_SORRY: private theorem execIRStmts_let_then_sstore_lit_ident_slots_continue
-- TYPESIG_SORRY:     (fuel : Nat)
-- TYPESIG_SORRY:     (state : IRState)
-- TYPESIG_SORRY:     (slots : List Nat)
-- TYPESIG_SORRY:     (tempName : String)
-- TYPESIG_SORRY:     (valueIR : YulExpr)
-- TYPESIG_SORRY:     (value : Nat)
-- TYPESIG_SORRY:     (hvalue : evalIRExpr state valueIR = some value) :
-- TYPESIG_SORRY:     execIRStmts (slots.length + fuel + 2) state
-- TYPESIG_SORRY:       (YulStmt.let_ tempName valueIR ::
-- TYPESIG_SORRY:         slots.map (fun slot =>
-- TYPESIG_SORRY:           YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident tempName]))) =
-- TYPESIG_SORRY:       .continue
-- TYPESIG_SORRY:         { state.setVar tempName value with
-- TYPESIG_SORRY:             storage := by sorry
-- SORRY'D:               abstractStoreStorageOrMappingMany
-- SORRY'D:                 (state.setVar tempName value).storage
-- SORRY'D:                 slots
-- SORRY'D:                 value } := by
-- SORRY'D:   have hlet :
-- SORRY'D:       execIRStmt (slots.length + fuel + 1) state
-- SORRY'D:         (YulStmt.let_ tempName valueIR) =
-- SORRY'D:           .continue (state.setVar tempName value) := by
-- SORRY'D:     simp [execIRStmt, hvalue]
-- SORRY'D:   have hslots :=
-- SORRY'D:     execIRStmts_sstore_lit_ident_slots_continue
-- SORRY'D:       fuel
-- SORRY'D:       (state.setVar tempName value)
-- SORRY'D:       slots
-- SORRY'D:       tempName
-- SORRY'D:       value
-- SORRY'D:       (by simp [IRState.getVar])
-- SORRY'D:   simpa [execIRStmts, hlet] using hslots

private theorem execIRStmts_single_block_of_continue
    (fuel : Nat)
    (state next : IRState)
    (body : List YulStmt)
    (hbody : execIRStmts fuel state body = .continue next) :
    execIRStmts (fuel + 2) state [YulStmt.block body] = .continue next := by
  have hblock :
      execIRStmt (fuel + 1) state (YulStmt.block body) = .continue next := by
    simpa [execIRStmt, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbody
  simpa [execIRStmts, hblock]

private theorem compatValue_not_mem_scope_of_reservedPrefix
    {scope : List String}
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope) :
    "__compat_value" ∉ scope := by sorry

private theorem validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : name ∈ spec.fields.map (·.name)) :
    ¬ name.startsWith "__" := by
  rcases List.mem_map.mp hmem with ⟨field, hfieldMem, hfieldName⟩
  subst hfieldName
  exact CompilationModel.validateIdentifierShapes_field_avoidReservedCompilerPrefix hvalidate hfieldMem

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
  intro name hmem
  have hname := hscopeNames name hmem
  have hname' :
      name ∈ fn.params.map (·.name) ∨
      name ∈ collectStmtListBindNames fn.body ∨
      name ∈ collectStmtListAssignedNames fn.body ∨
      name ∈ spec.fields.map (·.name) := by
    simpa [List.mem_append, or_assoc] using hname
  rcases hname' with hparam | hrest
  · exact CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
      hvalidate hfn hparam
  rcases hrest with hlocal | hrest
  · exact CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
      hvalidate hfn hlocal
  rcases hrest with hassign | hfield
  · exact CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
      hvalidate hfn hassign
  · exact validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix hvalidate hfield

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_singleSlot
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (halias : f.aliasSlots = [])
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setStorage fieldName value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
-- SORRY'D:       hfind, halias, hunpacked, hvalueIR]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
-- SORRY'D:     let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:     have hresolvedSlot :
-- SORRY'D:         findResolvedFieldAtSlotCopy fields slot = some f :=
-- SORRY'D:       findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
-- SORRY'D:         hnoConflict hfind hwriteSlots hunpacked
-- SORRY'D:     have heval :=
-- SORRY'D:       FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:         hcore hexact hinScope hbounded
-- SORRY'D:         (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
-- SORRY'D:         hruntime
-- SORRY'D:     rw [hvalueIR] at heval
-- SORRY'D:     have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:       simpa [valueNat] using heval
-- SORRY'D:     have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
-- SORRY'D:       simpa [compiledIR] using hslack
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt, hwriteSlots, valueNat]
-- SORRY'D:     · have hExecStmt :
-- SORRY'D:           execIRStmt (extraFuel + 1) state
-- SORRY'D:             (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
-- SORRY'D:               .continue
-- SORRY'D:                 { state with
-- SORRY'D:                     storage :=
-- SORRY'D:                       Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                         state.storage slot valueNat } :=
-- SORRY'D:         execIRStmt_sstore_lit_expr_succ_of_eval
-- SORRY'D:           extraFuel state slot valueIR valueNat hvalueEval
-- SORRY'D:       simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:     · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:       · exact runtimeStateMatchesIR_writeUintSlot hruntime hresolvedSlot hnotAddr hnotDyn
-- SORRY'D:       · exact bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact

-- TYPESIG_SORRY: private theorem compiledStmtStep_setStorageAddr_singleSlot_preserves
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot fields fieldName =
-- TYPESIG_SORRY:       some ({ name := fieldName, ty := FieldType.address }, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep.Preserves fields scope
-- TYPESIG_SORRY:       (.setStorageAddr fieldName value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hresolvedSlot : findResolvedFieldAtSlotCopy fields slot =
-- SORRY'D:       some { name := fieldName, ty := FieldType.address } :=
-- SORRY'D:     findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
-- SORRY'D:       hnoConflict hfind hwriteSlots (by rfl)
-- SORRY'D:   have heval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcore hexact hinScope hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hvalueIR] at heval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using heval
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, valueNat]
-- SORRY'D:   · have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
-- SORRY'D:             .continue { state with
-- SORRY'D:               storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot valueNat } :=
-- SORRY'D:       execIRStmt_sstore_lit_expr_succ_of_eval
-- SORRY'D:         extraFuel state slot valueIR valueNat hvalueEval
-- SORRY'D:     simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressSlot hruntime hresolvedSlot (by rfl) (by rfl)
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorageAddr_singleSlot
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot fields fieldName =
-- TYPESIG_SORRY:       some ({ name := fieldName, ty := FieldType.address }, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setStorageAddr fieldName value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
-- SORRY'D:       hfind, hwriteSlots, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setStorageAddr_singleSlot_preserves
-- SORRY'D:     hcore hinScope hfind hwriteSlots hnoConflict hvalueIR

-- TYPESIG_SORRY: private theorem compiledStmtStep_mstore_single_preserves
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {offset value : Expr}
-- TYPESIG_SORRY:     {offsetIR valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcoreOffset : FunctionBody.ExprCompileCore offset)
-- TYPESIG_SORRY:     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep.Preserves fields scope
-- TYPESIG_SORRY:       (.mstore offset value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])]
-- SORRY'D:   let offsetNat := SourceSemantics.evalExpr fields runtime offset
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hOffsetEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreOffset hexact hinScopeOffset hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
-- SORRY'D:       hruntime
-- SORRY'D:   have hValueEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hoffsetIR] at hOffsetEval
-- SORRY'D:   rw [hvalueIR] at hValueEval
-- SORRY'D:   have hExecStmt :
-- SORRY'D:       execIRStmt (extraFuel + 1) state
-- SORRY'D:         (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) =
-- SORRY'D:           .continue
-- SORRY'D:             { state with
-- SORRY'D:                 memory := fun o =>
-- SORRY'D:                   if o = offsetNat then valueNat else state.memory o } := by
-- SORRY'D:     simpa [offsetNat, valueNat, execIRStmt, evalIRExprs, hOffsetEval, hValueEval]
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, offsetNat, valueNat]
-- SORRY'D:   · simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · simpa [FunctionBody.runtimeStateMatchesIR] using hruntime
-- SORRY'D:     · simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope] using hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_mstore_single
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {offset value : Expr}
-- TYPESIG_SORRY:     {offsetIR valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcoreOffset : FunctionBody.ExprCompileCore offset)
-- TYPESIG_SORRY:     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.mstore offset value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_mstore_single_preserves
-- SORRY'D:     hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

-- TYPESIG_SORRY: private theorem compiledStmtStep_tstore_single_preserves
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {offset value : Expr}
-- TYPESIG_SORRY:     {offsetIR valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcoreOffset : FunctionBody.ExprCompileCore offset)
-- TYPESIG_SORRY:     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep.Preserves fields scope
-- TYPESIG_SORRY:       (.tstore offset value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])]
-- SORRY'D:   let offsetNat := SourceSemantics.evalExpr fields runtime offset
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hOffsetEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreOffset hexact hinScopeOffset hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
-- SORRY'D:       hruntime
-- SORRY'D:   have hValueEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hoffsetIR] at hOffsetEval
-- SORRY'D:   rw [hvalueIR] at hValueEval
-- SORRY'D:   have hExecStmt :
-- SORRY'D:       execIRStmt (extraFuel + 1) state
-- SORRY'D:         (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) =
-- SORRY'D:           .continue
-- SORRY'D:             { state with
-- SORRY'D:                 transientStorage := fun o =>
-- SORRY'D:                   if o = offsetNat then valueNat else state.transientStorage o } := by
-- SORRY'D:     simpa [offsetNat, valueNat, execIRStmt, evalIRExprs, hOffsetEval, hValueEval]
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, offsetNat, valueNat]
-- SORRY'D:   · simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact FunctionBody.runtimeStateMatchesIR_setTransientStorage hruntime offsetNat valueNat
-- SORRY'D:     · simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope] using hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_tstore_single
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {offset value : Expr}
-- TYPESIG_SORRY:     {offsetIR valueIR : YulExpr}
-- TYPESIG_SORRY:     (hcoreOffset : FunctionBody.ExprCompileCore offset)
-- TYPESIG_SORRY:     (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hoffsetIR : CompilationModel.compileExpr fields .calldata offset = Except.ok offsetIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.tstore offset value)
-- TYPESIG_SORRY:       [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_tstore_single_preserves
-- SORRY'D:     hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr
-- SORRY'D:     (YulExpr.call "sstore"
-- SORRY'D:       [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
-- SORRY'D:   let keyNat := SourceSemantics.evalExpr fields runtime key
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkeySourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey hexact hinScopeKey hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkeyIR] at hkeySourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkeyEval : evalIRExpr state keyIR = some keyNat := by
-- SORRY'D:     simpa [keyNat] using hkeySourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat (by simpa [keyNat] using hkeySourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat, valueNat]
-- SORRY'D:   · have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr
-- SORRY'D:             (YulExpr.call "sstore"
-- SORRY'D:               [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreMappingEntry
-- SORRY'D:                       state.storage slot keyNat valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hkeyEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeUintKeyedMappingSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key value : Expr}
-- TYPESIG_SORRY:     {keyIR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey : FunctionBody.ExprCompileCore key)
-- TYPESIG_SORRY:     (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
-- TYPESIG_SORRY:     (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMappingUint fieldName key value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
-- SORRY'D:       hmapping, hwriteSlots, hkeyIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     keyIRs.foldl
-- SORRY'D:       (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
-- SORRY'D:       (YulExpr.lit slot)
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
-- SORRY'D:   let keyVals := SourceSemantics.evalExprList fields runtime keys
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases eval_compileExprList_core_of_scope
-- SORRY'D:       hcoreKeys hexact hinScopeKeys hbounded hscope hruntime hkeyIRs with
-- SORRY'D:     ⟨resolvedKeys, hkeysEval, hkeyIRVals⟩
-- SORRY'D:   have hkeyValsSome : keyVals = some resolvedKeys := by
-- SORRY'D:     simpa [keyVals] using hkeysEval
-- SORRY'D:   rcases hslotSafety runtime resolvedKeys hkeyValsSome with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   have hWriteSlotEval :
-- SORRY'D:       evalIRExpr state writeSlotExpr =
-- SORRY'D:         some (SourceSemantics.mappingSlotChain slot resolvedKeys) := by
-- SORRY'D:     exact evalIRExpr_mappingSlotChain hkeyIRVals
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyVals, hkeyValsSome, valueNat,
-- SORRY'D:       SourceSemantics.writeAddressKeyedMappingChainSlots]
-- SORRY'D:   · have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                       state.storage
-- SORRY'D:                       (SourceSemantics.mappingSlotChain slot resolvedKeys)
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hWriteSlotEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts] using hExecStmt
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {keys : List Expr}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {keyIRs : List YulExpr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKeys : ∀ expr ∈ keys, FunctionBody.ExprCompileCore expr)
-- TYPESIG_SORRY:     (hinScopeKeys : ∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyVals,
-- TYPESIG_SORRY:         SourceSemantics.evalExprList fields runtime keys = some keyVals →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (SourceSemantics.mappingSlotChain slot keyVals) = none)
-- TYPESIG_SORRY:     (hkeyIRs : CompilationModel.compileExprList fields .calldata keys = Except.ok keyIRs)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMappingChain fieldName keys value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [keyIRs.foldl
-- TYPESIG_SORRY:             (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
-- TYPESIG_SORRY:             (YulExpr.lit slot), valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetMappingChain,
-- SORRY'D:       hmapping, hwriteSlots, hkeyIRs, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKeys hinScopeKeys hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIRs hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr
-- SORRY'D:     (YulExpr.call "sstore"
-- SORRY'D:       [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
-- SORRY'D:   let keyNat := SourceSemantics.evalExpr fields runtime key
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkeySourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey hexact hinScopeKey hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkeyIR] at hkeySourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkeyEval : evalIRExpr state keyIR = some keyNat := by
-- SORRY'D:     simpa [keyNat] using hkeySourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat (by simpa [keyNat] using hkeySourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat, valueNat]
-- SORRY'D:   · have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr
-- SORRY'D:             (YulExpr.call "sstore"
-- SORRY'D:               [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreMappingEntry
-- SORRY'D:                       state.storage slot keyNat valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hkeyEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreMappingEntry_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMappingSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMapping_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key value : Expr}
-- TYPESIG_SORRY:     {keyIR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey : FunctionBody.ExprCompileCore key)
-- TYPESIG_SORRY:     (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
-- TYPESIG_SORRY:     (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMapping fieldName key value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
-- SORRY'D:       hmapping, hwriteSlots, hkeyIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- SORRY'D:     if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
-- SORRY'D:   let keyNat := SourceSemantics.evalExpr fields runtime key
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkeySourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey hexact hinScopeKey hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkeyIR] at hkeySourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkeyEval : evalIRExpr state keyIR = some keyNat := by
-- SORRY'D:     simpa [keyNat] using hkeySourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat (by simpa [keyNat] using hkeySourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat, valueNat]
-- SORRY'D:   · have hWriteSlotEval :
-- SORRY'D:         evalIRExpr state writeSlotExpr =
-- SORRY'D:           some (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) := by
-- SORRY'D:       dsimp [writeSlotExpr]
-- SORRY'D:       by_cases hzero : wordOffset = 0
-- SORRY'D:       · subst hzero
-- SORRY'D:         simp [evalIRExpr, hkeyEval]
-- SORRY'D:       · simp [evalIRExpr, hkeyEval, hzero]
-- SORRY'D:     have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                       state.storage
-- SORRY'D:                       (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset)
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hWriteSlotEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts] using hExecStmt
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key value : Expr}
-- TYPESIG_SORRY:     {wordOffset : Nat}
-- TYPESIG_SORRY:     {keyIR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey : FunctionBody.ExprCompileCore key)
-- TYPESIG_SORRY:     (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- TYPESIG_SORRY:     (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMappingWord fieldName key wordOffset value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- TYPESIG_SORRY:            if wordOffset == 0 then mappingBase
-- TYPESIG_SORRY:            else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
-- SORRY'D:       hmapping, hwriteSlots, hkeyIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- SORRY'D:     if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
-- SORRY'D:   let blockBody :=
-- SORRY'D:     [ YulStmt.let_ "__compat_value" valueIR
-- SORRY'D:     , YulStmt.let_ "__compat_packed"
-- SORRY'D:         (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])
-- SORRY'D:     , YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [writeSlotExpr])
-- SORRY'D:     , YulStmt.let_ "__compat_slot_cleared"
-- SORRY'D:         (YulExpr.call "and"
-- SORRY'D:           [YulExpr.ident "__compat_slot_word",
-- SORRY'D:             YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
-- SORRY'D:     , YulStmt.expr
-- SORRY'D:         (YulExpr.call "sstore"
-- SORRY'D:           [writeSlotExpr,
-- SORRY'D:             YulExpr.call "or"
-- SORRY'D:               [YulExpr.ident "__compat_slot_cleared",
-- SORRY'D:                 YulExpr.call "shl"
-- SORRY'D:                   [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]]) ]
-- SORRY'D:   let compiledIR := [YulStmt.block blockBody]
-- SORRY'D:   let keyNat := SourceSemantics.evalExpr fields runtime key
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   let targetSlot := Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset
-- SORRY'D:   let oldWordNat := state.storage targetSlot
-- SORRY'D:   let storedWordNat := SourceSemantics.packedWordWrite oldWordNat valueNat packed
-- SORRY'D:   have hkeySourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey hexact hinScopeKey hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkeyIR] at hkeySourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkeyEval : evalIRExpr state keyIR = some keyNat := by
-- SORRY'D:     simpa [keyNat] using hkeySourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat (by simpa [keyNat] using hkeySourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
-- SORRY'D:     dsimp [writeSlotExpr, targetSlot]
-- SORRY'D:     by_cases hzero : wordOffset = 0
-- SORRY'D:     · subst hzero
-- SORRY'D:       simp [evalIRExpr, hkeyEval]
-- SORRY'D:     · simp [evalIRExpr, hkeyEval, hzero]
-- SORRY'D:   have hCompatValue :
-- SORRY'D:       execIRStmt (extraFuel + 1) state (YulStmt.let_ "__compat_value" valueIR) =
-- SORRY'D:         .continue (state.setVar "__compat_value" valueNat) := by
-- SORRY'D:     simp [execIRStmt, hvalueEval]
-- SORRY'D:   have hPackedEval :
-- SORRY'D:       evalIRExpr (state.setVar "__compat_value" valueNat)
-- SORRY'D:         (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)]) =
-- SORRY'D:           some (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val := by
-- SORRY'D:     simp [evalIRExpr, IRState.getVar]
-- SORRY'D:   have hCompatPacked :
-- SORRY'D:       execIRStmt (extraFuel + 1) (state.setVar "__compat_value" valueNat)
-- SORRY'D:         (YulStmt.let_ "__compat_packed"
-- SORRY'D:           (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])) =
-- SORRY'D:         .continue
-- SORRY'D:           ((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:             (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) := by
-- SORRY'D:     simp [execIRStmt, hPackedEval]
-- SORRY'D:   have hSlotWordEval :
-- SORRY'D:       evalIRExpr
-- SORRY'D:         (((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:           (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val))
-- SORRY'D:         (YulExpr.call "sload" [writeSlotExpr]) = some oldWordNat := by
-- SORRY'D:     simp [evalIRExpr, hWriteSlotEval, oldWordNat]
-- SORRY'D:   have hCompatSlotWord :
-- SORRY'D:       execIRStmt (extraFuel + 1)
-- SORRY'D:         (((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:           (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val))
-- SORRY'D:         (YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [writeSlotExpr])) =
-- SORRY'D:         .continue
-- SORRY'D:           ((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:             (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:             "__compat_slot_word" oldWordNat) := by
-- SORRY'D:     simp [execIRStmt, hSlotWordEval]
-- SORRY'D:   have hSlotClearedEval :
-- SORRY'D:       evalIRExpr
-- SORRY'D:         ((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:           (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:           "__compat_slot_word" oldWordNat)
-- SORRY'D:         (YulExpr.call "and"
-- SORRY'D:           [YulExpr.ident "__compat_slot_word",
-- SORRY'D:             YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]]) =
-- SORRY'D:           some (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:             (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
-- SORRY'D:     simp [evalIRExpr, IRState.getVar]
-- SORRY'D:   have hCompatSlotCleared :
-- SORRY'D:       execIRStmt (extraFuel + 1)
-- SORRY'D:         ((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:           (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:           "__compat_slot_word" oldWordNat)
-- SORRY'D:         (YulStmt.let_ "__compat_slot_cleared"
-- SORRY'D:           (YulExpr.call "and"
-- SORRY'D:             [YulExpr.ident "__compat_slot_word",
-- SORRY'D:               YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])) =
-- SORRY'D:         .continue
-- SORRY'D:           (((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:             (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:             "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:             (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:               (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) := by
-- SORRY'D:     simp [execIRStmt, hSlotClearedEval]
-- SORRY'D:   have hStoredEval :
-- SORRY'D:       evalIRExpr
-- SORRY'D:         (((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:           (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:           "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:           (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:             (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
-- SORRY'D:         (YulExpr.call "or"
-- SORRY'D:           [YulExpr.ident "__compat_slot_cleared",
-- SORRY'D:             YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]) =
-- SORRY'D:           some storedWordNat := by
-- SORRY'D:     simp [evalIRExpr, IRState.getVar, storedWordNat, SourceSemantics.packedWordWrite]
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat, valueNat, hpacked,
-- SORRY'D:       SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
-- SORRY'D:   · have hBody :
-- SORRY'D:         execIRStmts extraFuel state blockBody =
-- SORRY'D:           .continue
-- SORRY'D:             ((((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:               (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:               "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:               (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:                 (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) with
-- SORRY'D:               storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot storedWordNat) := by
-- SORRY'D:       simp [execIRStmts, blockBody, hCompatValue, hCompatPacked, hCompatSlotWord,
-- SORRY'D:         hCompatSlotCleared, execIRStmt, hWriteSlotEval, hStoredEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     have hWhole :
-- SORRY'D:         execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
-- SORRY'D:           .continue
-- SORRY'D:             ((((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:               (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:               "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:               (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:                 (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) with
-- SORRY'D:               storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot storedWordNat) := by
-- SORRY'D:       simpa [compiledIR] using
-- SORRY'D:         execIRStmts_single_block_of_continue
-- SORRY'D:           extraFuel
-- SORRY'D:           state
-- SORRY'D:           ((((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:             (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:             "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:             (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:               (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) with
-- SORRY'D:             storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot storedWordNat)
-- SORRY'D:           blockBody
-- SORRY'D:           hBody
-- SORRY'D:       simpa [targetSlot, storedWordNat] using hWhole
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · have hruntime1 := FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime
-- SORRY'D:       have hruntime2 := FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime1
-- SORRY'D:       have hruntime3 := FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime2
-- SORRY'D:       have hruntime4 := FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime3
-- SORRY'D:       simpa [targetSlot, storedWordNat] using
-- SORRY'D:         runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := (((((state.setVar "__compat_value" valueNat).setVar "__compat_packed"
-- SORRY'D:             (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)).setVar
-- SORRY'D:             "__compat_slot_word" oldWordNat)).setVar "__compat_slot_cleared"
-- SORRY'D:             (Verity.Core.Uint256.and oldWordNat
-- SORRY'D:               (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val))
-- SORRY'D:           (slot := slot) (key := keyNat) (wordOffset := wordOffset) (packed := packed)
-- SORRY'D:           (value := valueNat) hruntime4 hresolvedNone hdynNone
-- SORRY'D:     · have hexact1 :=
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact hcompatValue
-- SORRY'D:       have hexact2 :=
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact1 hcompatPacked
-- SORRY'D:       have hexact3 :=
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact2 hcompatSlotWord
-- SORRY'D:       have hexact4 :=
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact3 hcompatSlotCleared
-- SORRY'D:       exact hexact4

-- TYPESIG_SORRY: theorem compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key value : Expr}
-- TYPESIG_SORRY:     {wordOffset : Nat}
-- TYPESIG_SORRY:     {packed : PackedBits}
-- TYPESIG_SORRY:     {keyIR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey : FunctionBody.ExprCompileCore key)
-- TYPESIG_SORRY:     (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hcompatValue : "__compat_value" ∉ scope)
-- TYPESIG_SORRY:     (hcompatPacked : "__compat_packed" ∉ scope)
-- TYPESIG_SORRY:     (hcompatSlotWord : "__compat_slot_word" ∉ scope)
-- TYPESIG_SORRY:     (hcompatSlotCleared : "__compat_slot_cleared" ∉ scope)
-- TYPESIG_SORRY:     (hpacked : packedBitsValid packed = true)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- TYPESIG_SORRY:     (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMappingPackedWord fieldName key wordOffset packed value)
-- TYPESIG_SORRY:       [YulStmt.block
-- TYPESIG_SORRY:         [ YulStmt.let_ "__compat_value" valueIR
-- TYPESIG_SORRY:         , YulStmt.let_ "__compat_packed"
-- TYPESIG_SORRY:             (YulExpr.call "and" [YulExpr.ident "__compat_value",
-- TYPESIG_SORRY:               YulExpr.lit (packedMaskNat packed)])
-- TYPESIG_SORRY:         , YulStmt.let_ "__compat_slot_word"
-- TYPESIG_SORRY:             (YulExpr.call "sload"
-- TYPESIG_SORRY:               [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- TYPESIG_SORRY:                if wordOffset == 0 then mappingBase
-- TYPESIG_SORRY:                else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]])
-- TYPESIG_SORRY:         , YulStmt.let_ "__compat_slot_cleared"
-- TYPESIG_SORRY:             (YulExpr.call "and"
-- TYPESIG_SORRY:               [YulExpr.ident "__compat_slot_word",
-- TYPESIG_SORRY:                 YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
-- TYPESIG_SORRY:         , YulStmt.expr
-- TYPESIG_SORRY:             (YulExpr.call "sstore"
-- TYPESIG_SORRY:               [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- TYPESIG_SORRY:                if wordOffset == 0 then mappingBase
-- TYPESIG_SORRY:                else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
-- TYPESIG_SORRY:                YulExpr.call "or"
-- TYPESIG_SORRY:                  [YulExpr.ident "__compat_slot_cleared",
-- TYPESIG_SORRY:                    YulExpr.call "shl"
-- TYPESIG_SORRY:                      [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileMappingPackedSlotWrite,
-- SORRY'D:       hmapping, hpacked, hwriteSlots, hkeyIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey hinScopeKey hcoreValue hinScopeValue
-- SORRY'D:     hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared
-- SORRY'D:     hpacked hwriteSlots hslotSafety hkeyIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- SORRY'D:     if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
-- SORRY'D:   let keyNat := SourceSemantics.evalExpr fields runtime key
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkeySourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey hexact hinScopeKey hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkeyIR] at hkeySourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkeyEval : evalIRExpr state keyIR = some keyNat := by
-- SORRY'D:     simpa [keyNat] using hkeySourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat (by simpa [keyNat] using hkeySourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, hmembers, hmember, keyNat, valueNat]
-- SORRY'D:   · have hWriteSlotEval :
-- SORRY'D:         evalIRExpr state writeSlotExpr =
-- SORRY'D:           some (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) := by
-- SORRY'D:       dsimp [writeSlotExpr]
-- SORRY'D:       by_cases hzero : wordOffset = 0
-- SORRY'D:       · subst hzero
-- SORRY'D:         simp [evalIRExpr, hkeyEval]
-- SORRY'D:       · simp [evalIRExpr, hkeyEval, hzero]
-- SORRY'D:     have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                       state.storage
-- SORRY'D:                       (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset)
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hWriteSlotEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts] using hExecStmt
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setStructMember_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName memberName : String}
-- TYPESIG_SORRY:     {key value : Expr}
-- TYPESIG_SORRY:     {wordOffset : Nat}
-- TYPESIG_SORRY:     {members : List StructMember}
-- TYPESIG_SORRY:     {keyIR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping : isMapping fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey : FunctionBody.ExprCompileCore key)
-- TYPESIG_SORRY:     (hinScopeKey : FunctionBody.exprBoundNamesInScope key scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hmembers : findStructMembers fields fieldName = some members)
-- TYPESIG_SORRY:     (hmember :
-- TYPESIG_SORRY:       findStructMember members memberName =
-- TYPESIG_SORRY:         some { name := memberName, wordOffset := wordOffset, packed := none })
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- TYPESIG_SORRY:     (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setStructMember fieldName key memberName value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
-- TYPESIG_SORRY:            if wordOffset == 0 then mappingBase
-- TYPESIG_SORRY:            else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetStructMember,
-- SORRY'D:       CompilationModel.compileMappingSlotWrite, hmapping, hmembers, hmember,
-- SORRY'D:       hwriteSlots, hkeyIR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey hinScopeKey hcoreValue hinScopeValue hmembers hmember hwriteSlots
-- SORRY'D:     hslotSafety hkeyIR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let compiledIR := [YulStmt.expr
-- SORRY'D:     (YulExpr.call "sstore"
-- SORRY'D:       [YulExpr.call "mappingSlot"
-- SORRY'D:         [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])]
-- SORRY'D:   let keyNat1 := SourceSemantics.evalExpr fields runtime key1
-- SORRY'D:   let keyNat2 := SourceSemantics.evalExpr fields runtime key2
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkey1SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey1 hexact hinScopeKey1 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
-- SORRY'D:       hruntime
-- SORRY'D:   have hkey2SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey2 hexact hinScopeKey2 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkey1IR] at hkey1SourceEval
-- SORRY'D:   rw [hkey2IR] at hkey2SourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkey1Eval : evalIRExpr state key1IR = some keyNat1 := by
-- SORRY'D:     simpa [keyNat1] using hkey1SourceEval
-- SORRY'D:   have hkey2Eval : evalIRExpr state key2IR = some keyNat2 := by
-- SORRY'D:     simpa [keyNat2] using hkey2SourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat1 keyNat2
-- SORRY'D:       (by simpa [keyNat1] using hkey1SourceEval)
-- SORRY'D:       (by simpa [keyNat2] using hkey2SourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat1, keyNat2, valueNat]
-- SORRY'D:   · have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr
-- SORRY'D:             (YulExpr.call "sstore"
-- SORRY'D:               [YulExpr.call "mappingSlot"
-- SORRY'D:                 [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreMappingEntry
-- SORRY'D:                       (Compiler.Proofs.abstractStoreMappingEntry state.storage slot keyNat1 0)
-- SORRY'D:                       (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:                       keyNat2
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hkey1Eval, hkey2Eval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreMappingEntry_eq, Compiler.Proofs.abstractMappingSlot_eq_solidity]
-- SORRY'D:     simpa [compiledIR, execIRStmts, hExecStmt]
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot <|
-- SORRY'D:         bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMapping2_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key1 key2 value : Expr}
-- TYPESIG_SORRY:     {key1IR key2IR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping2 : isMapping2 fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey1 : FunctionBody.ExprCompileCore key1)
-- TYPESIG_SORRY:     (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
-- TYPESIG_SORRY:     (hcoreKey2 : FunctionBody.ExprCompileCore key2)
-- TYPESIG_SORRY:     (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat1 keyNat2,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2) = none)
-- TYPESIG_SORRY:     (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
-- TYPESIG_SORRY:     (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMapping2 fieldName key1 key2 value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [YulExpr.call "mappingSlot"
-- TYPESIG_SORRY:             [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetMapping2,
-- SORRY'D:       hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
-- SORRY'D:     hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
-- SORRY'D:     let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
-- SORRY'D:     if wordOffset == 0 then mappingSlot2 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset]
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
-- SORRY'D:   let keyNat1 := SourceSemantics.evalExpr fields runtime key1
-- SORRY'D:   let keyNat2 := SourceSemantics.evalExpr fields runtime key2
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkey1SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey1 hexact hinScopeKey1 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
-- SORRY'D:       hruntime
-- SORRY'D:   have hkey2SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey2 hexact hinScopeKey2 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkey1IR] at hkey1SourceEval
-- SORRY'D:   rw [hkey2IR] at hkey2SourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkey1Eval : evalIRExpr state key1IR = some keyNat1 := by
-- SORRY'D:     simpa [keyNat1] using hkey1SourceEval
-- SORRY'D:   have hkey2Eval : evalIRExpr state key2IR = some keyNat2 := by
-- SORRY'D:     simpa [keyNat2] using hkey2SourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat1 keyNat2
-- SORRY'D:       (by simpa [keyNat1] using hkey1SourceEval)
-- SORRY'D:       (by simpa [keyNat2] using hkey2SourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, keyNat1, keyNat2, valueNat]
-- SORRY'D:   · have hWriteSlotEval :
-- SORRY'D:         evalIRExpr state writeSlotExpr =
-- SORRY'D:           some (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:             keyNat2 + wordOffset) := by
-- SORRY'D:       dsimp [writeSlotExpr]
-- SORRY'D:       by_cases hzero : wordOffset = 0
-- SORRY'D:       · subst hzero
-- SORRY'D:         simp [evalIRExpr, hkey1Eval, hkey2Eval, Compiler.Proofs.abstractMappingSlot_eq_solidity]
-- SORRY'D:       · simp [evalIRExpr, hkey1Eval, hkey2Eval, hzero,
-- SORRY'D:           Compiler.Proofs.abstractMappingSlot_eq_solidity]
-- SORRY'D:     have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                       state.storage
-- SORRY'D:                       (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:                         (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:                         keyNat2 + wordOffset)
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hWriteSlotEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts] using hExecStmt
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {key1 key2 value : Expr}
-- TYPESIG_SORRY:     {wordOffset : Nat}
-- TYPESIG_SORRY:     {key1IR key2IR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping2 : isMapping2 fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey1 : FunctionBody.ExprCompileCore key1)
-- TYPESIG_SORRY:     (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
-- TYPESIG_SORRY:     (hcoreKey2 : FunctionBody.ExprCompileCore key2)
-- TYPESIG_SORRY:     (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat1 keyNat2,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2 + wordOffset) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2 + wordOffset) = none)
-- TYPESIG_SORRY:     (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
-- TYPESIG_SORRY:     (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setMapping2Word fieldName key1 key2 wordOffset value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
-- TYPESIG_SORRY:            let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
-- TYPESIG_SORRY:            if wordOffset == 0 then mappingSlot2
-- TYPESIG_SORRY:            else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetMapping2Word,
-- SORRY'D:       hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
-- SORRY'D:     hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

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
          irExec := by sorry
-- SORRY'D:   intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:   let writeSlotExpr :=
-- SORRY'D:     let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
-- SORRY'D:     let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
-- SORRY'D:     if wordOffset == 0 then mappingSlot2 else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset]
-- SORRY'D:   let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
-- SORRY'D:   let keyNat1 := SourceSemantics.evalExpr fields runtime key1
-- SORRY'D:   let keyNat2 := SourceSemantics.evalExpr fields runtime key2
-- SORRY'D:   let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:   have hkey1SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey1 hexact hinScopeKey1 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
-- SORRY'D:       hruntime
-- SORRY'D:   have hkey2SourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreKey2 hexact hinScopeKey2 hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
-- SORRY'D:       hruntime
-- SORRY'D:   have hvalueSourceEval :=
-- SORRY'D:     FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:       hcoreValue hexact hinScopeValue hbounded
-- SORRY'D:       (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
-- SORRY'D:       hruntime
-- SORRY'D:   rw [hkey1IR] at hkey1SourceEval
-- SORRY'D:   rw [hkey2IR] at hkey2SourceEval
-- SORRY'D:   rw [hvalueIR] at hvalueSourceEval
-- SORRY'D:   have hkey1Eval : evalIRExpr state key1IR = some keyNat1 := by
-- SORRY'D:     simpa [keyNat1] using hkey1SourceEval
-- SORRY'D:   have hkey2Eval : evalIRExpr state key2IR = some keyNat2 := by
-- SORRY'D:     simpa [keyNat2] using hkey2SourceEval
-- SORRY'D:   have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:     simpa [valueNat] using hvalueSourceEval
-- SORRY'D:   rcases hslotSafety runtime keyNat1 keyNat2
-- SORRY'D:       (by simpa [keyNat1] using hkey1SourceEval)
-- SORRY'D:       (by simpa [keyNat2] using hkey2SourceEval) with
-- SORRY'D:     ⟨hresolvedNone, hdynNone⟩
-- SORRY'D:   refine ⟨_, _, ?_⟩
-- SORRY'D:   · simp [SourceSemantics.execStmt, hwriteSlots, hmembers, hmember, keyNat1, keyNat2, valueNat]
-- SORRY'D:   · have hWriteSlotEval :
-- SORRY'D:         evalIRExpr state writeSlotExpr =
-- SORRY'D:           some (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:             keyNat2 + wordOffset) := by
-- SORRY'D:       dsimp [writeSlotExpr]
-- SORRY'D:       by_cases hzero : wordOffset = 0
-- SORRY'D:       · subst hzero
-- SORRY'D:         simp [evalIRExpr, hkey1Eval, hkey2Eval, Compiler.Proofs.abstractMappingSlot_eq_solidity]
-- SORRY'D:       · simp [evalIRExpr, hkey1Eval, hkey2Eval, hzero,
-- SORRY'D:           Compiler.Proofs.abstractMappingSlot_eq_solidity]
-- SORRY'D:     have hExecStmt :
-- SORRY'D:         execIRStmt (extraFuel + 1) state
-- SORRY'D:           (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
-- SORRY'D:             .continue
-- SORRY'D:               { state with
-- SORRY'D:                   storage :=
-- SORRY'D:                     Compiler.Proofs.abstractStoreStorageOrMapping
-- SORRY'D:                       state.storage
-- SORRY'D:                       (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:                         (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:                         keyNat2 + wordOffset)
-- SORRY'D:                       valueNat } := by
-- SORRY'D:       simp [execIRStmt, evalIRExpr, hWriteSlotEval, hvalueEval,
-- SORRY'D:         Compiler.Proofs.abstractStoreStorageOrMapping_eq]
-- SORRY'D:     simpa [compiledIR, execIRStmts] using hExecStmt
-- SORRY'D:   · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:     · exact runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
-- SORRY'D:         hruntime hresolvedNone hdynNone
-- SORRY'D:     · exact bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact

-- TYPESIG_SORRY: theorem compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName memberName : String}
-- TYPESIG_SORRY:     {key1 key2 value : Expr}
-- TYPESIG_SORRY:     {wordOffset : Nat}
-- TYPESIG_SORRY:     {members : List StructMember}
-- TYPESIG_SORRY:     {key1IR key2IR valueIR : YulExpr}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hmapping2 : isMapping2 fields fieldName = true)
-- TYPESIG_SORRY:     (hcoreKey1 : FunctionBody.ExprCompileCore key1)
-- TYPESIG_SORRY:     (hinScopeKey1 : FunctionBody.exprBoundNamesInScope key1 scope)
-- TYPESIG_SORRY:     (hcoreKey2 : FunctionBody.ExprCompileCore key2)
-- TYPESIG_SORRY:     (hinScopeKey2 : FunctionBody.exprBoundNamesInScope key2 scope)
-- TYPESIG_SORRY:     (hcoreValue : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hmembers : findStructMembers fields fieldName = some members)
-- TYPESIG_SORRY:     (hmember :
-- TYPESIG_SORRY:       findStructMember members memberName =
-- TYPESIG_SORRY:         some { name := memberName, wordOffset := wordOffset, packed := none })
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
-- TYPESIG_SORRY:     (hslotSafety :
-- TYPESIG_SORRY:       ∀ runtime keyNat1 keyNat2,
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- TYPESIG_SORRY:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- TYPESIG_SORRY:           findResolvedFieldAtSlotCopy fields
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2 + wordOffset) = none ∧
-- TYPESIG_SORRY:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- TYPESIG_SORRY:             (Compiler.Proofs.abstractMappingSlot
-- TYPESIG_SORRY:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- TYPESIG_SORRY:               keyNat2 + wordOffset) = none)
-- TYPESIG_SORRY:     (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
-- TYPESIG_SORRY:     (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setStructMember2 fieldName key1 key2 memberName value)
-- TYPESIG_SORRY:       [YulStmt.expr
-- TYPESIG_SORRY:         (YulExpr.call "sstore"
-- TYPESIG_SORRY:           [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
-- TYPESIG_SORRY:            let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
-- TYPESIG_SORRY:            if wordOffset == 0 then mappingSlot2
-- TYPESIG_SORRY:            else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetStructMember2,
-- SORRY'D:       hmapping2, hmembers, hmember, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
-- SORRY'D:   preserves := compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
-- SORRY'D:     hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
-- SORRY'D:     hmembers hmember hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_aliasSlots
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope : FunctionBody.exprBoundNamesInScope value scope)
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots fields fieldName = some (slot :: f.aliasSlots))
-- TYPESIG_SORRY:     (halias : f.aliasSlots ≠ [])
-- TYPESIG_SORRY:     (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope)
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     CompiledStmtStep fields scope (.setStorage fieldName value)
-- TYPESIG_SORRY:       [YulStmt.block
-- TYPESIG_SORRY:         ([YulStmt.let_ "__compat_value" valueIR] ++
-- TYPESIG_SORRY:           (slot :: f.aliasSlots).map (fun writeSlot =>
-- TYPESIG_SORRY:             YulStmt.expr
-- TYPESIG_SORRY:               (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] where
-- TYPESIG_SORRY:   compileOk := by sorry
-- SORRY'D:     simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
-- SORRY'D:       hfind, hwriteSlots, halias, hunpacked, hvalueIR]
-- SORRY'D:   preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
-- SORRY'D:     let slots := slot :: f.aliasSlots
-- SORRY'D:     let blockBody :=
-- SORRY'D:       [YulStmt.let_ "__compat_value" valueIR] ++
-- SORRY'D:         slots.map (fun writeSlot =>
-- SORRY'D:           YulStmt.expr
-- SORRY'D:             (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
-- SORRY'D:     let compiledIR := [YulStmt.block blockBody]
-- SORRY'D:     let valueNat := SourceSemantics.evalExpr fields runtime value
-- SORRY'D:     have heval :=
-- SORRY'D:       FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:         hcore hexact hinScope hbounded
-- SORRY'D:         (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
-- SORRY'D:         hruntime
-- SORRY'D:     rw [hvalueIR] at heval
-- SORRY'D:     have hvalueEval : evalIRExpr state valueIR = some valueNat := by
-- SORRY'D:       simpa [valueNat] using heval
-- SORRY'D:     have hbodyFuelLe : slots.length + 2 ≤ extraFuel := by
-- SORRY'D:       have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
-- SORRY'D:         simpa [compiledIR] using hslack
-- SORRY'D:       simp [compiledIR, blockBody, slots] at hslack'
-- SORRY'D:       omega
-- SORRY'D:     let bodyExtraFuel := extraFuel - (slots.length + 2)
-- SORRY'D:     have hbodyFuelEq : slots.length + bodyExtraFuel + 2 = extraFuel := by
-- SORRY'D:       dsimp [bodyExtraFuel]
-- SORRY'D:       omega
-- SORRY'D:     have hresolvedSlots :
-- SORRY'D:         ∀ writeSlot ∈ slots, findResolvedFieldAtSlotCopy fields writeSlot = some f := by
-- SORRY'D:       intro writeSlot hmem
-- SORRY'D:       exact
-- SORRY'D:         findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
-- SORRY'D:           hnoConflict hfind hwriteSlots hmem hunpacked
-- SORRY'D:     refine ⟨_, _, ?_⟩
-- SORRY'D:     · simp [SourceSemantics.execStmt, hwriteSlots, valueNat, slots]
-- SORRY'D:     · have hbody :
-- SORRY'D:           execIRStmts extraFuel state blockBody =
-- SORRY'D:             .continue
-- SORRY'D:               { state.setVar "__compat_value" valueNat with
-- SORRY'D:                   storage :=
-- SORRY'D:                     abstractStoreStorageOrMappingMany
-- SORRY'D:                       (state.setVar "__compat_value" valueNat).storage
-- SORRY'D:                       slots
-- SORRY'D:                       valueNat } := by
-- SORRY'D:         simpa [hbodyFuelEq, blockBody, slots, bodyExtraFuel] using
-- SORRY'D:           execIRStmts_let_then_sstore_lit_ident_slots_continue
-- SORRY'D:             bodyExtraFuel state slots "__compat_value" valueIR valueNat hvalueEval
-- SORRY'D:       have hwhole :
-- SORRY'D:           execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
-- SORRY'D:             .continue
-- SORRY'D:               { state.setVar "__compat_value" valueNat with
-- SORRY'D:                   storage :=
-- SORRY'D:                     abstractStoreStorageOrMappingMany
-- SORRY'D:                     (state.setVar "__compat_value" valueNat).storage
-- SORRY'D:                     slots
-- SORRY'D:                     valueNat } := by
-- SORRY'D:         simpa [compiledIR] using
-- SORRY'D:           execIRStmts_single_block_of_continue
-- SORRY'D:             extraFuel state
-- SORRY'D:             { state.setVar "__compat_value" valueNat with
-- SORRY'D:                 storage :=
-- SORRY'D:                   abstractStoreStorageOrMappingMany
-- SORRY'D:                     (state.setVar "__compat_value" valueNat).storage
-- SORRY'D:                     slots
-- SORRY'D:                     valueNat }
-- SORRY'D:             blockBody
-- SORRY'D:             hbody
-- SORRY'D:       simpa using hwhole
-- SORRY'D:     · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
-- SORRY'D:       · have hruntimeSet :
-- SORRY'D:             FunctionBody.runtimeStateMatchesIR fields runtime (state.setVar "__compat_value" valueNat) :=
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime
-- SORRY'D:         simpa [slots, IRState.setVar] using
-- SORRY'D:           runtimeStateMatchesIR_writeUintSlots hruntimeSet hresolvedSlots hnotAddr hnotDyn
-- SORRY'D:       · have hexactSet :
-- SORRY'D:             FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
-- SORRY'D:               (state.setVar "__compat_value" valueNat) :=
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
-- SORRY'D:             hexact (compatValue_not_mem_scope_of_reservedPrefix hscopeReserved)
-- SORRY'D:         simpa [slots, IRState.setVar] using
-- SORRY'D:           bindingsExactlyMatchIRVarsOnScope_writeUintSlots hexactSet

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
    ∃ compiledIR, CompiledStmtStep spec.fields scope (.setStorage fieldName value) compiledIR := by sorry
-- SORRY'D:   by_cases halias : f.aliasSlots = []
-- SORRY'D:   · refine ⟨[YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])], ?_⟩
-- SORRY'D:     apply compiledStmtStep_setStorage_singleSlot
-- SORRY'D:       (hcore := hcore)
-- SORRY'D:       (hinScope := hinScope)
-- SORRY'D:       (hfind := hfind)
-- SORRY'D:       (hwriteSlots := ?_)
-- SORRY'D:       (halias := halias)
-- SORRY'D:       (hunpacked := hunpacked)
-- SORRY'D:       (hnoConflict := hnoConflict)
-- SORRY'D:       (hnotAddr := hnotAddr)
-- SORRY'D:       (hnotDyn := hnotDyn)
-- SORRY'D:       (hvalueIR := hvalueIR)
-- SORRY'D:     simpa [halias] using hwriteSlots
-- SORRY'D:   · refine
-- SORRY'D:       ⟨[YulStmt.block
-- SORRY'D:           ([YulStmt.let_ "__compat_value" valueIR] ++
-- SORRY'D:             (slot :: f.aliasSlots).map (fun writeSlot =>
-- SORRY'D:               YulStmt.expr
-- SORRY'D:                 (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))],
-- SORRY'D:         ?_⟩
-- SORRY'D:     apply compiledStmtStep_setStorage_aliasSlots
-- SORRY'D:       (hcore := hcore)
-- SORRY'D:       (hinScope := hinScope)
-- SORRY'D:       (hfind := hfind)
-- SORRY'D:       (hwriteSlots := hwriteSlots)
-- SORRY'D:       (halias := halias)
-- SORRY'D:       (hscopeReserved := scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes
-- SORRY'D:         hvalidate hfn hscopeNames)
-- SORRY'D:       (hunpacked := hunpacked)
-- SORRY'D:       (hnoConflict := hnoConflict)
-- SORRY'D:       (hnotAddr := hnotAddr)
-- SORRY'D:       (hnotDyn := hnotDyn)
-- SORRY'D:       (hvalueIR := hvalueIR)

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hvalidate : validateIdentifierShapes spec = Except.ok ())
-- TYPESIG_SORRY:     (hfn : fn ∈ spec.functions)
-- TYPESIG_SORRY:     (hprefix :
-- TYPESIG_SORRY:       StmtListScopeDiscipline
-- TYPESIG_SORRY:         (spec.fields.map (·.name))
-- TYPESIG_SORRY:         (fn.params.map (·.name))
-- TYPESIG_SORRY:         prefix)
-- TYPESIG_SORRY:     (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope :
-- TYPESIG_SORRY:       FunctionBody.exprBoundNamesInScope
-- TYPESIG_SORRY:         value
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     ∃ compiledIR,
-- TYPESIG_SORRY:       CompiledStmtStep spec.fields
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
-- TYPESIG_SORRY:         (.setStorage fieldName value)
-- TYPESIG_SORRY:         compiledIR := by sorry
-- SORRY'D:   apply compiledStmtStep_setStorage_of_validateIdentifierShapes
-- SORRY'D:     (scope := List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
-- SORRY'D:     (hvalidate := hvalidate)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hscopeNames := ?_)
-- SORRY'D:     (hcore := hcore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hunpacked := hunpacked)
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hnotAddr := hnotAddr)
-- SORRY'D:     (hnotDyn := hnotDyn)
-- SORRY'D:     (hvalueIR := hvalueIR)
-- SORRY'D:   intro name hmem
-- SORRY'D:   have hscopeNames := stmtListScopeDiscipline_scope_names hprefix name hmem
-- SORRY'D:   rw [hbody] at hscopeNames
-- SORRY'D:   simpa [collectStmtListBindNames, collectStmtListAssignedNames, hbody] using hscopeNames

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
-- TYPESIG_SORRY:     (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
-- TYPESIG_SORRY:     (hfn : fn ∈ spec.functions)
-- TYPESIG_SORRY:     (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
-- TYPESIG_SORRY:     (hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) prefix)
-- TYPESIG_SORRY:     (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope :
-- TYPESIG_SORRY:       FunctionBody.exprBoundNamesInScope
-- TYPESIG_SORRY:         value
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     ∃ compiledIR,
-- TYPESIG_SORRY:       CompiledStmtStep spec.fields
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
-- TYPESIG_SORRY:         (.setStorage fieldName value)
-- TYPESIG_SORRY:         compiledIR := by sorry
-- SORRY'D:   apply compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
-- SORRY'D:     (hvalidate := hvalidateShapes)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hprefix := stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
-- SORRY'D:       hprefixCore hvalidateRefs hparamScope
-- SORRY'D:       (by simpa [List.append_assoc] using hbody))
-- SORRY'D:     (hbody := hbody)
-- SORRY'D:     (hcore := hcore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hunpacked := hunpacked)
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hnotAddr := hnotAddr)
-- SORRY'D:     (hnotDyn := hnotDyn)
-- SORRY'D:     (hvalueIR := hvalueIR)

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
-- TYPESIG_SORRY:     (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
-- TYPESIG_SORRY:     (hfn : fn ∈ spec.functions)
-- TYPESIG_SORRY:     (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
-- TYPESIG_SORRY:     (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
-- TYPESIG_SORRY:     (hbodyCompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         spec.fields [] [] .calldata [] false (fn.params.map (·.name)) fn.body =
-- TYPESIG_SORRY:           Except.ok bodyIR)
-- TYPESIG_SORRY:     (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
-- TYPESIG_SORRY:     (hcore : FunctionBody.ExprCompileCore value)
-- TYPESIG_SORRY:     (hinScope :
-- TYPESIG_SORRY:       FunctionBody.exprBoundNamesInScope
-- TYPESIG_SORRY:         value
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     ∃ compiledIR,
-- TYPESIG_SORRY:       CompiledStmtStep spec.fields
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
-- TYPESIG_SORRY:         (.setStorage fieldName value)
-- TYPESIG_SORRY:         compiledIR := by sorry
-- SORRY'D:   apply compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
-- SORRY'D:     (hvalidateShapes := hvalidateShapes)
-- SORRY'D:     (hvalidateRefs := hvalidateRefs)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hparamScope := hparamScope)
-- SORRY'D:     (hprefixCore := stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
-- SORRY'D:       (fields := spec.fields)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (prefix := prefix)
-- SORRY'D:       (suffix := .setStorage fieldName value :: suffix)
-- SORRY'D:       (bodyIR := bodyIR)
-- SORRY'D:       (by simpa [hbody] using hbodySurface)
-- SORRY'D:       (by simpa [hbody] using hbodyCompile))
-- SORRY'D:     (hbody := hbody)
-- SORRY'D:     (hcore := hcore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hunpacked := hunpacked)
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hnotAddr := hnotAddr)
-- SORRY'D:     (hnotDyn := hnotDyn)
-- SORRY'D:     (hvalueIR := hvalueIR)

-- TYPESIG_SORRY: theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     {bodyIR : List YulStmt}
-- TYPESIG_SORRY:     {fieldName : String}
-- TYPESIG_SORRY:     {value : Expr}
-- TYPESIG_SORRY:     {valueIR : YulExpr}
-- TYPESIG_SORRY:     {f : Field}
-- TYPESIG_SORRY:     {slot : Nat}
-- TYPESIG_SORRY:     (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
-- TYPESIG_SORRY:     (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
-- TYPESIG_SORRY:     (hfn : fn ∈ spec.functions)
-- TYPESIG_SORRY:     (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
-- TYPESIG_SORRY:     (hbodySurface : stmtListTouchesUnsupportedContractSurface fn.body = false)
-- TYPESIG_SORRY:     (hbodyCompile :
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         spec.fields [] [] .calldata [] false (fn.params.map (·.name)) fn.body =
-- TYPESIG_SORRY:           Except.ok bodyIR)
-- TYPESIG_SORRY:     (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
-- TYPESIG_SORRY:     (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
-- TYPESIG_SORRY:     (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
-- TYPESIG_SORRY:     (hunpacked : f.packedBits = none)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
-- TYPESIG_SORRY:     (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
-- TYPESIG_SORRY:     (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
-- TYPESIG_SORRY:     (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
-- TYPESIG_SORRY:     ∃ compiledIR,
-- TYPESIG_SORRY:       CompiledStmtStep spec.fields
-- TYPESIG_SORRY:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
-- TYPESIG_SORRY:         (.setStorage fieldName value)
-- TYPESIG_SORRY:         compiledIR := by sorry
-- SORRY'D:   have hprefixCore :
-- SORRY'D:       StmtListScopeCore (spec.fields.map (·.name)) prefix :=
-- SORRY'D:     stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
-- SORRY'D:       (fields := spec.fields)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (prefix := prefix)
-- SORRY'D:       (suffix := .setStorage fieldName value :: suffix)
-- SORRY'D:       (bodyIR := bodyIR)
-- SORRY'D:       (by simpa [hbody] using hbodySurface)
-- SORRY'D:       (by simpa [hbody] using hbodyCompile)
-- SORRY'D:   have hstmtSurface :
-- SORRY'D:       stmtTouchesUnsupportedContractSurface (.setStorage fieldName value) = false := by
-- SORRY'D:     exact
-- SORRY'D:       stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
-- SORRY'D:         (by simpa [hbody] using hbodySurface)
-- SORRY'D:   have hvalueCore : FunctionBody.ExprCompileCore value :=
-- SORRY'D:     exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
-- SORRY'D:       (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)
-- SORRY'D:   have hinScope :
-- SORRY'D:       FunctionBody.exprBoundNamesInScope
-- SORRY'D:         value
-- SORRY'D:         (List.foldl stmtNextScope (fn.params.map (·.name)) prefix) :=
-- SORRY'D:     exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
-- SORRY'D:       hprefixCore hvalueCore hvalidateRefs hparamScope hbody
-- SORRY'D:   exact compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList
-- SORRY'D:     (hvalidateShapes := hvalidateShapes)
-- SORRY'D:     (hvalidateRefs := hvalidateRefs)
-- SORRY'D:     (hfn := hfn)
-- SORRY'D:     (hparamScope := hparamScope)
-- SORRY'D:     (hbodySurface := hbodySurface)
-- SORRY'D:     (hbodyCompile := hbodyCompile)
-- SORRY'D:     (hbody := hbody)
-- SORRY'D:     (hcore := hvalueCore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hunpacked := hunpacked)
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hnotAddr := hnotAddr)
-- SORRY'D:     (hnotDyn := hnotDyn)
-- SORRY'D:     (hvalueIR := hvalueIR)

private theorem terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec)
    (hnotContinue : ∀ next, sourceResult ≠ .continue next) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by sorry
-- SORRY'D:   cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
-- SORRY'D:   case continue runtime =>
-- SORRY'D:     exact False.elim (hnotContinue runtime rfl)

theorem compiledStmtStep_ite
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hcond : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hthen : FunctionBody.StmtListTerminalCore scope thenBranch)
    (helse : FunctionBody.StmtListTerminalCore scope elseBranch) :
    ∃ compiledIR, CompiledStmtStep fields scope (.ite cond thenBranch elseBranch) compiledIR := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
-- SORRY'D:   rcases FunctionBody.compileStmtList_terminal_core_ok
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (inScopeNames := scope)
-- SORRY'D:       (stmts := thenBranch)
-- SORRY'D:       hthen with
-- SORRY'D:     ⟨thenIR, hthenIR⟩
-- SORRY'D:   rcases FunctionBody.compileStmtList_terminal_core_ok
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (inScopeNames := scope)
-- SORRY'D:       (stmts := elseBranch)
-- SORRY'D:       helse with
-- SORRY'D:     ⟨elseIR, helseIR⟩
-- SORRY'D:   have helseNonempty : elseBranch.isEmpty = false := by
-- SORRY'D:     cases elseBranch with
-- SORRY'D:     | nil =>
-- SORRY'D:         exfalso
-- SORRY'D:         exact FunctionBody.stmtListTerminalCore_ne_nil helse rfl
-- SORRY'D:     | cons =>
-- SORRY'D:         simp
-- SORRY'D:   let tempName :=
-- SORRY'D:     CompilationModel.pickFreshName "__ite_cond"
-- SORRY'D:       (scope ++ collectExprNames cond ++
-- SORRY'D:         collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
-- SORRY'D:   let compiledIR :=
-- SORRY'D:     [YulStmt.block
-- SORRY'D:       [ YulStmt.let_ tempName condIR
-- SORRY'D:       , YulStmt.if_ (YulExpr.ident tempName) thenIR
-- SORRY'D:       , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]
-- SORRY'D:   refine ⟨compiledIR, ?_⟩
-- SORRY'D:   refine
-- SORRY'D:     { compileOk := ?_
-- SORRY'D:       preserves := ?_ }
-- SORRY'D:   · unfold compiledIR tempName
-- SORRY'D:     unfold CompilationModel.compileStmt
-- SORRY'D:     rw [hcondIR, hthenIR, helseIR]
-- SORRY'D:     simp [helseNonempty]
-- SORRY'D:   · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
-- SORRY'D:     let slack := sizeOf compiledIR - compiledIR.length
-- SORRY'D:     let wholeExtraFuel := extraFuel - slack
-- SORRY'D:     have hwholeFuel :
-- SORRY'D:         sizeOf compiledIR + wholeExtraFuel + 1 =
-- SORRY'D:           compiledIR.length + extraFuel + 1 := by
-- SORRY'D:       dsimp [wholeExtraFuel, slack, compiledIR]
-- SORRY'D:       have : slack ≤ extraFuel := by
-- SORRY'D:         simpa [slack, compiledIR] using hslack
-- SORRY'D:       omega
-- SORRY'D:     have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
-- SORRY'D:       FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
-- SORRY'D:     let condValue := SourceSemantics.evalExpr fields runtime cond
-- SORRY'D:     have hcondEval :
-- SORRY'D:         evalIRExpr state condIR = some condValue := by
-- SORRY'D:       have heval :=
-- SORRY'D:         FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:           hcond hexact hinScope hbounded hpresent hruntime
-- SORRY'D:       rw [hcondIR] at heval
-- SORRY'D:       simpa [condValue] using heval
-- SORRY'D:     by_cases hcondZero : condValue = 0
-- SORRY'D:     · let branchExtraFuel :=
-- SORRY'D:         sizeOf compiledIR - (sizeOf elseIR + 5) + wholeExtraFuel
-- SORRY'D:       rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state.setVar tempName condValue)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (inScopeNames := scope)
-- SORRY'D:           (stmts := elseBranch)
-- SORRY'D:           (extraFuel := branchExtraFuel)
-- SORRY'D:           helse
-- SORRY'D:           FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:           hscope
-- SORRY'D:           (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (inScopeNames := scope)
-- SORRY'D:             (cond := cond)
-- SORRY'D:             (thenBranch := thenBranch)
-- SORRY'D:             (elseBranch := elseBranch)
-- SORRY'D:             (value := condValue)
-- SORRY'D:             hexact
-- SORRY'D:             FunctionBody.scopeNamesIncluded_refl)
-- SORRY'D:           hbounded
-- SORRY'D:           (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
-- SORRY'D:         ⟨elseIR', helseIR', helseSem⟩
-- SORRY'D:       rw [helseIR] at helseIR'
-- SORRY'D:       injection helseIR' with helseEq
-- SORRY'D:       subst helseEq
-- SORRY'D:       have hsourceEq :
-- SORRY'D:           SourceSemantics.execStmtList fields runtime
-- SORRY'D:             (.ite cond thenBranch elseBranch :: []) =
-- SORRY'D:             SourceSemantics.execStmtList fields runtime elseBranch :=
-- SORRY'D:         FunctionBody.execStmtList_terminal_core_ite_else_eq
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (cond := cond)
-- SORRY'D:           (thenBranch := thenBranch)
-- SORRY'D:           (elseBranch := elseBranch)
-- SORRY'D:           (rest := [])
-- SORRY'D:           helse
-- SORRY'D:           (by simp [condValue, hcondZero])
-- SORRY'D:       have hbodyMatch :
-- SORRY'D:           FunctionBody.stmtResultMatchesIRExec
-- SORRY'D:             fields
-- SORRY'D:             (SourceSemantics.execStmtList fields runtime elseBranch)
-- SORRY'D:             (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
-- SORRY'D:         have hmatch :=
-- SORRY'D:           FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (runtime := runtime)
-- SORRY'D:             (state := state)
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (cond := cond)
-- SORRY'D:             (thenBranch := thenBranch)
-- SORRY'D:             (elseBranch := elseBranch)
-- SORRY'D:             (rest := [])
-- SORRY'D:             (extraFuel := wholeExtraFuel)
-- SORRY'D:             (tempName := tempName)
-- SORRY'D:             (condIR := condIR)
-- SORRY'D:             (thenIR := thenIR)
-- SORRY'D:             (elseIR := elseIR)
-- SORRY'D:             (tailIR := [])
-- SORRY'D:             (condValue := condValue)
-- SORRY'D:             (irExec := execIRStmts
-- SORRY'D:               (sizeOf elseIR + branchExtraFuel)
-- SORRY'D:               (state.setVar tempName condValue)
-- SORRY'D:               elseIR)
-- SORRY'D:             helse
-- SORRY'D:             helseSem
-- SORRY'D:             (by simp [condValue, hcondZero])
-- SORRY'D:             hcondEval
-- SORRY'D:             hcondZero
-- SORRY'D:             (by
-- SORRY'D:               simpa [compiledIR, branchExtraFuel, tempName, condValue] using rfl)
-- SORRY'D:         rw [hsourceEq] at hmatch
-- SORRY'D:         simpa [hwholeFuel, compiledIR] using hmatch
-- SORRY'D:       refine ⟨_, _, ?_⟩
-- SORRY'D:       · simp [SourceSemantics.execStmt, condValue, hcondZero]
-- SORRY'D:       · rfl
-- SORRY'D:       · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
-- SORRY'D:           hbodyMatch
-- SORRY'D:           (FunctionBody.execStmtList_terminal_core_not_continue
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (runtime := runtime)
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (stmts := elseBranch)
-- SORRY'D:             helse)
-- SORRY'D:     · let branchExtraFuel :=
-- SORRY'D:         sizeOf compiledIR - (sizeOf thenIR + 5) + wholeExtraFuel
-- SORRY'D:       rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state.setVar tempName condValue)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (inScopeNames := scope)
-- SORRY'D:           (stmts := thenBranch)
-- SORRY'D:           (extraFuel := branchExtraFuel)
-- SORRY'D:           hthen
-- SORRY'D:           FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:           hscope
-- SORRY'D:           (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (inScopeNames := scope)
-- SORRY'D:             (cond := cond)
-- SORRY'D:             (thenBranch := thenBranch)
-- SORRY'D:             (elseBranch := elseBranch)
-- SORRY'D:             (value := condValue)
-- SORRY'D:             hexact
-- SORRY'D:             FunctionBody.scopeNamesIncluded_refl)
-- SORRY'D:           hbounded
-- SORRY'D:           (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
-- SORRY'D:         ⟨thenIR', hthenIR', hthenSem⟩
-- SORRY'D:       rw [hthenIR] at hthenIR'
-- SORRY'D:       injection hthenIR' with hthenEq
-- SORRY'D:       subst hthenEq
-- SORRY'D:       have hsourceEq :
-- SORRY'D:           SourceSemantics.execStmtList fields runtime
-- SORRY'D:             (.ite cond thenBranch elseBranch :: []) =
-- SORRY'D:             SourceSemantics.execStmtList fields runtime thenBranch :=
-- SORRY'D:         FunctionBody.execStmtList_terminal_core_ite_then_eq
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (cond := cond)
-- SORRY'D:           (thenBranch := thenBranch)
-- SORRY'D:           (elseBranch := elseBranch)
-- SORRY'D:           (rest := [])
-- SORRY'D:           hthen
-- SORRY'D:           (by simp [condValue, hcondZero])
-- SORRY'D:       have hbodyMatch :
-- SORRY'D:           FunctionBody.stmtResultMatchesIRExec
-- SORRY'D:             fields
-- SORRY'D:             (SourceSemantics.execStmtList fields runtime thenBranch)
-- SORRY'D:             (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
-- SORRY'D:         have hmatch :=
-- SORRY'D:           FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (runtime := runtime)
-- SORRY'D:             (state := state)
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (cond := cond)
-- SORRY'D:             (thenBranch := thenBranch)
-- SORRY'D:             (elseBranch := elseBranch)
-- SORRY'D:             (rest := [])
-- SORRY'D:             (extraFuel := wholeExtraFuel)
-- SORRY'D:             (tempName := tempName)
-- SORRY'D:             (condIR := condIR)
-- SORRY'D:             (thenIR := thenIR)
-- SORRY'D:             (elseIR := elseIR)
-- SORRY'D:             (tailIR := [])
-- SORRY'D:             (condValue := condValue)
-- SORRY'D:             (irExec := execIRStmts
-- SORRY'D:               (sizeOf thenIR + branchExtraFuel + 1)
-- SORRY'D:               (state.setVar tempName condValue)
-- SORRY'D:               thenIR)
-- SORRY'D:             hthen
-- SORRY'D:             hthenSem
-- SORRY'D:             (by simp [condValue, hcondZero])
-- SORRY'D:             hcondEval
-- SORRY'D:             (by
-- SORRY'D:               intro hzero
-- SORRY'D:               exact hcondZero hzero)
-- SORRY'D:             (by
-- SORRY'D:               simpa [compiledIR, branchExtraFuel, tempName, condValue, Nat.add_assoc,
-- SORRY'D:                 Nat.add_left_comm, Nat.add_comm] using rfl)
-- SORRY'D:         rw [hsourceEq] at hmatch
-- SORRY'D:         simpa [hwholeFuel, compiledIR] using hmatch
-- SORRY'D:       refine ⟨_, _, ?_⟩
-- SORRY'D:       · simp [SourceSemantics.execStmt, condValue, hcondZero]
-- SORRY'D:       · rfl
-- SORRY'D:       · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
-- SORRY'D:           hbodyMatch
-- SORRY'D:           (FunctionBody.execStmtList_terminal_core_not_continue
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (runtime := runtime)
-- SORRY'D:             (scope := scope)
-- SORRY'D:             (stmts := thenBranch)
-- SORRY'D:             hthen)

-- TYPESIG_SORRY: private theorem stmtListTouchesUnsupportedContractSurface_append
-- TYPESIG_SORRY:     {prefix suffix : List Stmt} :
-- TYPESIG_SORRY:     stmtListTouchesUnsupportedContractSurface (prefix ++ suffix) =
-- TYPESIG_SORRY:       (stmtListTouchesUnsupportedContractSurface prefix ||
-- TYPESIG_SORRY:         stmtListTouchesUnsupportedContractSurface suffix) := by sorry
-- SORRY'D:   induction prefix with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [stmtListTouchesUnsupportedContractSurface]
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       simp [stmtListTouchesUnsupportedContractSurface, ih, Bool.or_assoc]

private theorem stmtListCompileCore_of_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    FunctionBody.StmtListCompileCore scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) := by sorry
-- SORRY'D:   induction clauses generalizing scope with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa using FunctionBody.StmtListCompileCore.nil (scope := scope)
-- SORRY'D:   | cons clause rest ih =>
-- SORRY'D:       refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ ih
-- SORRY'D:       · cases clause with
-- SORRY'D:         | mk family n m p q message =>
-- SORRY'D:             cases family <;> repeat constructor
-- SORRY'D:       · intro name hmem
-- SORRY'D:         cases clause with
-- SORRY'D:         | mk family n m p q message =>
-- SORRY'D:             cases family <;> simp [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
-- SORRY'D:               FunctionBody.exprBoundNames] at hmem

private theorem foldl_stmtNextScope_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    List.foldl stmtNextScope scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) = scope := by sorry
-- SORRY'D:   induction clauses generalizing scope with
-- SORRY'D:   | nil =>
-- SORRY'D:       rfl
-- SORRY'D:   | cons clause rest ih =>
-- SORRY'D:       cases clause with
-- SORRY'D:       | mk family n m p q message =>
-- SORRY'D:           cases family <;>
-- SORRY'D:             simp [stmtNextScope, Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
-- SORRY'D:               collectStmtNames, ih]

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
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setStorage_singleSlot
-- SORRY'D:     (hcore := hcore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := by simpa [findFieldWriteSlots, hfind])
-- SORRY'D:     (halias := by rfl)
-- SORRY'D:     (hunpacked := by rfl)
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hnotAddr := by rfl)
-- SORRY'D:     (hnotDyn := by rfl)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setStorageAddr_singleSlot
-- SORRY'D:     (hcore := hcore)
-- SORRY'D:     (hinScope := hinScope)
-- SORRY'D:     (hfind := hfind)
-- SORRY'D:     (hwriteSlots := by simpa [findFieldWriteSlots, hfind])
-- SORRY'D:     (hnoConflict := hnoConflict)
-- SORRY'D:     (hvalueIR := hvalueIR)

private theorem stmtListGenericCore_singleton_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
-- SORRY'D:     ⟨offsetIR, hoffsetIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_mstore_single
-- SORRY'D:     (hcoreOffset := hcoreOffset)
-- SORRY'D:     (hinScopeOffset := hinScopeOffset)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hoffsetIR := hoffsetIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

private theorem stmtListGenericCore_singleton_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
-- SORRY'D:     ⟨offsetIR, hoffsetIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_tstore_single
-- SORRY'D:     (hcoreOffset := hcoreOffset)
-- SORRY'D:     (hinScopeOffset := hinScopeOffset)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hoffsetIR := hoffsetIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

private theorem stmtListGenericCore_of_requireClausesOnly
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) := by sorry
-- SORRY'D:   stmtListGenericCore_of_stmtListCompileCore
-- SORRY'D:     (fields := fields)
-- SORRY'D:     (scope := scope)
-- SORRY'D:     (stmtListCompileCore_of_requireLiteralGuardFamilyClauses (scope := scope) clauses)

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
        [Stmt.setStorage fieldName (Expr.literal writeVal)]) := by sorry
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:           (fields := fields)
-- SORRY'D:           (scope := scope)
-- SORRY'D:           (hnoConflict := hnoConflict)
-- SORRY'D:           (hfind := hfind)
-- SORRY'D:           (hcore := .literal writeVal)
-- SORRY'D:           (hinScope := by intro name hmem; simp [FunctionBody.exprBoundNames] at hmem)))

private theorem stmtListGenericCore_of_requireClausesThenReturnLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.return (Expr.literal retVal)]) := by sorry
-- SORRY'D:   have htail :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope [Stmt.return (Expr.literal retVal)] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.return_ (.literal retVal) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

private theorem stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (tmp : String)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have htail :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope
-- SORRY'D:         [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal retVal) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · refine FunctionBody.StmtListCompileCore.return_ (.localVar tmp) ?_ ?_
-- SORRY'D:       · exact .localVar tmp
-- SORRY'D:       · intro name hmem
-- SORRY'D:         simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:         simpa [hmem]
-- SORRY'D:       · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

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
        [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have hprefix :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope [Stmt.letVar tmp (Expr.literal n)] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_append
-- SORRY'D:           (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
-- SORRY'D:           (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (scope := List.foldl stmtNextScope scope [Stmt.letVar tmp (Expr.literal n)])
-- SORRY'D:             (hnoConflict := hnoConflict)
-- SORRY'D:             (hfind := hfind)
-- SORRY'D:             (hcore := .localVar tmp)
-- SORRY'D:             (hinScope := by
-- SORRY'D:               intro name hmem
-- SORRY'D:               simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:               simpa using hmem))))

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
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have hprefix :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope
-- SORRY'D:         [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · refine FunctionBody.StmtListCompileCore.assignVar (.literal m) ?_ ?_
-- SORRY'D:       · intro name hmem
-- SORRY'D:         simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:       · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_append
-- SORRY'D:           (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
-- SORRY'D:           (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (scope := List.foldl stmtNextScope scope
-- SORRY'D:               [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)])
-- SORRY'D:             (hnoConflict := hnoConflict)
-- SORRY'D:             (hfind := hfind)
-- SORRY'D:             (hcore := .localVar tmp)
-- SORRY'D:             (hinScope := by
-- SORRY'D:               intro name hmem
-- SORRY'D:               simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:               simpa using hmem))))

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
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have hprefix :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope
-- SORRY'D:         [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:          Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · refine FunctionBody.StmtListCompileCore.assignVar (.add (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
-- SORRY'D:       · exact .add (.localVar tmp) (.literal m)
-- SORRY'D:       · intro name hmem
-- SORRY'D:         simp [FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:         simpa using hmem
-- SORRY'D:       · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_append
-- SORRY'D:           (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
-- SORRY'D:           (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (scope := List.foldl stmtNextScope scope
-- SORRY'D:               [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:                Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))])
-- SORRY'D:             (hnoConflict := hnoConflict)
-- SORRY'D:             (hfind := hfind)
-- SORRY'D:             (hcore := .localVar tmp)
-- SORRY'D:             (hinScope := by
-- SORRY'D:               intro name hmem
-- SORRY'D:               simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:               simpa using hmem))))

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
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have hprefix :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope
-- SORRY'D:         [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:          Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · refine FunctionBody.StmtListCompileCore.assignVar (.sub (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
-- SORRY'D:       · exact .sub (.localVar tmp) (.literal m)
-- SORRY'D:       · intro name hmem
-- SORRY'D:         simp [FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:         simpa using hmem
-- SORRY'D:       · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_append
-- SORRY'D:           (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
-- SORRY'D:           (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (scope := List.foldl stmtNextScope scope
-- SORRY'D:               [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:                Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))])
-- SORRY'D:             (hnoConflict := hnoConflict)
-- SORRY'D:             (hfind := hfind)
-- SORRY'D:             (hcore := .localVar tmp)
-- SORRY'D:             (hinScope := by
-- SORRY'D:               intro name hmem
-- SORRY'D:               simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:               simpa using hmem))))

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
         Stmt.setStorage fieldName (Expr.localVar tmp)]) := by sorry
-- SORRY'D:   have hprefix :
-- SORRY'D:       FunctionBody.StmtListCompileCore scope
-- SORRY'D:         [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:          Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))] := by
-- SORRY'D:     refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
-- SORRY'D:     · intro name hmem
-- SORRY'D:       simp [FunctionBody.exprBoundNames] at hmem
-- SORRY'D:     · refine FunctionBody.StmtListCompileCore.assignVar (.mul (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
-- SORRY'D:       · exact .mul (.localVar tmp) (.literal m)
-- SORRY'D:       · intro name hmem
-- SORRY'D:         simp [FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:         simpa using hmem
-- SORRY'D:       · exact FunctionBody.StmtListCompileCore.nil
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
-- SORRY'D:     (by
-- SORRY'D:       simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
-- SORRY'D:         (stmtListGenericCore_append
-- SORRY'D:           (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
-- SORRY'D:           (stmtListGenericCore_singleton_setStorage_singleSlot
-- SORRY'D:             (fields := fields)
-- SORRY'D:             (scope := List.foldl stmtNextScope scope
-- SORRY'D:               [Stmt.letVar tmp (Expr.literal n),
-- SORRY'D:                Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))])
-- SORRY'D:             (hnoConflict := hnoConflict)
-- SORRY'D:             (hfind := hfind)
-- SORRY'D:             (hcore := .localVar tmp)
-- SORRY'D:             (hinScope := by
-- SORRY'D:               intro name hmem
-- SORRY'D:               simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
-- SORRY'D:               simpa using hmem))))

private theorem stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
    {fields : List Field}
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope [clause.toStmt] := by sorry
-- SORRY'D:   exact stmtListGenericCore_of_stmtListCompileCore
-- SORRY'D:     (fields := fields)
-- SORRY'D:     (scope := scope)
-- SORRY'D:     (by
-- SORRY'D:       refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
-- SORRY'D:       · cases clause with
-- SORRY'D:         | mk family n m p q message =>
-- SORRY'D:             cases family <;> repeat constructor
-- SORRY'D:       · intro name hmem
-- SORRY'D:         cases clause with
-- SORRY'D:         | mk family n m p q message =>
-- SORRY'D:             cases family <;>
-- SORRY'D:               simp [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
-- SORRY'D:                 FunctionBody.exprBoundNames] at hmem)

-- TYPESIG_SORRY: private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope prefix suffix : List Stmt}
-- TYPESIG_SORRY:     (hprefix : SupportedStmtList fields scope prefix)
-- TYPESIG_SORRY:     (hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope prefix) suffix)
-- TYPESIG_SORRY:     (ihPrefix : stmtListTouchesUnsupportedContractSurface prefix = false →
-- TYPESIG_SORRY:       StmtListGenericCore fields scope prefix)
-- TYPESIG_SORRY:     (ihSuffix : stmtListTouchesUnsupportedContractSurface suffix = false →
-- TYPESIG_SORRY:       StmtListGenericCore fields (List.foldl stmtNextScope scope prefix) suffix)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurface (prefix ++ suffix) = false) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope (prefix ++ suffix) := by sorry
-- SORRY'D:   have hsplit :
-- SORRY'D:       stmtListTouchesUnsupportedContractSurface prefix ||
-- SORRY'D:         stmtListTouchesUnsupportedContractSurface suffix = false := by
-- SORRY'D:     simpa [stmtListTouchesUnsupportedContractSurface_append] using hsurface
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (ihPrefix (Bool.or_eq_false.mp hsplit).1)
-- SORRY'D:     (ihSuffix (Bool.or_eq_false.mp hsplit).2)

-- TYPESIG_SORRY: private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {rest : List Stmt}
-- TYPESIG_SORRY:     (clause : RequireLiteralGuardFamilyClause)
-- TYPESIG_SORRY:     (ihRest : stmtListTouchesUnsupportedContractSurface rest = false →
-- TYPESIG_SORRY:       StmtListGenericCore fields scope rest)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurface (clause.toStmt :: rest) = false) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope (clause.toStmt :: rest) := by sorry
-- SORRY'D:   have hsplit :
-- SORRY'D:       stmtTouchesUnsupportedContractSurface clause.toStmt ||
-- SORRY'D:         stmtListTouchesUnsupportedContractSurface rest = false := by
-- SORRY'D:     simpa [stmtListTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (by
-- SORRY'D:       simpa using stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
-- SORRY'D:         (fields := fields) (scope := scope) clause)
-- SORRY'D:     (by
-- SORRY'D:       simpa using ihRest (Bool.or_eq_false.mp hsplit).2)

-- TYPESIG_SORRY: private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope prefix suffix : List Stmt}
-- TYPESIG_SORRY:     (hprefix : SupportedStmtList fields scope prefix)
-- TYPESIG_SORRY:     (hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope prefix) suffix)
-- TYPESIG_SORRY:     (ihPrefix :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites prefix = false →
-- TYPESIG_SORRY:         StmtListGenericCore fields scope prefix)
-- TYPESIG_SORRY:     (ihSuffix :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites suffix = false →
-- TYPESIG_SORRY:         StmtListGenericCore fields (List.foldl stmtNextScope scope prefix) suffix)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (prefix ++ suffix) = false) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope (prefix ++ suffix) := by sorry
-- SORRY'D:   have hsplit :
-- SORRY'D:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites prefix ||
-- SORRY'D:         stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites suffix = false := by
-- SORRY'D:     simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (ihPrefix (Bool.or_eq_false.mp hsplit).1)
-- SORRY'D:     (ihSuffix (Bool.or_eq_false.mp hsplit).2)

-- TYPESIG_SORRY: private theorem stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {rest : List Stmt}
-- TYPESIG_SORRY:     (clause : RequireLiteralGuardFamilyClause)
-- TYPESIG_SORRY:     (ihRest :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false →
-- TYPESIG_SORRY:         StmtListGenericCore fields scope rest)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (clause.toStmt :: rest) = false) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope (clause.toStmt :: rest) := by sorry
-- SORRY'D:   have hsplit :
-- SORRY'D:       stmtTouchesUnsupportedContractSurfaceExceptMappingWrites clause.toStmt ||
-- SORRY'D:         stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false := by
-- SORRY'D:     simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface
-- SORRY'D:   exact stmtListGenericCore_append
-- SORRY'D:     (by
-- SORRY'D:       simpa using stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
-- SORRY'D:         (fields := fields) (scope := scope) clause)
-- SORRY'D:     (by
-- SORRY'D:       simpa using ihRest (Bool.or_eq_false.mp hsplit).2)

private theorem false_of_supportedStmtList_ite_surface
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hsurface :
      stmtTouchesUnsupportedContractSurface
        (Stmt.ite cond thenBranch elseBranch) = false) :
    False := by
  simp [stmtTouchesUnsupportedContractSurface] at hsurface

private theorem false_of_supportedStmtList_ite_list_surface
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        [Stmt.ite cond thenBranch elseBranch] = false) :
    False := by
  have hhead :
      stmtTouchesUnsupportedContractSurface
        (Stmt.ite cond thenBranch elseBranch) = false := by
    simpa [stmtListTouchesUnsupportedContractSurface] using hsurface
  exact false_of_supportedStmtList_ite_surface hhead

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
    StmtListGenericCore fields scope [Stmt.setStorage fieldName value] :=
  stmtListGenericCore_singleton_setStorage_singleSlot
    (fields := fields)
    (scope := scope)
    (hnoConflict := hnoConflict)
    (hfind := hfind)
    (hcore := hcore)
    (hinScope := hinScope)

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
    StmtListGenericCore fields scope [Stmt.setStorageAddr fieldName value] :=
  stmtListGenericCore_singleton_setStorageAddr_singleSlot
    (fields := fields)
    (scope := scope)
    (hnoConflict := hnoConflict)
    (hfind := hfind)
    (hcore := hcore)
    (hinScope := hinScope)

private theorem stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] :=
  stmtListGenericCore_singleton_mstore_single
    (fields := fields)
    (scope := scope)
    (hcoreOffset := hcoreOffset)
    (hinScopeOffset := hinScopeOffset)
    (hcoreValue := hcoreValue)
    (hinScopeValue := hinScopeValue)

private theorem stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] :=
  stmtListGenericCore_singleton_tstore_single
    (fields := fields)
    (scope := scope)
    (hcoreOffset := hcoreOffset)
    (hinScopeOffset := hinScopeOffset)
    (hcoreValue := hcoreValue)
    (hinScopeValue := hinScopeValue)

private theorem compileExprList_core_ok
    {fields : List Field}
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    ∃ exprIRs, CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs := by sorry
-- SORRY'D:   induction exprs with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact ⟨[], by simp [CompilationModel.compileExprList]⟩
-- SORRY'D:   | cons expr rest ih =>
-- SORRY'D:       have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
-- SORRY'D:       have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
-- SORRY'D:         intro e he
-- SORRY'D:         exact hcore e (by simp [he])
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
-- SORRY'D:       rcases ih htail with ⟨restIR, hrestIR⟩
-- SORRY'D:       exact ⟨exprIR :: restIR, by simp [CompilationModel.compileExprList, hexprIR, hrestIR]⟩

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
      List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) exprIRs values := by sorry
-- SORRY'D:   induction exprs generalizing exprIRs with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [CompilationModel.compileExprList, SourceSemantics.evalExprList] at hcompiled
-- SORRY'D:       subst exprIRs
-- SORRY'D:       exact ⟨[], by simp [SourceSemantics.evalExprList], List.Forall₂.nil⟩
-- SORRY'D:   | cons expr rest ih =>
-- SORRY'D:       have hheadCore : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
-- SORRY'D:       have htailCore : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
-- SORRY'D:         intro e he
-- SORRY'D:         exact hcore e (by simp [he])
-- SORRY'D:       have hheadScope : FunctionBody.exprBoundNamesInScope expr scope := hinScope expr (by simp)
-- SORRY'D:       have htailScope : ∀ e ∈ rest, FunctionBody.exprBoundNamesInScope e scope := by
-- SORRY'D:         intro e he
-- SORRY'D:         exact hinScope e (by simp [he])
-- SORRY'D:       cases hheadCompile : CompilationModel.compileExpr fields .calldata expr <;>
-- SORRY'D:         simp [CompilationModel.compileExprList, hheadCompile] at hcompiled
-- SORRY'D:       rename_i exprIR
-- SORRY'D:       cases htailCompile : CompilationModel.compileExprList fields .calldata rest <;>
-- SORRY'D:         simp [CompilationModel.compileExprList, hheadCompile, htailCompile] at hcompiled
-- SORRY'D:       rename_i restIRs
-- SORRY'D:       cases hcompiled
-- SORRY'D:       have hheadIR :=
-- SORRY'D:         FunctionBody.eval_compileExpr_core_of_scope
-- SORRY'D:           hheadCore hexact hheadScope hbounded
-- SORRY'D:           (FunctionBody.exprBoundNamesPresent_of_scope hscope hheadScope)
-- SORRY'D:           hruntime
-- SORRY'D:       rw [hheadCompile] at hheadIR
-- SORRY'D:       rcases ih htailCore hexact htailScope hbounded hscope hruntime htailCompile with
-- SORRY'D:         ⟨restVals, htailEval, htailIR⟩
-- SORRY'D:       refine ⟨Option.getD (SourceSemantics.evalExpr fields runtime expr) 0 :: restVals, ?_, ?_⟩
-- SORRY'D:       · simpa [SourceSemantics.evalExprList, htailEval] using hheadIR
-- SORRY'D:       · simpa using List.Forall₂.cons hheadIR htailIR

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
      some (SourceSemantics.mappingSlotChain baseSlot keyVals) := by sorry
-- SORRY'D:   induction hkeys generalizing baseSlot with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp [SourceSemantics.mappingSlotChain, evalIRExpr]
-- SORRY'D:   | @cons exprIR value restIRs restVals hhead htail ih =>
-- SORRY'D:       simp [List.foldl_cons, SourceSemantics.mappingSlotChain, evalIRExpr,
-- SORRY'D:         hhead, Compiler.Proofs.abstractMappingSlot_eq_solidity, ih]

-- SORRY'D: /-- Extra Tier 2 assumptions needed to turn the singleton mapping-write
-- SORRY'D: constructors in `SupportedStmtList` into real compiled-step proofs. These are
-- SORRY'D: kept separate from the surface predicate because the remaining obligation is a
-- SORRY'D: layout-specific slot-safety fact, not a syntactic fragment question. -/
-- SORRY'D: structure SupportedStmtListMappingWriteSlotSafety (fields : List Field) : Prop where
-- SORRY'D:   setMappingUintSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key value : Expr}
-- SORRY'D:       {slot : Nat},
-- SORRY'D:       FunctionBody.ExprCompileCore key →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
-- SORRY'D:   setMappingChainSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {keys : List Expr}
-- SORRY'D:       {value : Expr}
-- SORRY'D:       {slot : Nat},
-- SORRY'D:       (∀ expr ∈ keys, FunctionBody.ExprCompileCore expr) →
-- SORRY'D:       (∀ expr ∈ keys, FunctionBody.exprBoundNamesInScope expr scope) →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyVals,
-- SORRY'D:         SourceSemantics.evalExprList fields runtime keys = some keyVals →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (SourceSemantics.mappingSlotChain slot keyVals) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (SourceSemantics.mappingSlotChain slot keyVals) = none)
-- SORRY'D:   setMappingSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key value : Expr}
-- SORRY'D:       {slot : Nat},
-- SORRY'D:       FunctionBody.ExprCompileCore key →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat) = none)
-- SORRY'D:   setMappingWordSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key value : Expr}
-- SORRY'D:       {wordOffset slot : Nat},
-- SORRY'D:       FunctionBody.ExprCompileCore key →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- SORRY'D:   setMappingPackedWordSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key value : Expr}
-- SORRY'D:       {wordOffset slot : Nat}
-- SORRY'D:       {packed : PackedBits},
-- SORRY'D:       FunctionBody.ExprCompileCore key →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       "__compat_value" ∉ scope →
-- SORRY'D:       "__compat_packed" ∉ scope →
-- SORRY'D:       "__compat_slot_word" ∉ scope →
-- SORRY'D:       "__compat_slot_cleared" ∉ scope →
-- SORRY'D:       packedBitsValid packed = true →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- SORRY'D:   setStructMemberSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName memberName : String}
-- SORRY'D:       {key value : Expr}
-- SORRY'D:       {slot wordOffset : Nat}
-- SORRY'D:       {members : List StructMember},
-- SORRY'D:       FunctionBody.ExprCompileCore key →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       findStructMembers fields fieldName = some members →
-- SORRY'D:       findStructMember members memberName =
-- SORRY'D:         some { name := memberName, wordOffset := wordOffset, packed := none } →
-- SORRY'D:       isMapping fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key = some keyNat →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot slot keyNat + wordOffset) = none)
-- SORRY'D:   setMapping2Single :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key1 key2 value : Expr}
-- SORRY'D:       {slot : Nat},
-- SORRY'D:       FunctionBody.ExprCompileCore key1 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key1 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore key2 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key2 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping2 fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat1 keyNat2,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2) = none)
-- SORRY'D:   setMapping2WordSingle :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName : String}
-- SORRY'D:       {key1 key2 value : Expr}
-- SORRY'D:       {wordOffset slot : Nat},
-- SORRY'D:       FunctionBody.ExprCompileCore key1 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key1 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore key2 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key2 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       isMapping2 fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat1 keyNat2,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2 + wordOffset) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2 + wordOffset) = none)
-- SORRY'D:   setStructMember2Single :
-- SORRY'D:     ∀ {scope : List String}
-- SORRY'D:       {fieldName memberName : String}
-- SORRY'D:       {key1 key2 value : Expr}
-- SORRY'D:       {slot wordOffset : Nat}
-- SORRY'D:       {members : List StructMember},
-- SORRY'D:       FunctionBody.ExprCompileCore key1 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key1 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore key2 →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope key2 scope →
-- SORRY'D:       FunctionBody.ExprCompileCore value →
-- SORRY'D:       FunctionBody.exprBoundNamesInScope value scope →
-- SORRY'D:       findFieldSlot fields fieldName = some slot →
-- SORRY'D:       findStructMembers fields fieldName = some members →
-- SORRY'D:       findStructMember members memberName =
-- SORRY'D:         some { name := memberName, wordOffset := wordOffset, packed := none } →
-- SORRY'D:       isMapping2 fields fieldName = true ∧
-- SORRY'D:       findFieldWriteSlots fields fieldName = some [slot] ∧
-- SORRY'D:       (∀ runtime keyNat1 keyNat2,
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key1 = some keyNat1 →
-- SORRY'D:         SourceSemantics.evalExpr fields runtime key2 = some keyNat2 →
-- SORRY'D:           findResolvedFieldAtSlotCopy fields
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2 + wordOffset) = none ∧
-- SORRY'D:           findDynamicArrayElementAtSlotCopy fields runtime.world
-- SORRY'D:             (Compiler.Proofs.abstractMappingSlot
-- SORRY'D:               (Compiler.Proofs.abstractMappingSlot slot keyNat1)
-- SORRY'D:               keyNat2 + wordOffset) = none)

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
    StmtListGenericCore fields scope [Stmt.setMappingUint fieldName key value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
-- SORRY'D:     ⟨keyIR, hkeyIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKey := hcoreKey)
-- SORRY'D:     (hinScopeKey := hinScopeKey)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIR := hkeyIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMappingChain fieldName keys value] := by sorry
-- SORRY'D:   rcases compileExprList_core_ok (fields := fields) hcoreKeys with ⟨keyIRs, hkeyIRs⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKeys := hcoreKeys)
-- SORRY'D:     (hinScopeKeys := hinScopeKeys)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIRs := hkeyIRs)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMapping fieldName key value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
-- SORRY'D:     ⟨keyIR, hkeyIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMapping_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKey := hcoreKey)
-- SORRY'D:     (hinScopeKey := hinScopeKey)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIR := hkeyIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMappingWord fieldName key wordOffset value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
-- SORRY'D:     ⟨keyIR, hkeyIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKey := hcoreKey)
-- SORRY'D:     (hinScopeKey := hinScopeKey)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIR := hkeyIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMappingPackedWord fieldName key wordOffset packed value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
-- SORRY'D:     ⟨keyIR, hkeyIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKey := hcoreKey)
-- SORRY'D:     (hinScopeKey := hinScopeKey)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hcompatValue := hcompatValue)
-- SORRY'D:     (hcompatPacked := hcompatPacked)
-- SORRY'D:     (hcompatSlotWord := hcompatSlotWord)
-- SORRY'D:     (hcompatSlotCleared := hcompatSlotCleared)
-- SORRY'D:     (hpacked := hpacked)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIR := hkeyIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setStructMember fieldName key memberName value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
-- SORRY'D:     ⟨keyIR, hkeyIR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setStructMember_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping := hmapping)
-- SORRY'D:     (hcoreKey := hcoreKey)
-- SORRY'D:     (hinScopeKey := hinScopeKey)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hmembers := hmembers)
-- SORRY'D:     (hmember := hmember)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkeyIR := hkeyIR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMapping2 fieldName key1 key2 value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
-- SORRY'D:     ⟨key1IR, hkey1IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
-- SORRY'D:     ⟨key2IR, hkey2IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMapping2_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping2 := hmapping2)
-- SORRY'D:     (hcoreKey1 := hcoreKey1)
-- SORRY'D:     (hinScopeKey1 := hinScopeKey1)
-- SORRY'D:     (hcoreKey2 := hcoreKey2)
-- SORRY'D:     (hinScopeKey2 := hinScopeKey2)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkey1IR := hkey1IR)
-- SORRY'D:     (hkey2IR := hkey2IR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
-- SORRY'D:     ⟨key1IR, hkey1IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
-- SORRY'D:     ⟨key2IR, hkey2IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping2 := hmapping2)
-- SORRY'D:     (hcoreKey1 := hcoreKey1)
-- SORRY'D:     (hinScopeKey1 := hinScopeKey1)
-- SORRY'D:     (hcoreKey2 := hcoreKey2)
-- SORRY'D:     (hinScopeKey2 := hinScopeKey2)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkey1IR := hkey1IR)
-- SORRY'D:     (hkey2IR := hkey2IR)
-- SORRY'D:     (hvalueIR := hvalueIR)

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
    StmtListGenericCore fields scope [Stmt.setStructMember2 fieldName key1 key2 memberName value] := by sorry
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
-- SORRY'D:     ⟨key1IR, hkey1IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
-- SORRY'D:     ⟨key2IR, hkey2IR⟩
-- SORRY'D:   rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
-- SORRY'D:     ⟨valueIR, hvalueIR⟩
-- SORRY'D:   refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
-- SORRY'D:   exact compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
-- SORRY'D:     (hmapping2 := hmapping2)
-- SORRY'D:     (hcoreKey1 := hcoreKey1)
-- SORRY'D:     (hinScopeKey1 := hinScopeKey1)
-- SORRY'D:     (hcoreKey2 := hcoreKey2)
-- SORRY'D:     (hinScopeKey2 := hinScopeKey2)
-- SORRY'D:     (hcoreValue := hcoreValue)
-- SORRY'D:     (hinScopeValue := hinScopeValue)
-- SORRY'D:     (hmembers := hmembers)
-- SORRY'D:     (hmember := hmember)
-- SORRY'D:     (hwriteSlots := hwriteSlots)
-- SORRY'D:     (hslotSafety := hslotSafety)
-- SORRY'D:     (hkey1IR := hkey1IR)
-- SORRY'D:     (hkey2IR := hkey2IR)
-- SORRY'D:     (hvalueIR := hvalueIR)

private theorem false_of_supportedStmtList_singleton_stmt_surface
    {stmt : Stmt}
    (hunsupported : stmtTouchesUnsupportedContractSurface stmt = true)
    (hsurface : stmtListTouchesUnsupportedContractSurface [stmt] = false) :
    False := by
  have hhead : stmtTouchesUnsupportedContractSurface stmt = false := by
    simpa [stmtListTouchesUnsupportedContractSurface] using hsurface
  rw [hunsupported] at hhead
  contradiction

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
  simp [stmtListTouchesUnsupportedContractSurface,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedCoreSurface,
    exprTouchesUnsupportedStateSurface,
    exprTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface] at hsurface

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
  simp [stmtListTouchesUnsupportedContractSurface,
    stmtTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedContractSurface,
    exprTouchesUnsupportedCoreSurface,
    exprTouchesUnsupportedStateSurface,
    exprTouchesUnsupportedCallSurface,
    stmtTouchesUnsupportedEffectSurface] at hsurface

theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by sorry
-- SORRY'D:   induction hSupported with
-- SORRY'D:   | compileCore hcore => exact stmtListGenericCore_of_stmtListCompileCore hcore
-- SORRY'D:   | terminalCore hterminal => exact stmtListGenericCore_of_stmtListTerminalCore hterminal
-- SORRY'D:   | setStorageSingleSlot hcore hinScope hfind =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
-- SORRY'D:         (fields := fields) hnoConflict hfind hcore hinScope
-- SORRY'D:   | setStorageAddrSingleSlot hcore hinScope hfind =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
-- SORRY'D:         (fields := fields) hnoConflict hfind hcore hinScope
-- SORRY'D:   | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
-- SORRY'D:         (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
-- SORRY'D:   | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
-- SORRY'D:         (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
-- SORRY'D:   | letStorageField hfind => exact False.elim (false_of_supportedStmtList_letStorageField_surface hsurface)
-- SORRY'D:   | returnMapping hkey hscope hslot => exact False.elim (false_of_supportedStmtList_returnMapping_surface hsurface)
-- SORRY'D:   | letMapping hkey hscope hslot => exact False.elim (false_of_supportedStmtList_letMapping_surface hsurface)
-- SORRY'D:   | letMapping2 hkey1 hscope1 hkey2 hscope2 hslot => exact False.elim (false_of_supportedStmtList_letMapping2_surface hsurface)
-- SORRY'D:   | letMappingUint hkey hscope hslot => exact False.elim (false_of_supportedStmtList_letMappingUint_surface hsurface)
-- SORRY'D:   | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot => exact False.elim (false_of_supportedStmtList_setMappingUintSingle_surface hsurface)
-- SORRY'D:   | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setMappingChainSingle_surface hsurface)
-- SORRY'D:   | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot => exact False.elim (false_of_supportedStmtList_setMappingSingle_surface hsurface)
-- SORRY'D:   | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setMappingWordSingle_surface hsurface)
-- SORRY'D:   | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
-- SORRY'D:       hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setMappingPackedWordSingle_surface hsurface)
-- SORRY'D:   | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setStructMemberSingle_surface hsurface)
-- SORRY'D:   | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot => exact False.elim (false_of_supportedStmtList_setMapping2Single_surface hsurface)
-- SORRY'D:   | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setMapping2WordSingle_surface hsurface)
-- SORRY'D:   | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_setStructMember2Single_surface hsurface)
-- SORRY'D:   | rawLogLiterals htopics => exact False.elim (false_of_supportedStmtList_rawLogLiterals_surface hsurface)
-- SORRY'D:   | letCallerLetStorageReqEqReqNeqSetStorageParamStop hOwner hne_sv_p hne_ov_p hne_ov_sv =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_surface hsurface)
-- SORRY'D:   | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
-- SORRY'D:       hOwner hTarget hne_sv_p hne_ov_p hne_ov_sv hne_tv_p hne_tv_sv hne_tv_ov =>
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_surface hsurface)
-- SORRY'D:   | requireClause clause hrest ih =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface
-- SORRY'D:         (fields := fields) (scope := scope) clause ih hsurface
-- SORRY'D:   | ite hcond hscope hthen helse ihThen ihElse => exact False.elim (false_of_supportedStmtList_ite_list_surface hsurface)
-- SORRY'D:   | append hprefix hsuffix ihPrefix ihSuffix =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_append_of_surface hprefix hsuffix ihPrefix ihSuffix hsurface

-- TYPESIG_SORRY: theorem stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hSupported : SupportedStmtList fields scope stmts)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope stmts := by sorry
-- SORRY'D:   induction hSupported with
-- SORRY'D:   | compileCore hcore =>
-- SORRY'D:       exact stmtListGenericCore_of_stmtListCompileCore hcore
-- SORRY'D:   | terminalCore hterminal =>
-- SORRY'D:       exact stmtListGenericCore_of_stmtListTerminalCore hterminal
-- SORRY'D:   | setStorageSingleSlot hcore hinScope hfind =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
-- SORRY'D:         (fields := fields) hnoConflict hfind hcore hinScope
-- SORRY'D:   | setStorageAddrSingleSlot hcore hinScope hfind =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
-- SORRY'D:         (fields := fields) hnoConflict hfind hcore hinScope
-- SORRY'D:   | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
-- SORRY'D:         (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
-- SORRY'D:   | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
-- SORRY'D:         (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
-- SORRY'D:   | letStorageField hfind =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.letVar tmp (Expr.storage fieldName)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letStorageField_surface hsurfaceBase)
-- SORRY'D:   | returnMapping hkey hscope hslot =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.return (Expr.mapping fieldName key)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_returnMapping_surface hsurfaceBase)
-- SORRY'D:   | letMapping hkey hscope hslot =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.letVar tmp (Expr.mapping fieldName key)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letMapping_surface hsurfaceBase)
-- SORRY'D:   | letMapping2 hkey1 hscope1 hkey2 hscope2 hslot =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.letVar tmp (Expr.mapping2 fieldName key1 key2)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letMapping2_surface hsurfaceBase)
-- SORRY'D:   | letMappingUint hkey hscope hslot =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.letVar tmp (Expr.mappingUint fieldName key)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_letMappingUint_surface hsurfaceBase)
-- SORRY'D:   | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMappingUintSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey := hkey)
-- SORRY'D:         (hinScopeKey := hscopeKey)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMappingChainSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKeys := hkeys)
-- SORRY'D:         (hinScopeKeys := hscopeKeys)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMappingSingle hkey hscopeKey hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMappingSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey := hkey)
-- SORRY'D:         (hinScopeKey := hscopeKey)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMappingWordSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey := hkey)
-- SORRY'D:         (hinScopeKey := hscopeKey)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
-- SORRY'D:       hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
-- SORRY'D:       rcases hsafety.setMappingPackedWordSingle
-- SORRY'D:           hkey hscopeKey hvalue hscopeValue hpacked hslot with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey := hkey)
-- SORRY'D:         (hinScopeKey := hscopeKey)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hcompatValue := hcompatValue)
-- SORRY'D:         (hcompatPacked := hcompatPacked)
-- SORRY'D:         (hcompatSlotWord := hcompatSlotWord)
-- SORRY'D:         (hcompatSlotCleared := hcompatSlotCleared)
-- SORRY'D:         (hpacked := hpacked)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
-- SORRY'D:       rcases hsafety.setStructMemberSingle
-- SORRY'D:           hkey hscopeKey hvalue hscopeValue hslot hmembers hmember with
-- SORRY'D:         ⟨hmapping, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setStructMemberSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey := hkey)
-- SORRY'D:         (hinScopeKey := hscopeKey)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping := hmapping)
-- SORRY'D:         (hmembers := hmembers)
-- SORRY'D:         (hmember := hmember)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping2, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMapping2Single_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey1 := hkey1)
-- SORRY'D:         (hinScopeKey1 := hscope1)
-- SORRY'D:         (hcoreKey2 := hkey2)
-- SORRY'D:         (hinScopeKey2 := hscope2)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping2 := hmapping2)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
-- SORRY'D:       rcases hsafety.setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot with
-- SORRY'D:         ⟨hmapping2, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setMapping2WordSingle_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey1 := hkey1)
-- SORRY'D:         (hinScopeKey1 := hscope1)
-- SORRY'D:         (hcoreKey2 := hkey2)
-- SORRY'D:         (hinScopeKey2 := hscope2)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping2 := hmapping2)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
-- SORRY'D:       rcases hsafety.setStructMember2Single
-- SORRY'D:           hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember with
-- SORRY'D:         ⟨hmapping2, hwriteSlots, hslotSafety⟩
-- SORRY'D:       exact stmtListGenericCore_singleton_setStructMember2Single_of_slotSafety
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (scope := scope)
-- SORRY'D:         (hcoreKey1 := hkey1)
-- SORRY'D:         (hinScopeKey1 := hscope1)
-- SORRY'D:         (hcoreKey2 := hkey2)
-- SORRY'D:         (hinScopeKey2 := hscope2)
-- SORRY'D:         (hcoreValue := hvalue)
-- SORRY'D:         (hinScopeValue := hscopeValue)
-- SORRY'D:         (hmapping2 := hmapping2)
-- SORRY'D:         (hmembers := hmembers)
-- SORRY'D:         (hmember := hmember)
-- SORRY'D:         (hwriteSlots := hwriteSlots)
-- SORRY'D:         (hslotSafety := hslotSafety)
-- SORRY'D:   | rawLogLiterals htopics =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface
-- SORRY'D:             [Stmt.rawLog (topics.map Expr.literal) (Expr.literal dataOffset) (Expr.literal dataSize)] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_rawLogLiterals_surface hsurfaceBase)
-- SORRY'D:   | letCallerLetStorageReqEqReqNeqSetStorageParamStop hOwner hne_sv_p hne_ov_p hne_ov_sv =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface
-- SORRY'D:             [ Stmt.letVar senderVar Expr.caller
-- SORRY'D:             , Stmt.letVar ownerVar (Expr.storage ownerField)
-- SORRY'D:             , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
-- SORRY'D:             , Stmt.require
-- SORRY'D:                 (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar ownerVar))) msg2
-- SORRY'D:             , Stmt.setStorage ownerField (Expr.param paramName)
-- SORRY'D:             , Stmt.stop
-- SORRY'D:             ] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim
-- SORRY'D:         (false_of_supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_surface
-- SORRY'D:           hsurfaceBase)
-- SORRY'D:   | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
-- SORRY'D:       hOwner hTarget hne_sv_p hne_ov_p hne_ov_sv hne_tv_p hne_tv_sv hne_tv_ov =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface
-- SORRY'D:             [ Stmt.letVar senderVar Expr.caller
-- SORRY'D:             , Stmt.letVar ownerVar (Expr.storage ownerField)
-- SORRY'D:             , Stmt.require (Expr.eq (Expr.localVar senderVar) (Expr.localVar ownerVar)) msg1
-- SORRY'D:             , Stmt.letVar targetVar (Expr.storage targetField)
-- SORRY'D:             , Stmt.require
-- SORRY'D:                 (Expr.logicalNot (Expr.eq (Expr.param paramName) (Expr.localVar targetVar))) msg2
-- SORRY'D:             , Stmt.setStorage targetField (Expr.param paramName)
-- SORRY'D:             , Stmt.stop
-- SORRY'D:             ] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim
-- SORRY'D:         (false_of_supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_surface
-- SORRY'D:           hsurfaceBase)
-- SORRY'D:   | requireClause clause hrest ih =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_requireClause_of_surface_exceptMappingWrites
-- SORRY'D:         (fields := fields) (scope := scope) clause ih hsurface
-- SORRY'D:   | ite hcond hscope hthen helse ihThen ihElse =>
-- SORRY'D:       have hsurfaceBase :
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface [Stmt.ite cond thenBranch elseBranch] = false := by
-- SORRY'D:         simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtTouchesUnsupportedContractSurfaceExceptMappingWrites,
-- SORRY'D:           stmtListTouchesUnsupportedContractSurface,
-- SORRY'D:           stmtTouchesUnsupportedContractSurface] using hsurface
-- SORRY'D:       exact False.elim (false_of_supportedStmtList_ite_list_surface hsurfaceBase)
-- SORRY'D:   | append hprefix hsuffix ihPrefix ihSuffix =>
-- SORRY'D:       exact stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
-- SORRY'D:         hprefix hsuffix ihPrefix ihSuffix hsurface

-- SORRY'D: /-- The current supported statement-list witness already suffices for the
-- SORRY'D: weaker helper-free source-step interface consumed by the exact helper-aware
-- SORRY'D: seam. This keeps helper-free reuse derivable directly from the proof-layer
-- SORRY'D: fragment witness without exposing the stronger full generic-core theorem at the
-- SORRY'D: supported-body boundary. -/
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

-- TYPESIG_SORRY: theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hSupported : SupportedStmtList fields scope stmts)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety fields)
-- TYPESIG_SORRY:     (hsurface :
-- TYPESIG_SORRY:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
-- TYPESIG_SORRY:     StmtListHelperFreeStepInterface fields scope stmts := by sorry
-- SORRY'D:   stmtListHelperFreeStepInterface_of_core
-- SORRY'D:     (stmtListGenericCore_of_supportedStmtList_of_surface_exceptMappingWrites
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (stmts := stmts)
-- SORRY'D:       hnoConflict
-- SORRY'D:       hSupported
-- SORRY'D:       hsafety
-- SORRY'D:       hsurface)

-- TYPESIG_SORRY: theorem stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict fields = none)
-- TYPESIG_SORRY:     (hSupported : SupportedStmtList fields scope stmts)
-- TYPESIG_SORRY:     (hcore : stmtListTouchesUnsupportedCoreSurface stmts = false)
-- TYPESIG_SORRY:     (hstate : stmtListTouchesUnsupportedStateSurfaceExceptMappingWrites stmts = false)
-- TYPESIG_SORRY:     (hcalls : stmtListTouchesUnsupportedCallSurface stmts = false)
-- TYPESIG_SORRY:     (heffects : stmtListTouchesUnsupportedEffectSurface stmts = false)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety fields) :
-- TYPESIG_SORRY:     StmtListHelperFreeStepInterface fields scope stmts := by sorry
-- SORRY'D:   have hsurface :
-- SORRY'D:       stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false :=
-- SORRY'D:     stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_eq_false_of_featureClosed
-- SORRY'D:       stmts hcore hstate hcalls heffects
-- SORRY'D:   exact stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface_exceptMappingWrites
-- SORRY'D:     (fields := fields)
-- SORRY'D:     (scope := scope)
-- SORRY'D:     (stmts := stmts)
-- SORRY'D:     hnoConflict
-- SORRY'D:     hSupported
-- SORRY'D:     hsafety
-- SORRY'D:     hsurface

-- SORRY'D: /-- The supported-body interface also derives the weaker source-side reuse
-- SORRY'D: witness needed by the exact helper-aware seam: helper-free heads retain the
-- SORRY'D: legacy generic-step obligation, while helper-positive heads can be discharged
-- SORRY'D: separately. -/
theorem SupportedBodyInterface.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by sorry
-- SORRY'D:   have hsurface :
-- SORRY'D:       stmtListTouchesUnsupportedContractSurface fn.body = false :=
-- SORRY'D:     stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
-- SORRY'D:       hBody.core.surfaceClosed
-- SORRY'D:       hBody.state.surfaceClosed
-- SORRY'D:       (SupportedBodyCallInterface.surfaceClosed (hBody := hBody))
-- SORRY'D:       hBody.effects.surfaceClosed
-- SORRY'D:   stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
-- SORRY'D:     (fields := spec.fields)
-- SORRY'D:     (scope := fn.params.map (·.name))
-- SORRY'D:     (stmts := fn.body)
-- SORRY'D:     hnoConflict
-- SORRY'D:     hBody.stmtList
-- SORRY'D:     hsurface

-- TYPESIG_SORRY: theorem SupportedBodyInterfaceExceptMappingWrites.helperFreeStepInterface
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hBody : SupportedBodyInterfaceExceptMappingWrites spec fn)
-- TYPESIG_SORRY:     (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
-- TYPESIG_SORRY:     (hsafety : SupportedStmtListMappingWriteSlotSafety spec.fields) :
-- TYPESIG_SORRY:     StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by sorry
-- SORRY'D:   exact stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed_exceptMappingWrites
-- SORRY'D:     (fields := spec.fields)
-- SORRY'D:     (scope := fn.params.map (·.name))
-- SORRY'D:     (stmts := fn.body)
-- SORRY'D:     hnoConflict
-- SORRY'D:     hBody.stmtList
-- SORRY'D:     hBody.core.surfaceClosed
-- SORRY'D:     hBody.state.surfaceClosed
-- SORRY'D:     (SupportedBodyCallInterface.surfaceClosed_exceptMappingWrites (hBody := hBody))
-- SORRY'D:     hBody.effects.surfaceClosed
-- SORRY'D:     hsafety

private theorem exprBoundNamesInScope_of_scopeNamesIncluded
    {expr : Expr}
    {scope largerScope : List String}
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.exprBoundNamesInScope expr largerScope := by
  intro name hname
  exact hincluded name (hinScope name hname)

private theorem stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by sorry
-- SORRY'D:   induction hcore generalizing largerScope with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact StmtListGenericCore.nil
-- SORRY'D:   | letVar hvalue hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_letVar
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
-- SORRY'D:   | assignVar hvalue hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_assignVar
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
-- SORRY'D:   | require_ hcond hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
-- SORRY'D:         ⟨failCond, hfailCond⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_require
-- SORRY'D:           (hcore := hcond)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hfailCompile := hfailCond))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:           (stmt := .require _ _) hincluded)
-- SORRY'D:   | return_ hvalue hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_return
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:           (stmt := .return _) hincluded)
-- SORRY'D:   | stop hrest ih =>
-- SORRY'D:       exact StmtListGenericCore.cons compiledStmtStep_stop
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:           (stmt := .stop) hincluded)

private theorem stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by sorry
-- SORRY'D:   induction hterminal generalizing largerScope with
-- SORRY'D:   | letVar hvalue hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_letVar
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
-- SORRY'D:   | assignVar hvalue hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_assignVar
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
-- SORRY'D:   | require_ hcond hinScope hrest ih =>
-- SORRY'D:       rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
-- SORRY'D:         ⟨failCond, hfailCond⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_require
-- SORRY'D:           (hcore := hcond)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hfailCompile := hfailCond))
-- SORRY'D:         (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:           (stmt := .require _ _) hincluded)
-- SORRY'D:   | return_ hvalue hinScope hrest =>
-- SORRY'D:       rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
-- SORRY'D:         ⟨valueIR, hvalueIR⟩
-- SORRY'D:       exact StmtListGenericCore.cons
-- SORRY'D:         (compiledStmtStep_return
-- SORRY'D:           (hcore := hvalue)
-- SORRY'D:           (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           (hvalueIR := hvalueIR))
-- SORRY'D:         (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
-- SORRY'D:           hrest
-- SORRY'D:           (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:             (stmt := .return _) hincluded))
-- SORRY'D:   | stop hrest =>
-- SORRY'D:       exact StmtListGenericCore.cons compiledStmtStep_stop
-- SORRY'D:         (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
-- SORRY'D:           hrest
-- SORRY'D:           (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:             (stmt := .stop) hincluded))
-- SORRY'D:   | ite hcond hinScope hthen helse hrest ihThen ihElse =>
-- SORRY'D:       rcases compiledStmtStep_ite (fields := fields) hcond
-- SORRY'D:           (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
-- SORRY'D:           hthen helse with
-- SORRY'D:         ⟨compiledIR, hstep⟩
-- SORRY'D:       exact StmtListGenericCore.cons hstep
-- SORRY'D:         (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
-- SORRY'D:           hrest
-- SORRY'D:           (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:             (stmt := .ite _ _ _) hincluded))

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

-- TYPESIG_SORRY: theorem stmtListGenericCore_append
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {scope : List String}
-- TYPESIG_SORRY:     {prefix suffix : List Stmt}
-- TYPESIG_SORRY:     (hprefix : StmtListGenericCore fields scope prefix)
-- TYPESIG_SORRY:     (hsuffix :
-- TYPESIG_SORRY:       StmtListGenericCore
-- TYPESIG_SORRY:         fields
-- TYPESIG_SORRY:         (List.foldl stmtNextScope scope prefix)
-- TYPESIG_SORRY:         suffix) :
-- TYPESIG_SORRY:     StmtListGenericCore fields scope (prefix ++ suffix) := by sorry
-- SORRY'D:   induction hprefix generalizing suffix with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa using hsuffix
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       simp
-- SORRY'D:       exact StmtListGenericCore.cons hstep (ih hsuffix)

private theorem scopeNamesIncluded_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt} :
    FunctionBody.scopeNamesIncluded scope (List.foldl stmtNextScope scope stmts) := by sorry
-- SORRY'D:   induction stmts generalizing scope with
-- SORRY'D:   | nil =>
-- SORRY'D:       simpa using FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       exact
-- SORRY'D:         FunctionBody.scopeNamesIncluded_collectStmtNames_tail
-- SORRY'D:           (ih (scope := stmtNextScope scope stmt))

theorem compileStmtList_ok_of_stmtListGenericCore
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by sorry
-- SORRY'D:   induction hgeneric generalizing inScopeNames with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       rcases ih
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (scopeNamesIncluded_stmtNextScope hincluded) with
-- SORRY'D:         ⟨tailIR, htail⟩
-- SORRY'D:       refine ⟨compiledIR ++ tailIR, ?_⟩
-- SORRY'D:       exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:         hstep.compileOk htail

theorem compileStmtList_ok_of_stmtListGenericWithHelpers
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by sorry
-- SORRY'D:   induction hgeneric generalizing inScopeNames with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       rcases ih
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (scopeNamesIncluded_stmtNextScope hincluded) with
-- SORRY'D:         ⟨tailIR, htail⟩
-- SORRY'D:       refine ⟨compiledIR ++ tailIR, ?_⟩
-- SORRY'D:       exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:         hstep.compileOk htail

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
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by sorry
-- SORRY'D:   induction hgeneric generalizing inScopeNames with
-- SORRY'D:   | nil =>
-- SORRY'D:       exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       rcases ih
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (scopeNamesIncluded_stmtNextScope hincluded) with
-- SORRY'D:         ⟨tailIR, htail⟩
-- SORRY'D:       refine ⟨compiledIR ++ tailIR, ?_⟩
-- SORRY'D:       exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:         hstep.compileOk htail

theorem stmtStepMatchesIRExec_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by sorry
-- SORRY'D:   cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
-- SORRY'D:   case continue runtime state =>
-- SORRY'D:     rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
-- SORRY'D:     exact ⟨hruntime,
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
-- SORRY'D:       hbounded,
-- SORRY'D:       FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩

theorem stmtStepMatchesIRExecWithInternals_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch : stmtStepMatchesIRExecWithInternals fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec := by sorry
-- SORRY'D:   cases sourceResult <;> cases irExec <;>
-- SORRY'D:     simp [stmtStepMatchesIRExecWithInternals] at hmatch ⊢
-- SORRY'D:   case continue runtime state =>
-- SORRY'D:     rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
-- SORRY'D:     exact ⟨hruntime,
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
-- SORRY'D:       hbounded,
-- SORRY'D:       FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩

theorem stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields scope sourceResult irExec) :
    FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch <;>
    simp [FunctionBody.stmtResultMatchesIRExec, hmatch]

theorem stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch :
      stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec) :
    stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by sorry
-- SORRY'D:   cases sourceResult <;> cases irExec <;>
-- SORRY'D:     simp [stmtStepMatchesIRExecWithInternals, stmtResultMatchesIRExecWithInternals] at hmatch ⊢ <;>
-- SORRY'D:     simp [stmtResultMatchesIRExecWithInternals, hmatch]

private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by sorry
-- SORRY'D:   induction head with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       simp [List.cons_append]
-- SORRY'D:       omega

private theorem scopeNamesIncluded_stmtNextScope
    {scope inScopeNames : List String}
    {stmt : Stmt}
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    FunctionBody.scopeNamesIncluded
      (stmtNextScope scope stmt)
      (collectStmtNames stmt ++ inScopeNames) := by
  intro name hname
  rcases List.mem_append.mp hname with hhead | htail
  · exact List.mem_append.mpr <| Or.inl hhead
  · exact List.mem_append.mpr <| Or.inr <| hincluded name htail

private theorem execIRStmts_append_of_continue
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead : execIRStmts fuel state head = .continue next) :
    execIRStmts fuel state (head ++ tail) =
      execIRStmts (fuel - head.length) next tail := by sorry
-- SORRY'D:   induction head generalizing fuel state with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp at hhead
-- SORRY'D:       subst hhead
-- SORRY'D:       simp
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       cases fuel with
-- SORRY'D:       | zero =>
-- SORRY'D:           simp [execIRStmts] at hhead
-- SORRY'D:       | succ fuel =>
-- SORRY'D:           simp [execIRStmts] at hhead ⊢
-- SORRY'D:           cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead
-- SORRY'D:           case continue next' =>
-- SORRY'D:             simpa using ih fuel next' hhead

private theorem execIRStmts_append_of_not_continue
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResult)
    (hhead : execIRStmts fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmts fuel state (head ++ tail) = irExec := by sorry
-- SORRY'D:   induction head generalizing fuel state with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp at hhead
-- SORRY'D:       subst hhead
-- SORRY'D:       exact False.elim (hnot state rfl)
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       cases fuel with
-- SORRY'D:       | zero =>
-- SORRY'D:           simp [execIRStmts] at hhead ⊢
-- SORRY'D:       | succ fuel =>
-- SORRY'D:           simp [execIRStmts] at hhead ⊢
-- SORRY'D:           cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead ⊢
-- SORRY'D:           case continue next' =>
-- SORRY'D:             exact ih fuel next' hhead hnot
-- SORRY'D:           case return value state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmts, hstmt]

private theorem execIRStmtsWithInternals_append_of_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) =
      execIRStmtsWithInternals runtimeContract (fuel - head.length) next tail := by sorry
-- SORRY'D:   induction head generalizing fuel state with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp at hhead
-- SORRY'D:       subst hhead
-- SORRY'D:       simp
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       cases fuel with
-- SORRY'D:       | zero =>
-- SORRY'D:           simp [execIRStmtsWithInternals] at hhead
-- SORRY'D:       | succ fuel =>
-- SORRY'D:           simp [execIRStmtsWithInternals] at hhead ⊢
-- SORRY'D:           cases hstmt : execIRStmtWithInternals runtimeContract fuel state stmt <;>
-- SORRY'D:             simp [hstmt] at hhead
-- SORRY'D:           case continue next' =>
-- SORRY'D:             simpa using ih fuel next' hhead

private theorem execIRStmtsWithInternals_append_of_not_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResultWithInternals)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) = irExec := by sorry
-- SORRY'D:   induction head generalizing fuel state with
-- SORRY'D:   | nil =>
-- SORRY'D:       simp at hhead
-- SORRY'D:       subst hhead
-- SORRY'D:       exact False.elim (hnot state rfl)
-- SORRY'D:   | cons stmt rest ih =>
-- SORRY'D:       cases fuel with
-- SORRY'D:       | zero =>
-- SORRY'D:           simp [execIRStmtsWithInternals] at hhead ⊢
-- SORRY'D:       | succ fuel =>
-- SORRY'D:           simp [execIRStmtsWithInternals] at hhead ⊢
-- SORRY'D:           cases hstmt : execIRStmtWithInternals runtimeContract fuel state stmt <;>
-- SORRY'D:             simp [hstmt] at hhead ⊢
-- SORRY'D:           case continue next' =>
-- SORRY'D:             exact ih fuel next' hhead hnot
-- SORRY'D:           case return value state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmtsWithInternals, hstmt]
-- SORRY'D:           case stop state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmtsWithInternals, hstmt]
-- SORRY'D:           case revert state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmtsWithInternals, hstmt]
-- SORRY'D:           case leave state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmtsWithInternals, hstmt]
-- SORRY'D:           case stop state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmts, hstmt]
-- SORRY'D:           case revert state' =>
-- SORRY'D:             cases hhead
-- SORRY'D:             simp [execIRStmts, hstmt]

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
        irExec := by sorry
-- SORRY'D:   induction hgeneric generalizing runtime state inScopeNames extraFuel with
-- SORRY'D:   | nil =>
-- SORRY'D:       refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
-- SORRY'D:       exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       have hnextIncluded :
-- SORRY'D:           FunctionBody.scopeNamesIncluded
-- SORRY'D:             (stmtNextScope scope stmt)
-- SORRY'D:             (collectStmtNames stmt ++ inScopeNames) :=
-- SORRY'D:         scopeNamesIncluded_stmtNextScope hincluded
-- SORRY'D:       rcases ih
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (extraFuel := 0)
-- SORRY'D:           hnextIncluded hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem⟩
-- SORRY'D:       let bodyIR := compiledIR ++ tailIR
-- SORRY'D:       have hbodyCompile :
-- SORRY'D:           CompilationModel.compileStmtList
-- SORRY'D:             fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
-- SORRY'D:               Except.ok bodyIR := by
-- SORRY'D:         exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:           hstep.compileOk htailCompile
-- SORRY'D:       let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
-- SORRY'D:       have hheadSlack :
-- SORRY'D:           sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
-- SORRY'D:         have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
-- SORRY'D:           simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
-- SORRY'D:         dsimp [headExtraFuel]
-- SORRY'D:         omega
-- SORRY'D:       rcases hstep.preserves runtime state headExtraFuel
-- SORRY'D:           hexact hscope hbounded hruntime hheadSlack with
-- SORRY'D:         ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
-- SORRY'D:       refine ⟨bodyIR, hbodyCompile, ?_⟩
-- SORRY'D:       cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:         let tailExtraFuel' :=
-- SORRY'D:           sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
-- SORRY'D:         have htailSem' :=
-- SORRY'D:           ih
-- SORRY'D:             (runtime := _)
-- SORRY'D:             (state := _)
-- SORRY'D:             (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:             (extraFuel := tailExtraFuel')
-- SORRY'D:             hnextIncluded hscope' hexact' hbounded' hruntime'
-- SORRY'D:         rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
-- SORRY'D:         rw [htailCompile] at htailCompile'
-- SORRY'D:         injection htailCompile' with htailEq
-- SORRY'D:         subst htailEq
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .continue ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
-- SORRY'D:           rw [execIRStmts_append_of_continue
-- SORRY'D:               (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:               (state := state)
-- SORRY'D:               (next := ‹IRState›)
-- SORRY'D:               (head := compiledIR)
-- SORRY'D:               (tail := tailIR)
-- SORRY'D:               hheadExec']
-- SORRY'D:           dsimp [tailExtraFuel']
-- SORRY'D:           omega
-- SORRY'D:         rw [show SourceSemantics.execStmtList fields runtime (stmt :: rest) =
-- SORRY'D:             SourceSemantics.execStmtList fields ‹SourceSemantics.RuntimeState› rest by
-- SORRY'D:               simp [SourceSemantics.execStmtList, hsourceHead]]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .stop ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .stop ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .stop ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtList, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [List.foldl] using hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨rfl, hruntime'⟩
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .return ‹Nat› ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .return ‹Nat› ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .return ‹Nat› ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtList, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         exact ⟨rfl, hruntime'⟩
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .revert ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .revert ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .revert ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtList, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simp [stmtStepMatchesIRExec]

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
        irExec := by sorry
-- SORRY'D:   induction hgeneric generalizing runtime state inScopeNames extraFuel with
-- SORRY'D:   | nil =>
-- SORRY'D:       refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
-- SORRY'D:       exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       have hnextIncluded :
-- SORRY'D:           FunctionBody.scopeNamesIncluded
-- SORRY'D:             (stmtNextScope scope stmt)
-- SORRY'D:             (collectStmtNames stmt ++ inScopeNames) :=
-- SORRY'D:         scopeNamesIncluded_stmtNextScope hincluded
-- SORRY'D:       rcases ih
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (extraFuel := 0)
-- SORRY'D:           hnextIncluded hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem⟩
-- SORRY'D:       let bodyIR := compiledIR ++ tailIR
-- SORRY'D:       have hbodyCompile :
-- SORRY'D:           CompilationModel.compileStmtList
-- SORRY'D:             fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
-- SORRY'D:               Except.ok bodyIR := by
-- SORRY'D:         exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:           hstep.compileOk htailCompile
-- SORRY'D:       let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
-- SORRY'D:       have hheadSlack :
-- SORRY'D:           sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
-- SORRY'D:         have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
-- SORRY'D:           simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
-- SORRY'D:         dsimp [headExtraFuel]
-- SORRY'D:         omega
-- SORRY'D:       rcases hstep.preserves runtime state helperFuel headExtraFuel
-- SORRY'D:           hexact hscope hbounded hruntime hheadSlack with
-- SORRY'D:         ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
-- SORRY'D:       refine ⟨bodyIR, hbodyCompile, ?_⟩
-- SORRY'D:       cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:         let tailExtraFuel' :=
-- SORRY'D:           sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
-- SORRY'D:         have htailSem' :=
-- SORRY'D:           ih
-- SORRY'D:             (runtime := _)
-- SORRY'D:             (state := _)
-- SORRY'D:             (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:             (extraFuel := tailExtraFuel')
-- SORRY'D:             hnextIncluded hscope' hexact' hbounded' hruntime'
-- SORRY'D:         rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
-- SORRY'D:         rw [htailCompile] at htailCompile'
-- SORRY'D:         injection htailCompile' with htailEq
-- SORRY'D:         subst htailEq
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .continue ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
-- SORRY'D:           rw [execIRStmts_append_of_continue
-- SORRY'D:               (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:               (state := state)
-- SORRY'D:               (next := ‹IRState›)
-- SORRY'D:               (head := compiledIR)
-- SORRY'D:               (tail := tailIR)
-- SORRY'D:               hheadExec']
-- SORRY'D:           dsimp [tailExtraFuel']
-- SORRY'D:           omega
-- SORRY'D:         rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
-- SORRY'D:             SourceSemantics.execStmtListWithHelpers spec fields helperFuel
-- SORRY'D:               ‹SourceSemantics.RuntimeState› rest by
-- SORRY'D:               simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .stop ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .stop ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .stop ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [List.foldl] using hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨rfl, hruntime'⟩
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .return ‹Nat› ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .return ‹Nat› ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .return ‹Nat› ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         exact ⟨rfl, hruntime'⟩
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:               .revert ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               .revert ‹IRState› := by
-- SORRY'D:           exact execIRStmts_append_of_not_continue
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .revert ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simp [stmtStepMatchesIRExec]

-- TYPESIG_SORRY: theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope inScopeNames : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     (helperFuel : Nat)
-- TYPESIG_SORRY:     (extraFuel : Nat)
-- TYPESIG_SORRY:     (hfuelPos : 0 < helperFuel)
-- TYPESIG_SORRY:     (hgeneric :
-- TYPESIG_SORRY:       StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
-- TYPESIG_SORRY:     (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
-- TYPESIG_SORRY:     (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hbounded : FunctionBody.bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
-- TYPESIG_SORRY:     ∃ bodyIR,
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
-- TYPESIG_SORRY:       let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
-- TYPESIG_SORRY:       let irExec := by sorry
-- SORRY'D:         execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
-- SORRY'D:       stmtStepMatchesIRExecWithInternals
-- SORRY'D:         fields
-- SORRY'D:         (List.foldl stmtNextScope scope stmts)
-- SORRY'D:         sourceResult
-- SORRY'D:         irExec := by
-- SORRY'D:   induction hgeneric generalizing runtime state inScopeNames extraFuel with
-- SORRY'D:   | nil =>
-- SORRY'D:       refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
-- SORRY'D:       exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
-- SORRY'D:   | @cons scope stmt compiledIR rest hstep hrest ih =>
-- SORRY'D:       have hnextIncluded :
-- SORRY'D:           FunctionBody.scopeNamesIncluded
-- SORRY'D:             (stmtNextScope scope stmt)
-- SORRY'D:             (collectStmtNames stmt ++ inScopeNames) :=
-- SORRY'D:         scopeNamesIncluded_stmtNextScope hincluded
-- SORRY'D:       rcases ih
-- SORRY'D:           (runtime := runtime)
-- SORRY'D:           (state := state)
-- SORRY'D:           (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:           (extraFuel := 0)
-- SORRY'D:           hnextIncluded hscope hexact hbounded hruntime with
-- SORRY'D:         ⟨tailIR, htailCompile, htailSem⟩
-- SORRY'D:       let bodyIR := compiledIR ++ tailIR
-- SORRY'D:       have hbodyCompile :
-- SORRY'D:           CompilationModel.compileStmtList
-- SORRY'D:             fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
-- SORRY'D:               Except.ok bodyIR := by
-- SORRY'D:         exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
-- SORRY'D:           hstep.compileOk htailCompile
-- SORRY'D:       let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
-- SORRY'D:       have hheadSlack :
-- SORRY'D:           sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
-- SORRY'D:         have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
-- SORRY'D:           simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
-- SORRY'D:         dsimp [headExtraFuel]
-- SORRY'D:         omega
-- SORRY'D:       rcases hstep.preserves runtime state helperFuel headExtraFuel
-- SORRY'D:           hfuelPos hexact hscope hbounded hruntime hheadSlack with
-- SORRY'D:         ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
-- SORRY'D:       refine ⟨bodyIR, hbodyCompile, ?_⟩
-- SORRY'D:       cases sourceHead <;> cases irHead <;>
-- SORRY'D:         simp [stmtStepMatchesIRExecWithInternals] at hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
-- SORRY'D:         let tailExtraFuel' :=
-- SORRY'D:           sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
-- SORRY'D:         have htailSem' :=
-- SORRY'D:           ih
-- SORRY'D:             (runtime := _)
-- SORRY'D:             (state := _)
-- SORRY'D:             (inScopeNames := collectStmtNames stmt ++ inScopeNames)
-- SORRY'D:             (extraFuel := tailExtraFuel')
-- SORRY'D:             hfuelPos hnextIncluded hscope' hexact' hbounded' hruntime'
-- SORRY'D:         rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
-- SORRY'D:         rw [htailCompile] at htailCompile'
-- SORRY'D:         injection htailCompile' with htailEq
-- SORRY'D:         subst htailEq
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:                 .continue ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:               execIRStmtsWithInternals runtimeContract
-- SORRY'D:                 (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
-- SORRY'D:           rw [execIRStmtsWithInternals_append_of_continue
-- SORRY'D:               (runtimeContract := runtimeContract)
-- SORRY'D:               (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:               (state := state)
-- SORRY'D:               (next := ‹IRState›)
-- SORRY'D:               (head := compiledIR)
-- SORRY'D:               (tail := tailIR)
-- SORRY'D:               hheadExec']
-- SORRY'D:           dsimp [tailExtraFuel']
-- SORRY'D:           omega
-- SORRY'D:         rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
-- SORRY'D:             SourceSemantics.execStmtListWithHelpers spec fields helperFuel
-- SORRY'D:               ‹SourceSemantics.RuntimeState› rest by
-- SORRY'D:               simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:                 .stop ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:                 .stop ‹IRState› := by
-- SORRY'D:           exact execIRStmtsWithInternals_append_of_not_continue
-- SORRY'D:             (runtimeContract := runtimeContract)
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .stop ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simpa [List.foldl] using hheadMatch
-- SORRY'D:       ·
-- SORRY'D:         rcases hheadMatch with ⟨rfl, hruntime'⟩
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:                 .return ‹Nat› ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:                 .return ‹Nat› ‹IRState› := by
-- SORRY'D:           exact execIRStmtsWithInternals_append_of_not_continue
-- SORRY'D:             (runtimeContract := runtimeContract)
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .return ‹Nat› ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         exact ⟨rfl, hruntime'⟩
-- SORRY'D:       ·
-- SORRY'D:         have hheadExec' :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state compiledIR =
-- SORRY'D:                 .revert ‹IRState› := by
-- SORRY'D:           simpa [headExtraFuel, bodyIR] using hheadExec
-- SORRY'D:         have hfullExec :
-- SORRY'D:             execIRStmtsWithInternals runtimeContract
-- SORRY'D:               (sizeOf bodyIR + extraFuel + 1) state bodyIR =
-- SORRY'D:                 .revert ‹IRState› := by
-- SORRY'D:           exact execIRStmtsWithInternals_append_of_not_continue
-- SORRY'D:             (runtimeContract := runtimeContract)
-- SORRY'D:             (fuel := sizeOf bodyIR + extraFuel + 1)
-- SORRY'D:             (state := state)
-- SORRY'D:             (head := compiledIR)
-- SORRY'D:             (tail := tailIR)
-- SORRY'D:             (irExec := .revert ‹IRState›)
-- SORRY'D:             hheadExec'
-- SORRY'D:             (by intro next hcontra; simp at hcontra)
-- SORRY'D:         rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
-- SORRY'D:         rw [hfullExec]
-- SORRY'D:         simp [stmtStepMatchesIRExecWithInternals]

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
  rcases exec_compileStmtList_generic_sizeOf_extraFuel_step
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (inScopeNames := inScopeNames)
      (stmts := stmts)
      (extraFuel := extraFuel)
      hgeneric
      hincluded
      hscope
      hexact
      hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, hcompile, ?_⟩
  exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hstep

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
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (inScopeNames := inScopeNames)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hgeneric
      hincluded
      hscope
      hexact
      hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, hcompile, ?_⟩
  exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hstep

-- TYPESIG_SORRY: theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {runtime : SourceSemantics.RuntimeState}
-- TYPESIG_SORRY:     {state : IRState}
-- TYPESIG_SORRY:     {scope inScopeNames : List String}
-- TYPESIG_SORRY:     {stmts : List Stmt}
-- TYPESIG_SORRY:     (helperFuel : Nat)
-- TYPESIG_SORRY:     (extraFuel : Nat)
-- TYPESIG_SORRY:     (hfuelPos : 0 < helperFuel)
-- TYPESIG_SORRY:     (hgeneric :
-- TYPESIG_SORRY:       StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
-- TYPESIG_SORRY:     (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames)
-- TYPESIG_SORRY:     (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
-- TYPESIG_SORRY:     (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
-- TYPESIG_SORRY:     (hbounded : FunctionBody.bindingsBounded runtime.bindings)
-- TYPESIG_SORRY:     (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
-- TYPESIG_SORRY:     ∃ bodyIR,
-- TYPESIG_SORRY:       CompilationModel.compileStmtList
-- TYPESIG_SORRY:         fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR ∧
-- TYPESIG_SORRY:       let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
-- TYPESIG_SORRY:       let irExec := by sorry
-- SORRY'D:         execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
-- SORRY'D:       stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
-- SORRY'D:   rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (runtime := runtime)
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := scope)
-- SORRY'D:       (inScopeNames := inScopeNames)
-- SORRY'D:       (stmts := stmts)
-- SORRY'D:       (helperFuel := helperFuel)
-- SORRY'D:       (extraFuel := extraFuel)
-- SORRY'D:       hfuelPos
-- SORRY'D:       hgeneric
-- SORRY'D:       hincluded
-- SORRY'D:       hscope
-- SORRY'D:       hexact
-- SORRY'D:       hbounded
-- SORRY'D:       hruntime with
-- SORRY'D:     ⟨bodyIR, hcompile, hstep⟩
-- SORRY'D:   refine ⟨bodyIR, hcompile, ?_⟩
-- SORRY'D:   exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep

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
        (SourceSemantics.effectiveFields model) sourceResult irExec := by sorry
-- SORRY'D:   have hstateRuntime' :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         state := by
-- SORRY'D:     simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
-- SORRY'D:   have hbodyCompile' :
-- SORRY'D:       compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
-- SORRY'D:     simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
-- SORRY'D:   have hscopeExact :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope
-- SORRY'D:         (fn.params.map (·.name)) bindings state :=
-- SORRY'D:     FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
-- SORRY'D:   let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
-- SORRY'D:   rcases exec_compileStmtList_generic_sizeOf_extraFuel
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                     bindings := bindings })
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (inScopeNames := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (extraFuel := sizeSlack)
-- SORRY'D:       hgeneric
-- SORRY'D:       FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:       hscope
-- SORRY'D:       hscopeExact
-- SORRY'D:       hbounded
-- SORRY'D:       hstateRuntime' with
-- SORRY'D:     ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
-- SORRY'D:   have hbodyEq : bodyIR = bodyStmts := by
-- SORRY'D:     rw [hbodyCompile'] at hbodyGenericCompile
-- SORRY'D:     injection hbodyGenericCompile with hEq
-- SORRY'D:     exact hEq.symm
-- SORRY'D:   subst bodyIR
-- SORRY'D:   have hfuel :
-- SORRY'D:       sizeOf bodyStmts + sizeSlack + 1 =
-- SORRY'D:         bodyStmts.length + extraFuel + 1 := by
-- SORRY'D:     dsimp [sizeSlack]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, rfl, ?_, ?_⟩
-- SORRY'D:   · simpa [hfuel] using rfl
-- SORRY'D:   · simpa [hfuel, sizeSlack] using hgenericSem

-- SORRY'D: /-- Exact helper-aware body theorem for a helper-aware generic statement
-- SORRY'D: induction witness. This is the induction-level target needed to replace the
-- SORRY'D: current helper-free `SupportedStmtList` gate with compositional helper-step
-- SORRY'D: proofs. -/
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
        (SourceSemantics.effectiveFields model) sourceResult irExec := by sorry
-- SORRY'D:   have hstateRuntime' :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         state := by
-- SORRY'D:     simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
-- SORRY'D:   have hbodyCompile' :
-- SORRY'D:       compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
-- SORRY'D:     simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
-- SORRY'D:   have hscopeExact :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope
-- SORRY'D:         (fn.params.map (·.name)) bindings state :=
-- SORRY'D:     FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
-- SORRY'D:   let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
-- SORRY'D:   rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                     bindings := bindings })
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (inScopeNames := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (helperFuel := helperFuel)
-- SORRY'D:       (extraFuel := sizeSlack)
-- SORRY'D:       hgeneric
-- SORRY'D:       FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:       hscope
-- SORRY'D:       hscopeExact
-- SORRY'D:       hbounded
-- SORRY'D:       hstateRuntime' with
-- SORRY'D:     ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
-- SORRY'D:   have hbodyEq : bodyIR = bodyStmts := by
-- SORRY'D:     rw [hbodyCompile'] at hbodyGenericCompile
-- SORRY'D:     injection hbodyGenericCompile with hEq
-- SORRY'D:     exact hEq.symm
-- SORRY'D:   subst bodyIR
-- SORRY'D:   have hfuel :
-- SORRY'D:       sizeOf bodyStmts + sizeSlack + 1 =
-- SORRY'D:         bodyStmts.length + extraFuel + 1 := by
-- SORRY'D:     dsimp [sizeSlack]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, rfl, ?_, ?_⟩
-- SORRY'D:   · simpa [hfuel] using rfl
-- SORRY'D:   · simpa [hfuel, sizeSlack] using hgenericSem

-- SORRY'D: /-- Exact helper-aware body theorem for an exact helper-aware generic
-- SORRY'D: statement-induction witness. Unlike the transitional legacy-compiled-body
-- SORRY'D: theorem, this already targets `execIRStmtsWithInternals`, so future helper-call
-- SORRY'D: cases can be proved against the compiled semantics that actually executes
-- SORRY'D: helper-rich Yul. -/
-- SORRY'D: private theorem
-- SORRY'D:     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (bodyStmts : List YulStmt)
-- SORRY'D:     (helperFuel : Nat)
-- SORRY'D:     (tx : IRTransaction)
-- SORRY'D:     (initialWorld : Verity.ContractState)
-- SORRY'D:     (state : IRState)
-- SORRY'D:     (bindings : List (String × Nat))
-- SORRY'D:     (extraFuel : Nat)
-- SORRY'D:     (hextraFuel : sizeOf bodyStmts - bodyStmts.length ≤ extraFuel)
-- SORRY'D:     (hfuelPos : 0 < helperFuel)
-- SORRY'D:     (hnormalized : SourceSemantics.effectiveFields model = model.fields)
-- SORRY'D:     (hnoEvents : model.events = [])
-- SORRY'D:     (hnoErrors : model.errors = [])
-- SORRY'D:     (hgeneric :
-- SORRY'D:       StmtListGenericWithHelpersAndHelperIR
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hbodyCompile :
-- SORRY'D:       compileStmtList model.fields model.events model.errors .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts)
-- SORRY'D:     (hscope :
-- SORRY'D:       FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
-- SORRY'D:     (hbounded : FunctionBody.bindingsBounded bindings)
-- SORRY'D:     (hstateRuntime :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := [] }
-- SORRY'D:         state)
-- SORRY'D:     (hstateBindings :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVars bindings state) :
-- SORRY'D:     SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
-- SORRY'D:       runtimeContract
-- SORRY'D:       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
-- SORRY'D:   have hstateRuntime' :
-- SORRY'D:       FunctionBody.runtimeStateMatchesIR
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:           bindings := bindings }
-- SORRY'D:         state := by
-- SORRY'D:     simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
-- SORRY'D:   have hbodyCompile' :
-- SORRY'D:       compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
-- SORRY'D:         (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
-- SORRY'D:     simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
-- SORRY'D:   have hscopeExact :
-- SORRY'D:       FunctionBody.bindingsExactlyMatchIRVarsOnScope
-- SORRY'D:         (fn.params.map (·.name)) bindings state :=
-- SORRY'D:     FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
-- SORRY'D:   let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
-- SORRY'D:   rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (fields := SourceSemantics.effectiveFields model)
-- SORRY'D:       (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
-- SORRY'D:                     bindings := bindings })
-- SORRY'D:       (state := state)
-- SORRY'D:       (scope := fn.params.map (·.name))
-- SORRY'D:       (inScopeNames := fn.params.map (·.name))
-- SORRY'D:       (stmts := fn.body)
-- SORRY'D:       (helperFuel := helperFuel)
-- SORRY'D:       (extraFuel := sizeSlack)
-- SORRY'D:       hfuelPos
-- SORRY'D:       hgeneric
-- SORRY'D:       FunctionBody.scopeNamesIncluded_refl
-- SORRY'D:       hscope
-- SORRY'D:       hscopeExact
-- SORRY'D:       hbounded
-- SORRY'D:       hstateRuntime' with
-- SORRY'D:     ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
-- SORRY'D:   have hbodyEq : bodyIR = bodyStmts := by
-- SORRY'D:     rw [hbodyCompile'] at hbodyGenericCompile
-- SORRY'D:     injection hbodyGenericCompile with hEq
-- SORRY'D:     exact hEq.symm
-- SORRY'D:   subst bodyIR
-- SORRY'D:   have hfuel :
-- SORRY'D:       sizeOf bodyStmts + sizeSlack + 1 =
-- SORRY'D:         bodyStmts.length + extraFuel + 1 := by
-- SORRY'D:     dsimp [sizeSlack]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, rfl, ?_, ?_⟩
-- SORRY'D:   · simpa [hfuel] using rfl
-- SORRY'D:   · simpa [hfuel, sizeSlack] using hgenericSem

-- SORRY'D: /-- Transitional helper-aware body/IR preservation target for the non-core
-- SORRY'D: generic body theorem. This already moves the source side onto helper-aware
-- SORRY'D: semantics, but the compiled side still runs through legacy `execIRStmts`, so it
-- SORRY'D: only matches the current helper-free compiled-body boundary. -/
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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:   refine ⟨sourceResult, match irExec with
-- SORRY'D:       | .continue next => .continue next
-- SORRY'D:       | .return value next => .return value next
-- SORRY'D:       | .stop next => .stop next
-- SORRY'D:       | .revert next => .revert next, hsource, ?_, ?_⟩
-- SORRY'D:   · have hcompat :=
-- SORRY'D:       execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
-- SORRY'D:         (bodyStmts.length + extraFuel + 1)
-- SORRY'D:         state
-- SORRY'D:         bodyStmts
-- SORRY'D:         hdisjoint
-- SORRY'D:     simpa [hbodyExec] using hcompat
-- SORRY'D:   · cases irExec <;> simpa [stmtResultMatchesIRExecWithInternals] using hmatch

-- SORRY'D: /-- Under compiled-body disjointness, the exact helper-aware body goal can also
-- SORRY'D: be collapsed back to the legacy compiled-body goal. This keeps the new exact
-- SORRY'D: helper-aware seam reusable with the existing function-level theorem surface
-- SORRY'D: until callers are ready to retarget all the way to `execIRFunctionWithInternals`. -/
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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
-- SORRY'D:   cases irExec with
-- SORRY'D:   | continue next =>
-- SORRY'D:       refine ⟨sourceResult, .continue next, hsource, ?_, ?_⟩
-- SORRY'D:       · have hcompat :=
-- SORRY'D:           execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
-- SORRY'D:             (bodyStmts.length + extraFuel + 1)
-- SORRY'D:             state
-- SORRY'D:             bodyStmts
-- SORRY'D:             hdisjoint
-- SORRY'D:         rw [← hcompat]
-- SORRY'D:         simpa using hbodyExec
-- SORRY'D:       · simpa [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec] using
-- SORRY'D:           hmatch
-- SORRY'D:   | return value next =>
-- SORRY'D:       refine ⟨sourceResult, .return value next, hsource, ?_, ?_⟩
-- SORRY'D:       · have hcompat :=
-- SORRY'D:           execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
-- SORRY'D:             (bodyStmts.length + extraFuel + 1)
-- SORRY'D:             state
-- SORRY'D:             bodyStmts
-- SORRY'D:             hdisjoint
-- SORRY'D:         rw [← hcompat]
-- SORRY'D:         simpa using hbodyExec
-- SORRY'D:       · simpa [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec] using
-- SORRY'D:           hmatch
-- SORRY'D:   | stop next =>
-- SORRY'D:       refine ⟨sourceResult, .stop next, hsource, ?_, ?_⟩
-- SORRY'D:       · have hcompat :=
-- SORRY'D:           execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
-- SORRY'D:             (bodyStmts.length + extraFuel + 1)
-- SORRY'D:             state
-- SORRY'D:             bodyStmts
-- SORRY'D:             hdisjoint
-- SORRY'D:         rw [← hcompat]
-- SORRY'D:         simpa using hbodyExec
-- SORRY'D:       · simpa [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec] using
-- SORRY'D:           hmatch
-- SORRY'D:   | revert next =>
-- SORRY'D:       refine ⟨sourceResult, .revert next, hsource, ?_, ?_⟩
-- SORRY'D:       · have hcompat :=
-- SORRY'D:           execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
-- SORRY'D:             (bodyStmts.length + extraFuel + 1)
-- SORRY'D:             state
-- SORRY'D:             bodyStmts
-- SORRY'D:             hdisjoint
-- SORRY'D:         rw [← hcompat]
-- SORRY'D:         simpa using hbodyExec
-- SORRY'D:       · simpa [stmtResultMatchesIRExecWithInternals, FunctionBody.stmtResultMatchesIRExec] using
-- SORRY'D:           hmatch
-- SORRY'D:   | leave _ =>
-- SORRY'D:       cases hmatch

-- SORRY'D: /-- Exact helper-aware body theorem for a helper-aware generic statement
-- SORRY'D: induction witness. This is the induction-level target needed to replace the
-- SORRY'D: current helper-free `SupportedStmtList` gate with compositional helper-step
-- SORRY'D: proofs. -/
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
  exact supported_function_body_correct_from_exact_state_generic_helper_steps_raw
    model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
    hextraFuel hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
    hbounded hstateRuntime hstateBindings

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   exact
-- SORRY'D:     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
-- SORRY'D:       runtimeContract
-- SORRY'D:       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
-- SORRY'D:       hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
-- SORRY'D:       hbounded hstateRuntime hstateBindings

-- SORRY'D: /-- Body-level exact helper-aware bridge for the future helper-rich theorem
-- SORRY'D: path: helper-free heads only need the weaker helper-free source/compiled reuse
-- SORRY'D: witnesses, while helper-surface-positive heads are supplied directly by the
-- SORRY'D: exact helper-step interface. This removes the structural requirement that the
-- SORRY'D: whole body already satisfy `StmtListGenericCore` before helper-rich cases can
-- SORRY'D: enter the exact compiled theorem target. -/
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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   have hgeneric :
-- SORRY'D:       StmtListGenericWithHelpersAndHelperIR
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (hhelperFree := hhelperFree)
-- SORRY'D:       (hsteps := hsteps)
-- SORRY'D:       (hlegacy := hlegacy)
-- SORRY'D:       hinternal
-- SORRY'D:   exact
-- SORRY'D:     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
-- SORRY'D:       runtimeContract
-- SORRY'D:       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
-- SORRY'D:       hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
-- SORRY'D:       hbounded hstateRuntime hstateBindings

-- SORRY'D: /-- Body-level exact helper-aware bridge over the split helper-positive
-- SORRY'D: interfaces: genuine internal-helper heads are discharged separately from the
-- SORRY'D: residual coarse helper-surface heads, so future helper-summary work does not
-- SORRY'D: also need to prove unrelated non-helper exact-step cases. -/
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
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hinternal := hinternalSteps)
      (hresidual := hresidualSteps)
      (hlegacy := hlegacy)
      hnoInternalFunctions
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

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
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hcall := hcall)
      (hassign := hassign)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   have hgeneric :
-- SORRY'D:       StmtListGenericWithHelpersAndHelperIR
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := model)
-- SORRY'D:       (hhelperFree := hhelperFree)
-- SORRY'D:       (hdirect := hdirect)
-- SORRY'D:       (hexpr := hexpr)
-- SORRY'D:       (hstruct := hstruct)
-- SORRY'D:       (hresidual := hresidual)
-- SORRY'D:       (hlegacy := hlegacy)
-- SORRY'D:       hnoInternalFunctions
-- SORRY'D:   exact
-- SORRY'D:     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
-- SORRY'D:       runtimeContract
-- SORRY'D:       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
-- SORRY'D:       hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
-- SORRY'D:       hbounded hstateRuntime hstateBindings

-- SORRY'D: private theorem
-- SORRY'D:     generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (model : CompilationModel)
-- SORRY'D:     (fn : FunctionSpec)
-- SORRY'D:     (hhelperFree :
-- SORRY'D:       StmtListHelperFreeStepInterface
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hcall :
-- SORRY'D:       StmtListDirectInternalHelperCallStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hassign :
-- SORRY'D:       StmtListDirectInternalHelperAssignStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hexpr :
-- SORRY'D:       StmtListExprInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hstruct :
-- SORRY'D:       StmtListStructuralInternalHelperStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hresidual :
-- SORRY'D:       StmtListResidualHelperSurfaceStepInterface
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body)
-- SORRY'D:     (hdisjoint :
-- SORRY'D:       StmtListHelperFreeCompiledCallsDisjoint
-- SORRY'D:         runtimeContract
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body) :
-- SORRY'D:     StmtListGenericWithHelpersAndHelperIR
-- SORRY'D:       runtimeContract
-- SORRY'D:       model
-- SORRY'D:       (SourceSemantics.effectiveFields model)
-- SORRY'D:       (fn.params.map (·.name))
-- SORRY'D:       fn.body :=
-- SORRY'D:   stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
-- SORRY'D:     (runtimeContract := runtimeContract)
-- SORRY'D:     (spec := model)
-- SORRY'D:     (hhelperFree := hhelperFree)
-- SORRY'D:     (hsteps :=
-- SORRY'D:       stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
-- SORRY'D:         (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
-- SORRY'D:           (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
-- SORRY'D:             hcall
-- SORRY'D:             hassign)
-- SORRY'D:           hexpr
-- SORRY'D:           hstruct)
-- SORRY'D:         hresidual)
-- SORRY'D:     (hdisjoint := hdisjoint)

-- SORRY'D: /-- Disjoint-based body-level exact helper-aware bridge over the fully split
-- SORRY'D: genuine-helper interfaces.  Replaces `StmtListHelperFreeCompiledLegacyCompatible`
-- SORRY'D: + `runtimeContract.internalFunctions = []` with the weaker
-- SORRY'D: `StmtListHelperFreeCompiledCallsDisjoint`.  This is the entry point for
-- SORRY'D: function bodies that live in a contract with an internal helper table. -/
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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by sorry
-- SORRY'D:   have hgeneric :
-- SORRY'D:       StmtListGenericWithHelpersAndHelperIR
-- SORRY'D:         runtimeContract
-- SORRY'D:         model
-- SORRY'D:         (SourceSemantics.effectiveFields model)
-- SORRY'D:         (fn.params.map (·.name))
-- SORRY'D:         fn.body :=
-- SORRY'D:     generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
-- SORRY'D:       runtimeContract model fn hhelperFree hcall hassign hexpr hstruct hresidual
-- SORRY'D:       hdisjoint
-- SORRY'D:   exact
-- SORRY'D:     supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
-- SORRY'D:       runtimeContract
-- SORRY'D:       model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
-- SORRY'D:       hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
-- SORRY'D:       hbounded hstateRuntime hstateBindings

-- SORRY'D: /-- Current-fragment disjointness-based wrapper that lands directly in the exact
-- SORRY'D: helper-aware compiled body goal. This keeps the existing helper-free step
-- SORRY'D: library reusable while exposing the weaker compiled-side condition that later
-- SORRY'D: helper-table work actually needs. -/
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
  have hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false :=
    stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed
      hcontractSurface
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hhelperFree
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      hdisjoint
      hbodyCompile
      hscope hbounded hstateRuntime hstateBindings

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
  have hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body := by
    simpa [hnormalized] using
      (stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface
        (runtimeContract := runtimeContract)
        (fields := model.fields)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hnoPacked
        hcontractSurface
        hinternal)
  exact
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoPacked hcontractSurface
      hhelperFree hbodyCompile hscope hbounded hstateRuntime hstateBindings hdisjoint

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
  have hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false :=
    stmtListTouchesUnsupportedHelperSurface_eq_false_of_contractSurfaceClosed_exceptMappingWrites
      hcontractSurface
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hhelperFree
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := model)
        (fields := SourceSemantics.effectiveFields model)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hhelperSurface)
      hdisjoint
      hbodyCompile
      hscope hbounded hstateRuntime hstateBindings

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
  have hdisjoint :
      StmtListHelperFreeCompiledCallsDisjoint
        runtimeContract
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body := by
    simpa [hnormalized] using
      (stmtListHelperFreeCompiledCallsDisjoint_of_supportedContractSurface_exceptMappingWrites
        (runtimeContract := runtimeContract)
        (fields := model.fields)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hnoPacked
        hcontractSurface
        hinternal)
  exact
    supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir_except_mapping_writes_callsDisjoint
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoPacked hcontractSurface
      hhelperFree hbodyCompile hscope hbounded hstateRuntime hstateBindings hdisjoint

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
  rcases supported_function_body_correct_from_exact_state_generic
      model fn bodyStmts tx initialWorld state bindings extraFuel hextraFuel
      hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope hbounded
      hstateRuntime hstateBindings with
    ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  refine ⟨sourceResult, irExec, ?_, hbodyExec, hmatch⟩
  simpa [SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal] using
    hhelperGoal.trans hsource

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
  have hgenericWithHelpers :
      StmtListGenericWithHelpers
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
      (spec := model)
      (hhelperFree := hhelperFree)
      hhelperSurface
  exact supported_function_body_correct_from_exact_state_generic_helper_steps
    model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
    hextraFuel hnormalized hnoEvents hnoErrors hgenericWithHelpers hbodyCompile
    hscope hbounded hstateRuntime hstateBindings

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
      compiledIR := by sorry
-- SORRY'D:   refine {
-- SORRY'D:     compileOk := hcompile
-- SORRY'D:     preserves := ?_ }
-- SORRY'D:   intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
-- SORRY'D:   obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCallAssign_shape hcompile
-- SORRY'D:   have hArgEq : argExprs' = argExprs := by
-- SORRY'D:     simp [hargCompile] at hargOk
-- SORRY'D:     exact hargOk.symm
-- SORRY'D:   subst hArgEq
-- SORRY'D:   set singletonIR :=
-- SORRY'D:     [YulStmt.letMany names
-- SORRY'D:       (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]
-- SORRY'D:   have hshape' : compiledIR = singletonIR := by
-- SORRY'D:     simpa [singletonIR] using hshape
-- SORRY'D:   have hlenOne : singletonIR.length = 1 := by
-- SORRY'D:     simp [singletonIR]
-- SORRY'D:   have hExtraPos : 1 ≤ extraFuel := by
-- SORRY'D:     have hsz : sizeOf singletonIR ≥ 2 := by
-- SORRY'D:       simp [singletonIR]
-- SORRY'D:       omega
-- SORRY'D:     rw [hshape'] at hslack
-- SORRY'D:     rw [hlenOne] at hslack
-- SORRY'D:     omega
-- SORRY'D:   set irFuel := extraFuel - 1 with hirFuel
-- SORRY'D:   have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
-- SORRY'D:   have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
-- SORRY'D:     rw [hlenOne, hirFuel]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, ?_, ?_, ?_⟩
-- SORRY'D:   · exact SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:       (Stmt.internalCallAssign names calleeName args)
-- SORRY'D:   · exact execIRStmtsWithInternals runtimeContract (compiledIR.length + extraFuel + 1) state compiledIR
-- SORRY'D:   · rfl
-- SORRY'D:   · rw [hshape', hFuelEq]
-- SORRY'D:   · simpa [singletonIR] using hMatch

-- SORRY'D: /-- Generic `CompiledStmtStepWithHelpersAndHelperIR` constructor for
-- SORRY'D: `Stmt.internalCall` (void internal helper calls).  Analogous to
-- SORRY'D: `compiledStmtStepWithHelpersAndHelperIR_internalCallAssign` but for the
-- SORRY'D: void-call case where the compiled IR is `[.expr (.call yulName argExprs)]`.

-- SORRY'D: The caller supplies a `bridge` hypothesis that ties the source-level
-- SORRY'D: `execStmtWithHelpers` result to the IR-level `execIRStmtsWithInternals` result
-- SORRY'D: on the singleton IR list with `irFuel + 3` fuel. -/
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
      compiledIR := by sorry
-- SORRY'D:   refine {
-- SORRY'D:     compileOk := hcompile
-- SORRY'D:     preserves := ?_ }
-- SORRY'D:   intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
-- SORRY'D:   obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape hcompile
-- SORRY'D:   have hArgEq : argExprs' = argExprs := by
-- SORRY'D:     simp [hargCompile] at hargOk
-- SORRY'D:     exact hargOk.symm
-- SORRY'D:   subst hArgEq
-- SORRY'D:   set singletonIR :=
-- SORRY'D:     [YulStmt.expr
-- SORRY'D:       (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]
-- SORRY'D:   have hshape' : compiledIR = singletonIR := by
-- SORRY'D:     simpa [singletonIR] using hshape
-- SORRY'D:   have hlenOne : singletonIR.length = 1 := by
-- SORRY'D:     simp [singletonIR]
-- SORRY'D:   have hExtraPos : 1 ≤ extraFuel := by
-- SORRY'D:     have hsz : sizeOf singletonIR ≥ 2 := by
-- SORRY'D:       simp [singletonIR]
-- SORRY'D:       omega
-- SORRY'D:     rw [hshape'] at hslack
-- SORRY'D:     rw [hlenOne] at hslack
-- SORRY'D:     omega
-- SORRY'D:   set irFuel := extraFuel - 1 with hirFuel
-- SORRY'D:   have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
-- SORRY'D:   have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
-- SORRY'D:     rw [hlenOne, hirFuel]
-- SORRY'D:     omega
-- SORRY'D:   refine ⟨_, _, ?_, ?_, ?_⟩
-- SORRY'D:   · exact SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:       (Stmt.internalCall calleeName args)
-- SORRY'D:   · exact execIRStmtsWithInternals runtimeContract (compiledIR.length + extraFuel + 1) state compiledIR
-- SORRY'D:   · rfl
-- SORRY'D:   · rw [hshape', hFuelEq]
-- SORRY'D:   · simpa [singletonIR] using hMatch

-- SORRY'D: /-- Non-vacuous list-level constructor for a direct helper-return-binding head.
-- SORRY'D: This packages `compiledStmtStepWithHelpersAndHelperIR_internalCallAssign` into
-- SORRY'D: the split direct-helper step interface expected by the exact helper-aware list
-- SORRY'D: induction seam. -/
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
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

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
  refine ⟨?_, ?_⟩
  · intro calleeName hmem
    exfalso
    simpa [hbody.helperCallNames_nil] using hmem
  · intro calleeName hmem
    exact hassign.assign hmem

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

/-- Reassemble the full compile-side Tier 4 inventory from independently
constructed call and assign halves. -/
-- TYPESIG_SORRY: theorem directInternalHelperPerCalleeCompileCatalog_of_callCatalog_and_assignCatalog
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hcall : DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn)
-- TYPESIG_SORRY:     (hassign : DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperPerCalleeCompileCatalog spec fields fn := by sorry
-- SORRY'D:   refine ⟨?_, ?_⟩
-- SORRY'D:   · intro calleeName hmem scope args
-- SORRY'D:     exact hcall.call hmem
-- SORRY'D:   · intro calleeName hmem scope names args
-- SORRY'D:     exact hassign.assign hmem

-- SORRY'D: /-- Under the current supported statement fragment, every direct helper void
-- SORRY'D: call compile obligation is vacuous because `SupportedStmtList` contains no
-- SORRY'D: helper-call syntax at all. This lets the public Tier 4 seam keep only the
-- SORRY'D: assign-side compile inventory explicit. -/
theorem directInternalHelperPerCalleeCallCompileCatalog_of_supportedBody
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn) :
    DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn := by sorry
-- SORRY'D:   refine ⟨?_⟩
-- SORRY'D:   intro calleeName hmem
-- SORRY'D:   exfalso
-- SORRY'D:   simpa [hbody.helperCallNames_nil] using hmem

-- SORRY'D: /-- Split compile-side Tier 4 inventory. This isolates the purely compilation
-- SORRY'D: obligations from the semantic bridge obligations so future fragment widening can
-- SORRY'D: discharge compile success generically once direct helper calls are admitted into
-- SORRY'D: the supported statement witness. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeCompileCatalog
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   call :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ {scope : List String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:             (Stmt.internalCall calleeName args) = Except.ok compiledIR
-- SORRY'D:   assign :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ {scope : List String} {names : List String} {args : List Expr},
-- SORRY'D:         ∃ compiledIR,
-- SORRY'D:           CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:             (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR

-- SORRY'D: /-- Callee-local runtime-helper witness inventory. This isolates the part of the
-- SORRY'D: Tier 4 seam that is already discharged by the compiled runtime helper table, so
-- SORRY'D: future helper-rank induction does not need to thread lookup/presence facts
-- SORRY'D: through every direct-helper singleton proof. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeRuntimeWitnessCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   witness :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       SupportedCompiledInternalHelperWitness spec runtimeContract calleeName

-- SORRY'D: /-- Build the callee-local runtime-helper witness inventory directly from the
-- SORRY'D: global runtime helper table and the body's existing helper witness inventory. -/
-- TYPESIG_SORRY: theorem directInternalHelperPerCalleeRuntimeWitnessCatalog_of_runtimeHelperTable
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
-- TYPESIG_SORRY:     (hHelpers : SupportedBodyHelperInterface spec fn) :
-- TYPESIG_SORRY:     DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn := by sorry
-- SORRY'D:   refine ⟨?_⟩
-- SORRY'D:   intro calleeName hmem
-- SORRY'D:   exact hRuntime.compiledOfCall hHelpers hmem

-- SORRY'D: /-- Split semantic Tier 4 core. This keeps the end-to-end source/IR step
-- SORRY'D: alignment separate from both compile-success obligations and runtime helper
-- SORRY'D: lookup obligations, matching the eventual division between helper-rank
-- SORRY'D: induction and contract-level helper-table construction. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeSemanticCoreCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   call :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCall calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCall calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.expr (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])
-- SORRY'D:   assign :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {names : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.letMany names (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- SORRY'D: /-- Irreducible semantic Tier 4 kernel. This is the part future helper-rank
-- SORRY'D: induction should actually construct: source helper witnesses and summary
-- SORRY'D: soundness are supplied explicitly, so callers that already carry
-- SORRY'D: `SupportedBodyHelperInterface` plus helper-summary proofs can reassemble the
-- SORRY'D: full semantic core mechanically. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   call :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       (hmem : calleeName ∈ helperCallNames fn) →
-- SORRY'D:       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
-- SORRY'D:       InternalHelperSummarySound spec
-- SORRY'D:         sourceWitness.callee
-- SORRY'D:         sourceWitness.summary.contract →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCall calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCall calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.expr (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])
-- SORRY'D:   assign :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       (hmem : calleeName ∈ helperCallNames fn) →
-- SORRY'D:       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
-- SORRY'D:       InternalHelperSummarySound spec
-- SORRY'D:         sourceWitness.callee
-- SORRY'D:         sourceWitness.summary.contract →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {names : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.letMany names (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- SORRY'D: /-- Call-only half of the irreducible semantic Tier 4 kernel. This lets future
-- SORRY'D: helper-rank induction discharge statement-position void helper calls
-- SORRY'D: independently from helper-return-binding calls. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeCallSemanticKernelCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   call :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       (hmem : calleeName ∈ helperCallNames fn) →
-- SORRY'D:       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
-- SORRY'D:       InternalHelperSummarySound spec
-- SORRY'D:         sourceWitness.callee
-- SORRY'D:         sourceWitness.summary.contract →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCall calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCall calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.expr (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- SORRY'D: /-- Assign-only half of the irreducible semantic Tier 4 kernel. This isolates
-- SORRY'D: the roadmap's current strategic blocker, namely direct helper-return-binding
-- SORRY'D: steps, from the void-call half. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   assign :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       (hmem : calleeName ∈ helperCallNames fn) →
-- SORRY'D:       (sourceWitness : SupportedInternalHelperWitness spec calleeName) →
-- SORRY'D:       InternalHelperSummarySound spec
-- SORRY'D:         sourceWitness.callee
-- SORRY'D:         sourceWitness.summary.contract →
-- SORRY'D:       ∀ (compiledHelper :
-- SORRY'D:           SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
-- SORRY'D:         {scope : List String} {names : List String} {args : List Expr}
-- SORRY'D:         {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:           (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:             [YulStmt.letMany names (YulExpr.call
-- SORRY'D:               (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- SORRY'D: /-- Under the current supported statement fragment, every direct helper call
-- SORRY'D: kernel obligation is vacuous because `SupportedStmtList` contains no helper-call
-- SORRY'D: syntax at all. This lets the public Tier 4 seam focus on the assign side, which
-- SORRY'D: is the actual roadmap blocker. -/
-- TYPESIG_SORRY: theorem directInternalHelperPerCalleeCallSemanticKernelCatalog_of_supportedBody
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hbody : SupportedBodyInterface spec fn) :
-- TYPESIG_SORRY:     DirectInternalHelperPerCalleeCallSemanticKernelCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   refine ⟨?_⟩
-- SORRY'D:   intro calleeName hmem
-- SORRY'D:   exfalso
-- SORRY'D:   simpa [hbody.helperCallNames_nil] using hmem

-- SORRY'D: /-- Reassemble the full semantic kernel from independently constructed call and
-- SORRY'D: assign halves. This lets future helper-rank induction target the assign side
-- SORRY'D: first without changing the downstream bridge machinery. -/
-- TYPESIG_SORRY: theorem directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hcall :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeCallSemanticKernelCatalog
-- TYPESIG_SORRY:         runtimeContract spec fields fn)
-- TYPESIG_SORRY:     (hassign :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- TYPESIG_SORRY:         runtimeContract spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   refine ⟨?_, ?_⟩
-- SORRY'D:   · intro calleeName hmem sourceWitness hsound compiledHelper scope args compiledIR argExprs
-- SORRY'D:       hstmt hargs
-- SORRY'D:     exact
-- SORRY'D:       hcall.call
-- SORRY'D:         hmem
-- SORRY'D:         sourceWitness
-- SORRY'D:         hsound
-- SORRY'D:         compiledHelper
-- SORRY'D:         hstmt
-- SORRY'D:         hargs
-- SORRY'D:   · intro calleeName hmem sourceWitness hsound compiledHelper scope names args compiledIR argExprs
-- SORRY'D:       hstmt hargs
-- SORRY'D:     exact
-- SORRY'D:       hassign.assign
-- SORRY'D:         hmem
-- SORRY'D:         sourceWitness
-- SORRY'D:         hsound
-- SORRY'D:         compiledHelper
-- SORRY'D:         hstmt
-- SORRY'D:         hargs

-- SORRY'D: /-- Reassemble the split semantic Tier 4 core from helper witnesses and summary
-- SORRY'D: soundness already carried by `SupportedBodyHelperInterface`, plus the smaller
-- SORRY'D: semantic kernel future rank induction actually needs to construct. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperPerCalleeSemanticCoreCatalog_of_supportedBodyHelpers_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hHelpers : SupportedBodyHelperInterface spec fn)
-- SORRY'D:     (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog
-- SORRY'D:         runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn := by
-- SORRY'D:   refine ⟨?_, ?_⟩
-- SORRY'D:   · intro calleeName hmem compiledHelper scope args compiledIR argExprs hstmt hargs
-- SORRY'D:     exact
-- SORRY'D:       hkernel.call
-- SORRY'D:         hmem
-- SORRY'D:         (hHelpers.summaryOfCall hmem)
-- SORRY'D:         (hsummaries calleeName hmem)
-- SORRY'D:         compiledHelper
-- SORRY'D:         hstmt
-- SORRY'D:         hargs
-- SORRY'D:   · intro calleeName hmem compiledHelper scope names args compiledIR argExprs hstmt hargs
-- SORRY'D:     exact
-- SORRY'D:       hkernel.assign
-- SORRY'D:         hmem
-- SORRY'D:         (hHelpers.summaryOfCall hmem)
-- SORRY'D:         (hsummaries calleeName hmem)
-- SORRY'D:         compiledHelper
-- SORRY'D:         hstmt
-- SORRY'D:         hargs

-- SORRY'D: /-- Assemble the assign-only callee-local Tier 4 bridge inventory directly from
-- SORRY'D: the assign compile catalog, callee-local runtime helper witnesses, the
-- SORRY'D: supported body's helper-summary inventory, and the irreducible assign semantic
-- SORRY'D: kernel. This packages the exact assign-side proof object future rank induction
-- SORRY'D: should ultimately construct. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperPerCalleeAssignBridgeCatalog_of_assignCompileCatalog_and_runtimeWitnessCatalog_and_supportedBodyHelpers_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hcompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- SORRY'D:     (hHelpers : SupportedBodyHelperInterface spec fn)
-- SORRY'D:     (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn := by
-- SORRY'D:   refine ⟨?_⟩
-- SORRY'D:   intro calleeName hmem
-- SORRY'D:   refine
-- SORRY'D:     { compile := ?_
-- SORRY'D:       bridge := ?_ }
-- SORRY'D:   · intro scope names args
-- SORRY'D:     exact hcompile.assign hmem (scope := scope) (names := names) (args := args)
-- SORRY'D:   · intro scope names args compiledIR argExprs hstmt hargs
-- SORRY'D:     exact
-- SORRY'D:       hkernel.assign
-- SORRY'D:         hmem
-- SORRY'D:         (hHelpers.summaryOfCall hmem)
-- SORRY'D:         (hsummaries calleeName hmem)
-- SORRY'D:         (hruntime.witness hmem)
-- SORRY'D:         hstmt
-- SORRY'D:         hargs

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split assign-side Tier 4 ingredients plus the current supported-body
-- SORRY'D: witness. This keeps downstream theorem seams on the reusable head-step catalog
-- SORRY'D: that future rank induction should ultimately construct, instead of forcing them
-- SORRY'D: to route through the intermediate assign-bridge layer. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hbody : SupportedBodyInterface spec fn)
-- SORRY'D:     (hcompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- SORRY'D:     (hsummaries :
-- SORRY'D:       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hbody
-- SORRY'D:       (directInternalHelperPerCalleeAssignBridgeCatalog_of_assignCompileCatalog_and_runtimeWitnessCatalog_and_supportedBodyHelpers_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hcompile
-- SORRY'D:         hruntime
-- SORRY'D:         hbody.calls.helpers
-- SORRY'D:         hsummaries
-- SORRY'D:         hkernel)

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split assign-side Tier 4 ingredients plus the current supported-body
-- SORRY'D: witness. This keeps downstream theorem seams on the reusable head-step catalog
-- SORRY'D: that future rank induction should ultimately construct, and now lands first on
-- SORRY'D: the exact body-level bridge catalog rather than the derived per-callee
-- SORRY'D: assign-bridge layer. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hbody : SupportedBodyInterface spec fn)
-- SORRY'D:     (hcompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- SORRY'D:     (hsummaries :
-- SORRY'D:       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_bridgeCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hbody
-- SORRY'D:         hcompile
-- SORRY'D:         hruntime
-- SORRY'D:         hsummaries
-- SORRY'D:         hkernel)

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split assign-side compile/runtime-helper-table/semantic-kernel Tier 4
-- SORRY'D: ingredients plus the current supported-body witness. This removes the last
-- SORRY'D: runtime-witness repackaging step on the assign-first theorem chain. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hbody : SupportedBodyInterface spec fn)
-- SORRY'D:     (hcompile :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
-- SORRY'D:     (hsummaries :
-- SORRY'D:       SupportedBodyHelperSummariesSound spec fn hbody.calls.helpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog
-- SORRY'D:         runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBody_and_assignCompileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_assignSemanticKernelCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hbody
-- SORRY'D:       hcompile
-- SORRY'D:       (directInternalHelperPerCalleeRuntimeWitnessCatalog_of_runtimeHelperTable
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hruntime
-- SORRY'D:         hbody.calls.helpers)
-- SORRY'D:       hsummaries
-- SORRY'D:       hkernel

-- SORRY'D: /-- Split semantic Tier 4 inventory. This keeps the end-to-end source/IR step
-- SORRY'D: alignment separate from the compile-success obligations, matching the eventual
-- SORRY'D: division between helper-rank induction and fragment-widening compile lemmas. -/
-- SORRY'D: structure DirectInternalHelperPerCalleeSemanticBridgeCatalog
-- SORRY'D:     (runtimeContract : IRContract)
-- SORRY'D:     (spec : CompilationModel)
-- SORRY'D:     (fields : List Field)
-- SORRY'D:     (fn : FunctionSpec) : Prop where
-- SORRY'D:   call :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ {scope : List String} {args : List Expr}
-- SORRY'D:           {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCall calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCall calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCall calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.expr (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])
-- SORRY'D:   assign :
-- SORRY'D:     ∀ {calleeName : String},
-- SORRY'D:       calleeName ∈ helperCallNames fn →
-- SORRY'D:       ∀ {scope : List String} {names : List String} {args : List Expr}
-- SORRY'D:           {compiledIR : List YulStmt} {argExprs : List YulExpr},
-- SORRY'D:         CompilationModel.compileStmt fields [] [] .calldata [] false scope
-- SORRY'D:           (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
-- SORRY'D:         CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
-- SORRY'D:         ∀ (runtime : SourceSemantics.RuntimeState)
-- SORRY'D:           (state : IRState)
-- SORRY'D:           (helperFuel : Nat)
-- SORRY'D:           (irFuel : Nat),
-- SORRY'D:           0 < helperFuel →
-- SORRY'D:           FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
-- SORRY'D:           FunctionBody.scopeNamesPresent scope runtime.bindings →
-- SORRY'D:           FunctionBody.bindingsBounded runtime.bindings →
-- SORRY'D:           FunctionBody.runtimeStateMatchesIR fields runtime state →
-- SORRY'D:           stmtStepMatchesIRExecWithInternals fields
-- SORRY'D:             (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
-- SORRY'D:               (Stmt.internalCallAssign names calleeName args))
-- SORRY'D:             (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
-- SORRY'D:               [YulStmt.letMany names (YulExpr.call
-- SORRY'D:                 (CompilationModel.internalFunctionYulName calleeName) argExprs)])

-- SORRY'D: /-- Reassemble the existing semantic bridge inventory once runtime helper
-- SORRY'D: witnesses are available callee-locally. This leaves future rank induction with
-- SORRY'D: just the genuinely semantic work while contract compilation can discharge the
-- SORRY'D: runtime witness side independently. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperPerCalleeSemanticBridgeCatalog_of_runtimeWitnessCatalog_and_semanticCoreCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hruntime :
-- SORRY'D:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- SORRY'D:     (hsemantic :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn := by
-- SORRY'D:   refine ⟨?_, ?_⟩
-- SORRY'D:   · intro calleeName hmem scope args compiledIR argExprs hstmt hargs
-- SORRY'D:     exact hsemantic.call hmem (hruntime.witness hmem) hstmt hargs
-- SORRY'D:   · intro calleeName hmem scope names args compiledIR argExprs hstmt hargs
-- SORRY'D:     exact hsemantic.assign hmem (hruntime.witness hmem) hstmt hargs

-- SORRY'D: /-- Reassemble the existing callee-local Tier 4 bridge object after splitting the
-- SORRY'D: compile and semantic obligations. This is the intended future landing point for
-- SORRY'D: independent fragment-widening and helper-rank-induction developments. -/
-- TYPESIG_SORRY: theorem directInternalHelperPerCalleeBridgeCatalog_of_compileCatalog_and_semanticBridgeCatalog
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- TYPESIG_SORRY:     (hsemantic :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   refine ⟨?_, ?_⟩
-- SORRY'D:   · intro calleeName hmem
-- SORRY'D:     refine
-- SORRY'D:       { compile := ?_
-- SORRY'D:         bridge := ?_ }
-- SORRY'D:     · intro scope args
-- SORRY'D:       exact hcompile.call hmem (scope := scope) (args := args)
-- SORRY'D:     · intro scope args compiledIR argExprs hstmt hargs
-- SORRY'D:       exact hsemantic.call hmem hstmt hargs
-- SORRY'D:   · intro calleeName hmem
-- SORRY'D:     refine
-- SORRY'D:       { compile := ?_
-- SORRY'D:         bridge := ?_ }
-- SORRY'D:     · intro scope names args
-- SORRY'D:       exact hcompile.assign hmem (scope := scope) (names := names) (args := args)
-- SORRY'D:     · intro scope names args compiledIR argExprs hstmt hargs
-- SORRY'D:       exact hsemantic.assign hmem hstmt hargs

-- SORRY'D: /-- Assemble the existing body-level direct-helper bridge catalog from the more
-- SORRY'D: rank-induction-friendly per-callee bridge inventory. -/
theorem directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcallee : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro scope calleeName args hmem
    exact (hcallee.call hmem).compile (scope := scope) (args := args)
  · intro scope calleeName args compiledIR argExprs hmem hcompile hargCompile
    exact (hcallee.call hmem).bridge
      (scope := scope)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile
  · intro scope names calleeName args hmem
    exact (hcallee.assign hmem).compile (scope := scope) (names := names) (args := args)
  · intro scope names calleeName args compiledIR argExprs hmem hcompile hargCompile
    exact (hcallee.assign hmem).bridge
      (scope := scope)
      (names := names)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile

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
  exact
    directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperPerCalleeBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hbody
        hassign)

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
  intro scope calleeName args hmem
  rcases hbridge.callCompile (scope := scope) (calleeName := calleeName)
      (args := args) hmem with ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCall_shape hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIR_internalCall
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (calleeName := calleeName)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile
      (hbridge.callBridge
        (scope := scope)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hmem
        hcompile
        hargCompile)

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
  intro scope names calleeName args hmem
  rcases hbridge.assignCompile (scope := scope) (names := names)
      (calleeName := calleeName) (args := args) hmem with ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCallAssign_shape hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIR_internalCallAssign
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (names := names)
      (calleeName := calleeName)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile
      (hbridge.assignBridge
        (scope := scope)
        (names := names)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hmem
        hcompile
        hargCompile)

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
  refine ⟨?_, ?_⟩
  · exact directInternalHelperHeadStepCatalog_call_of_bridgeCatalog hbridge
  · exact directInternalHelperHeadStepCatalog_assign_of_bridgeCatalog hbridge

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
  exact
    directInternalHelperHeadStepCatalog_of_bridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hcallee)

/-- Assemble the exact body-level direct-helper head-step catalog directly from
the split compile/semantic Tier 4 inventories. This removes the last per-callee
bridge detour once callers already provide the compile catalog and semantic
bridge data separately. -/
-- TYPESIG_SORRY: theorem directInternalHelperHeadStepCatalog_of_compileCatalog_and_semanticBridgeCatalog
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- TYPESIG_SORRY:     (hsemantic :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeSemanticBridgeCatalog runtimeContract spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       (directInternalHelperPerCalleeBridgeCatalog_of_compileCatalog_and_semanticBridgeCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hcompile
-- SORRY'D:         hsemantic)

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split compile/runtime-witness/semantic-core Tier 4 inventories. This keeps
-- SORRY'D: the theorem seam on the precise head-step catalog even before helper-summary
-- SORRY'D: facts are reintroduced. -/
-- TYPESIG_SORRY: theorem directInternalHelperHeadStepCatalog_of_compileCatalog_and_runtimeWitnessCatalog_and_semanticCoreCatalog
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- TYPESIG_SORRY:     (hruntime :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- TYPESIG_SORRY:     (hsemantic :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeSemanticCoreCatalog runtimeContract spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_compileCatalog_and_semanticBridgeCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hcompile
-- SORRY'D:       (directInternalHelperPerCalleeSemanticBridgeCatalog_of_runtimeWitnessCatalog_and_semanticCoreCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hruntime
-- SORRY'D:         hsemantic)

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split compile/runtime-witness/semantic-kernel Tier 4 inventories plus the
-- SORRY'D: current supported-body helper summaries. This is the direct landing point for
-- SORRY'D: future helper-rank induction once the semantic kernel is all that remains
-- SORRY'D: non-vacuous. -/
-- TYPESIG_SORRY: theorem directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_semanticKernelCatalog
-- TYPESIG_SORRY:     {runtimeContract : IRContract}
-- TYPESIG_SORRY:     {spec : CompilationModel}
-- TYPESIG_SORRY:     {fields : List Field}
-- TYPESIG_SORRY:     {fn : FunctionSpec}
-- TYPESIG_SORRY:     (hhelpers : SupportedBodyHelpersInterface spec fn)
-- TYPESIG_SORRY:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- TYPESIG_SORRY:     (hruntime :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeRuntimeWitnessCatalog runtimeContract spec fn)
-- TYPESIG_SORRY:     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
-- TYPESIG_SORRY:     (hkernel :
-- TYPESIG_SORRY:       DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn) :
-- TYPESIG_SORRY:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by sorry
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_compileCatalog_and_runtimeWitnessCatalog_and_semanticCoreCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hcompile
-- SORRY'D:       hruntime
-- SORRY'D:       (directInternalHelperPerCalleeSemanticCoreCatalog_of_supportedBodyHelpers_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hhelpers
-- SORRY'D:         hsummaries
-- SORRY'D:         hkernel)

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split compile/runtime-helper-table/semantic-kernel Tier 4 inventories plus
-- SORRY'D: the current supported-body helper summaries. This removes the remaining
-- SORRY'D: runtime-witness repackaging step once callers already provide the compiled
-- SORRY'D: runtime helper table. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hhelpers : SupportedBodyHelpersInterface spec fn)
-- SORRY'D:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
-- SORRY'D:     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
-- SORRY'D:     (hkernel :
-- SORRY'D:       DirectInternalHelperPerCalleeSemanticKernelCatalog runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeWitnessCatalog_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hhelpers
-- SORRY'D:       hcompile
-- SORRY'D:       (directInternalHelperPerCalleeRuntimeWitnessCatalog_of_runtimeHelperTable
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hruntime
-- SORRY'D:         hhelpers)
-- SORRY'D:       hsummaries
-- SORRY'D:       hkernel

-- SORRY'D: /-- Assemble the exact body-level direct-helper head-step catalog directly from
-- SORRY'D: the split compile/runtime-helper-table/call-kernel/assign-kernel Tier 4
-- SORRY'D: inventories plus the current supported-body helper summaries. This keeps the
-- SORRY'D: wrapper seam on the exact future rank-induction target even when call and
-- SORRY'D: assign semantic kernels are still supplied separately. -/
-- SORRY'D: theorem
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_callSemanticKernelCatalog_and_assignSemanticKernelCatalog
-- SORRY'D:     {runtimeContract : IRContract}
-- SORRY'D:     {spec : CompilationModel}
-- SORRY'D:     {fields : List Field}
-- SORRY'D:     {fn : FunctionSpec}
-- SORRY'D:     (hhelpers : SupportedBodyHelpersInterface spec fn)
-- SORRY'D:     (hcompile : DirectInternalHelperPerCalleeCompileCatalog spec fields fn)
-- SORRY'D:     (hruntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
-- SORRY'D:     (hsummaries : SupportedBodyHelperSummariesSound spec fn hhelpers)
-- SORRY'D:     (hcall :
-- SORRY'D:       DirectInternalHelperPerCalleeCallSemanticKernelCatalog runtimeContract spec fields fn)
-- SORRY'D:     (hassign :
-- SORRY'D:       DirectInternalHelperPerCalleeAssignSemanticKernelCatalog runtimeContract spec fields fn) :
-- SORRY'D:     DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
-- SORRY'D:   exact
-- SORRY'D:     directInternalHelperHeadStepCatalog_of_supportedBodyHelpers_and_compileCatalog_and_runtimeHelperTable_and_helperSummariesSound_and_semanticKernelCatalog
-- SORRY'D:       (runtimeContract := runtimeContract)
-- SORRY'D:       (spec := spec)
-- SORRY'D:       (fields := fields)
-- SORRY'D:       (fn := fn)
-- SORRY'D:       hhelpers
-- SORRY'D:       hcompile
-- SORRY'D:       hruntime
-- SORRY'D:       hsummaries
-- SORRY'D:       (directInternalHelperPerCalleeSemanticKernelCatalog_of_callCatalog_and_assignCatalog
-- SORRY'D:         (runtimeContract := runtimeContract)
-- SORRY'D:         (spec := spec)
-- SORRY'D:         (fields := fields)
-- SORRY'D:         (fn := fn)
-- SORRY'D:         hcall
-- SORRY'D:         hassign)

-- SORRY'D: /-- Assemble the reusable direct-helper head-step catalog directly from the
-- SORRY'D: current helper-free supported-body witness plus the assign-only per-callee
-- SORRY'D: bridge inventory. This removes one more derived Tier 4 seam while preserving the
-- SORRY'D: same eventual rank-induction target. -/
theorem directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
  exact
    directInternalHelperHeadStepCatalog_of_bridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hbody
        hassign)

private theorem eraseDups_nodup_and_mem_aux_local [BEq α] [LawfulBEq α]
    (n : Nat) (l : List α) (hlen : l.length ≤ n) :
    (l.eraseDups).Nodup ∧ (∀ a, a ∈ l.eraseDups ↔ a ∈ l) := by
  induction n generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst this
      exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | succ n ih =>
      match l with
      | [] => exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
      | x :: xs =>
          rw [List.eraseDups_cons]
          have hfilt_len : (xs.filter fun b => !b == x).length ≤ n := by
            have := List.length_filter_le (fun b => !b == x) xs
            simp [List.length_cons] at hlen
            omega
          have ⟨ihNd, ihMem⟩ := ih _ hfilt_len
          constructor
          · rw [List.nodup_cons]
            constructor
            · intro h
              have hmf := (ihMem x).mp h
              rw [List.mem_filter] at hmf
              have := hmf.2
              simp at this
            · exact ihNd
          · intro a
            constructor
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · exact Or.inr (List.mem_filter.mp ((ihMem a).mp h)).1
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · by_cases heq : a == x
                · exact Or.inl (beq_iff_eq.mp heq)
                · exact Or.inr ((ihMem a).mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

private theorem List.mem_eraseDups_iff_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} : a ∈ l.eraseDups ↔ a ∈ l :=
  (eraseDups_nodup_and_mem_aux_local l.length l (Nat.le_refl _)).2 a

private theorem List.mem_eraseDups_of_mem_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  List.mem_eraseDups_iff_local.mpr h

private theorem List.mem_of_mem_eraseDups_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l :=
  List.mem_eraseDups_iff_local.mp h

private theorem internalCallAssign_callee_mem_stmtListInternalHelperCallNames_eraseDups
    {names : List String} {calleeName : String} {args : List Expr} {rest : List Stmt} :
    calleeName ∈
      (stmtListInternalHelperCallNames
        (Stmt.internalCallAssign names calleeName args :: rest)).eraseDups := by
  apply List.mem_eraseDups_of_mem_local
  simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]

private theorem internalCall_callee_mem_stmtListInternalHelperCallNames_eraseDups
    {calleeName : String} {args : List Expr} {rest : List Stmt} :
    calleeName ∈
      (stmtListInternalHelperCallNames
        (Stmt.internalCall calleeName args :: rest)).eraseDups := by
  apply List.mem_eraseDups_of_mem_local
  simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]

private theorem mem_stmtListInternalHelperCallNames_cons_of_mem_tail
    {stmt : Stmt} {rest : List Stmt} {calleeName : String}
    (hrest : calleeName ∈ stmtListInternalHelperCallNames rest) :
    calleeName ∈ stmtListInternalHelperCallNames (stmt :: rest) := by
  simp [stmtListInternalHelperCallNames, hrest]

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCallAssign names calleeName args =>
          rcases hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect

-- SORRY'D: /-- Assemble the exact direct-helper-assign list interface from head-step
-- SORRY'D: constructors indexed only by helper callees that actually occur in the current
-- SORRY'D: statement list. This is the precise seam future helper-rank induction should
-- SORRY'D: target: it no longer needs to quantify over arbitrary helper names unrelated to
-- SORRY'D: the body under proof. -/
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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCallAssign names calleeName args =>
            rcases hstep
                (scope := scope)
                (names := names)
                (calleeName := calleeName)
                (args := args)
                internalCallAssign_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect
      · apply ih
        intro scope names calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

-- SORRY'D: /-- Non-vacuous list-level constructor for a direct helper statement head.
-- SORRY'D: This packages `compiledStmtStepWithHelpersAndHelperIR_internalCall` into the
-- SORRY'D: split direct-helper call interface expected by the exact helper-aware list
-- SORRY'D: induction seam. -/
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
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCall calleeName args =>
          rcases hstep (scope := scope) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect

-- SORRY'D: /-- Assemble the exact direct-helper-call list interface from head-step
-- SORRY'D: constructors indexed only by helper callees that actually occur in the current
-- SORRY'D: statement list. This matches the `helperCallNames`-based rank inventory carried
-- SORRY'D: by `SupportedBodyHelperInterface`, avoiding arbitrary-name quantification at the
-- SORRY'D: function theorem boundary. -/
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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCall calleeName args =>
            rcases hstep
                (scope := scope)
                (calleeName := calleeName)
                (args := args)
                internalCall_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect
      · apply ih
        intro scope calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

-- SORRY'D: /-- Assemble both exact direct-helper list interfaces from a single body-local
-- SORRY'D: head-step catalog. This keeps the list recursion mechanical so future
-- SORRY'D: rank-decreasing helper proofs can focus on constructing one catalog object. -/
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
  intro hcatalog
  constructor
  · exact
      stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := fn.body)
        hcatalog.call
  · exact
      stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := fn.body)
        hcatalog.assign

private theorem internalFunctionYulName_ne_stop
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "stop" := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix] at hHead
  cases hHead with
  | inl h =>
      have hcontra : (toString "").data.head? ≠ some 's' := by decide
      exact hcontra h
  | inr h =>
      have hcontra : (toString "internal_").data.head? ≠ some 's' := by decide
      exact hcontra h.2

private theorem internalFunctionYulName_ne_sstore
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "sstore" := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix] at hHead
  cases hHead with
  | inl h =>
      have hcontra : (toString "").data.head? ≠ some 's' := by decide
      exact hcontra h
  | inr h =>
      have hcontra : (toString "internal_").data.head? ≠ some 's' := by decide
      exact hcontra h.2

private theorem internalFunctionYulName_ne_mstore
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "mstore" := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix] at hHead
  cases hHead with
  | inl h =>
      have hcontra : (toString "").data.head? ≠ some 'm' := by decide
      exact hcontra h
  | inr h =>
      have hcontra : (toString "internal_").data.head? ≠ some 'm' := by decide
      exact hcontra h.2

private theorem internalFunctionYulName_ne_revert
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "revert" := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix] at hHead
  cases hHead with
  | inl h =>
      have hcontra : (toString "").data.head? ≠ some 'r' := by decide
      exact hcontra h
  | inr h =>
      have hcontra : (toString "internal_").data.head? ≠ some 'r' := by decide
      exact hcontra h.2

private theorem internalFunctionYulName_ne_return
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "return" := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix] at hHead
  cases hHead with
  | inl h =>
      have hcontra : (toString "").data.head? ≠ some 'r' := by decide
      exact hcontra h
  | inr h =>
      have hcontra : (toString "internal_").data.head? ≠ some 'r' := by decide
      exact hcontra h.2

-- SORRY'D: /-- Runtime-helper-table packaged version of
-- SORRY'D: `execIRStmtsWithInternals_of_internalCallAssign_compile`: the caller no longer
-- SORRY'D: threads a raw `findInternalFunction?` hypothesis by hand, only the compiled
-- SORRY'D: helper witness coming from `SupportedRuntimeHelperTableInterface`. -/
theorem execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {compiledIR : List YulStmt}
    (compiledHelper :
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState)
    (irFuel : Nat)
    {argVals : List Nat}
    {state' : IRState}
    (hcompile :
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile :
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    (hargs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state') :
    ∃ helper,
      compiledIR = [YulStmt.letMany names
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values values state'' =>
            if names.length = values.length then
              .continue (state''.setVars (names.zip values))
            else .revert state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  have hcalleeName : compiledHelper.sourceWitness.callee.name = calleeName :=
    compiledHelper.sourceWitness.nameEq
  have hfindSome :
      (findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName)).isSome = true :=
    by
      simpa [hcalleeName] using
        (findInternalFunction?_of_compileInternalFunction_mem
          compiledHelper.compileOk
          compiledHelper.presentInRuntime)
  cases hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) with
  | none =>
      simp [hfind] at hfindSome
  | some helper =>
      rcases
          execIRStmtsWithInternals_of_internalCallAssign_compile
            (fields := fields)
            (scope := scope)
            (names := names)
            (functionName := calleeName)
            (args := args)
            (compiledIR := compiledIR)
            runtimeContract
            irFuel
            state
            helper
            argVals
            state'
            hcompile
            hfind
            argExprs
            hargCompile
            hargs with
        ⟨hshape, hexec⟩
      refine ⟨helper, ?_⟩
      exact ⟨hshape, ⟨rfl, hexec⟩⟩

-- SORRY'D: /-- Runtime-helper-table packaged version of
-- SORRY'D: `execIRStmtsWithInternals_of_internalCall_compile`: the caller no longer threads
-- SORRY'D: raw helper lookup or builtin-name side conditions by hand. -/
theorem execIRStmtsWithInternals_of_internalCall_compiledHelperWitness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    {compiledIR : List YulStmt}
    (compiledHelper :
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState)
    (irFuel : Nat)
    {argVals : List Nat}
    {state' : IRState}
    (hcompile :
      CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (Stmt.internalCall calleeName args) = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile :
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    (hargs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state') :
    ∃ helper,
      compiledIR = [YulStmt.expr
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values _ state'' => .continue state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  have hcalleeName : compiledHelper.sourceWitness.callee.name = calleeName :=
    compiledHelper.sourceWitness.nameEq
  have hfindSome :
      (findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName)).isSome = true :=
    by
      simpa [hcalleeName] using
        (findInternalFunction?_of_compileInternalFunction_mem
          compiledHelper.compileOk
          compiledHelper.presentInRuntime)
  cases hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) with
  | none =>
      simp [hfind] at hfindSome
  | some helper =>
      rcases
          execIRStmtsWithInternals_of_internalCall_compile
            (fields := fields)
            (scope := scope)
            (functionName := calleeName)
            (args := args)
            (compiledIR := compiledIR)
            runtimeContract
            irFuel
            state
            helper
            argVals
            state'
            hcompile
            hfind
            argExprs
            hargCompile
            hargs
            (internalFunctionYulName_ne_stop calleeName)
            (internalFunctionYulName_ne_sstore calleeName)
            (internalFunctionYulName_ne_mstore calleeName)
            (internalFunctionYulName_ne_revert calleeName)
            (internalFunctionYulName_ne_return calleeName) with
        ⟨hshape, hexec⟩
      refine ⟨helper, ?_⟩
      exact ⟨hshape, ⟨rfl, hexec⟩⟩

-- SORRY'D: end Compiler.Proofs.IRGeneration
