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

/-- Source names visible to generic statement proofs must stay out of the
compiler scratch namespace used by compatibility temporaries. Internal
immutable storage fields may legally use other `__*` names. -/
def scopeAvoidsReservedCompilerPrefix (scope : List String) : Prop :=
  "__compat_value" ∉ scope ∧
  "__compat_packed" ∉ scope ∧
  "__compat_slot_word" ∉ scope ∧
  "__compat_slot_cleared" ∉ scope

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

private theorem field_mem_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    f ∈ fields :=
  field_mem_of_findFieldWithResolvedSlot_eq_some hfind

private theorem legacyCompatibleExternalStmtList_of_unpackedStorageWrite
    (slot : Nat)
    (aliasSlots : List Nat)
    (valueExpr : YulExpr) :
    True := by
  trivial

-- TODO: prove by case analysis on compileSetStorage output
-- The proof needs to handle: rcases on compileExpr (error propagates as Except.error,
-- contradiction with Except.ok), then split on slot :: aliasSlots pattern, rewrite
-- packedBits = none, and construct LegacyCompatibleExternalStmtList for the resulting IR.
-- Key difficulty: the block case produces non-trivial statement lists.
private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    {f : Field}
    {slot : Nat}
    {requireAddressField : Bool}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot))
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value requireAddressField =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  have hmem := field_mem_of_findFieldWithResolvedSlot_some hfind
  have hunpacked := hnoPacked f hmem
  unfold CompilationModel.compileSetStorage at hcompile
  simp only [hfind] at hcompile
  by_cases hmap : isMapping fields fieldName
  · simp [hmap] at hcompile
  · simp only [hmap, ite_false] at hcompile
    cases requireAddressField with
    | false =>
        simp only [ite_false, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        rcases hve : CompilationModel.compileExpr fields .calldata value with err | valueExpr
        · simp [hve, Bind.bind, Except.bind] at hcompile
        · simp only [hve, Except.ok.injEq] at hcompile
          cases hslots : f.aliasSlots with
          | nil =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              exact .expr _ [] .nil
          | cons s rest =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              refine .block _ [] (.let_ _ _ _ ?_) .nil
              simp only [← List.map_cons, ← List.map_map, ← Function.comp_def]
              exact legacyCompatibleExternalStmtList_of_exprStmtExprs _
    | true =>
        simp only [ite_true, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        cases hty : f.ty <;> simp [hty, Bind.bind, Except.bind, pure, Except.pure] at hcompile
        rcases hve : CompilationModel.compileExpr fields .calldata value with err | valueExpr
        · simp [hve, Bind.bind, Except.bind] at hcompile
        · simp only [hve, Except.ok.injEq] at hcompile
          cases hslots : f.aliasSlots with
          | nil =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              exact .expr _ [] .nil
          | cons s rest =>
              simp [hslots, hunpacked] at hcompile; subst hcompile
              refine .block _ [] (.let_ _ _ _ ?_) .nil
              simp only [← List.map_cons, ← List.map_map, ← Function.comp_def]
              exact legacyCompatibleExternalStmtList_of_exprStmtExprs _

private theorem legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
    {fields : List Field}
    {fieldName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    {requireAddressField : Bool}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hcompile :
      CompilationModel.compileSetStorage fields .calldata fieldName value requireAddressField =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStorage at hcompile
  by_cases hmap : isMapping fields fieldName
  · simp [hmap] at hcompile
  · simp only [hmap, ite_false] at hcompile
    rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
    · simp [hfind] at hcompile
    · simp only [hfind] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_resolved
        hnoPacked hfind (by rwa [CompilationModel.compileSetStorage, if_neg hmap, hfind])

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
  exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
    hnoPacked hcompile

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

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_mstore
    {fields : List Field}
    {inScopeNames : List String}
    {offset value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.mstore offset value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hoffset : CompilationModel.compileExpr fields .calldata offset with _ | offsetIR
  · simp [hoffset] at hcompile
    cases hcompile
  · rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
      exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "mstore" [offsetIR, valueIR])
        []
        LegacyCompatibleExternalStmtList.nil

private theorem legacyCompatibleExternalStmtList_of_compileStmt_ok_tstore
    {fields : List Field}
    {inScopeNames : List String}
    {offset value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt
        fields [] [] .calldata [] false inScopeNames (.tstore offset value) =
          Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileStmt at hcompile
  rcases hoffset : CompilationModel.compileExpr fields .calldata offset with _ | offsetIR
  · simp [hoffset] at hcompile
    cases hcompile
  · rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueIR
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
    · simp [hoffset, hvalue] at hcompile
      cases hcompile
      exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "tstore" [offsetIR, valueIR])
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
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt with
  | letVar name value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar hcompile
  | assignVar name value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar hcompile
  | setStorage fieldName value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields hnoPacked hcompile
  | setStorageAddr fieldName value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields_aux
        (requireAddressField := true)
        hnoPacked
        hcompile
  | require cond message =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_require hcompile
  | «return» value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_return hcompile
  | stop =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_stop hcompile
  | mstore offset value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_mstore hcompile
  | tstore offset value =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_tstore hcompile
  | _ =>
      simp [stmtTouchesUnsupportedContractSurface] at hsurface

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

private theorem legacyCompatibleExternalStmtList_of_mappingWriteCompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (keyExpr valueExpr : YulExpr)
    (wordOffset : Nat) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([("__compat_key", keyExpr), ("__compat_value", valueExpr)].map
            (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            YulStmt.expr
              (YulExpr.call "sstore"
                [let mappingBase :=
                    YulExpr.call "mappingSlot"
                      [YulExpr.lit writeSlot, YulExpr.ident "__compat_key"]
                 if wordOffset == 0 then mappingBase
                 else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
                 YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      YulExpr.call "sstore"
        [let mappingBase :=
            YulExpr.call "mappingSlot"
              [YulExpr.lit writeSlot, YulExpr.ident "__compat_key"]
         if wordOffset == 0 then mappingBase
         else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset],
         YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key", keyExpr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

private theorem legacyCompatibleExternalStmtList_of_mapping2CompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (key1Expr key2Expr valueExpr : YulExpr) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([ ("__compat_key1", key1Expr)
         , ("__compat_key2", key2Expr)
         , ("__compat_value", valueExpr)
         ].map (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            let innerSlot :=
              YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
            YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
               YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      let innerSlot :=
        YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
      YulExpr.call "sstore"
        [YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"],
         YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key1", key1Expr), ("__compat_key2", key2Expr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

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
  unfold CompilationModel.compileMappingSlotWrite at hcompile
  by_cases hmapping : isMapping fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots] at hcompile
        cases slots with
        | nil =>
            simp at hcompile
        | cons slot rest =>
            cases rest with
            | nil =>
                injection hcompile with hbody
                subst hbody
                exact LegacyCompatibleExternalStmtList.expr _ [] .nil
            | cons slot' rest' =>
                injection hcompile with hbody
                subst hbody
                simpa using
                  legacyCompatibleExternalStmtList_of_mappingWriteCompatBlock
                    slot slot' rest' keyExpr valueExpr wordOffset
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_mapping2WordCompatBlock
    (slot slot' : Nat)
    (rest' : List Nat)
    (key1Expr key2Expr valueExpr : YulExpr)
    (wordOffset : Nat) :
    LegacyCompatibleExternalStmtList
      [YulStmt.block (
        ([ ("__compat_key1", key1Expr)
         , ("__compat_key2", key2Expr)
         , ("__compat_value", valueExpr)
         ].map (fun binding => YulStmt.let_ binding.1 binding.2)) ++
          (slot :: slot' :: rest').map (fun writeSlot =>
            let innerSlot :=
              YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
            let outerSlot :=
              YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
            let finalSlot :=
              if wordOffset == 0 then outerSlot
              else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
            YulStmt.expr (YulExpr.call "sstore"
              [finalSlot, YulExpr.ident "__compat_value"])))] := by
  let compatExprs :=
    (slot :: slot' :: rest').map (fun writeSlot =>
      let innerSlot :=
        YulExpr.call "mappingSlot" [YulExpr.lit writeSlot, YulExpr.ident "__compat_key1"]
      let outerSlot :=
        YulExpr.call "mappingSlot" [innerSlot, YulExpr.ident "__compat_key2"]
      let finalSlot :=
        if wordOffset == 0 then outerSlot
        else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
      YulExpr.call "sstore"
        [finalSlot, YulExpr.ident "__compat_value"])
  have hcompatExprs :
      LegacyCompatibleExternalStmtList (compatExprs.map YulStmt.expr) :=
    legacyCompatibleExternalStmtList_of_exprStmtExprs compatExprs
  refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
  simpa [compatExprs] using
    (legacyCompatibleExternalStmtList_of_letBindings
      [("__compat_key1", key1Expr), ("__compat_key2", key2Expr), ("__compat_value", valueExpr)]
      (compatExprs.map YulStmt.expr)
      hcompatExprs)

private theorem legacyCompatibleExternalStmtList_of_compileSetMapping2Word_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 : Expr}
    {wordOffset : Nat}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMapping2Word fields dynamicSource field key1 key2 wordOffset value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetMapping2Word at hcompile
  by_cases hmapping : isMapping2 fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots, bind, Except.bind] at hcompile
        rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
        · simp [hkey1] at hcompile
        · simp [hkey1] at hcompile
          rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
          · simp [hkey2] at hcompile
          · simp [hkey2] at hcompile
            rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
            · simp [hvalue] at hcompile
            · simp [hvalue] at hcompile
              cases slots with
              | nil =>
                  simp at hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      injection hcompile with hbody
                      subst hbody
                      exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                  | cons slot' rest' =>
                      injection hcompile with hbody
                      subst hbody
                      simpa using
                        legacyCompatibleExternalStmtList_of_mapping2WordCompatBlock
                          slot slot' rest' key1Expr key2Expr valueExpr wordOffset
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_mapLetStmts
    {α : Type} (xs : List α) (f : α → String) (g : α → YulExpr) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.let_ (f x) (g x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .let_ (f x) (g x) _ ih

private theorem legacyCompatibleExternalStmtList_of_mapExprStmts
    {α : Type} (xs : List α) (f : α → YulExpr) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.expr (f x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .expr (f x) _ ih

private theorem legacyCompatibleExternalStmtList_of_mapBlockStmts
    {α : Type} (xs : List α) (f : α → List YulStmt)
    (hf : ∀ x, LegacyCompatibleExternalStmtList (f x)) :
    LegacyCompatibleExternalStmtList (xs.map (fun x => YulStmt.block (f x))) := by
  induction xs with
  | nil => exact .nil
  | cons x rest ih => exact .block _ _ (hf x) ih

private theorem legacyCompatibleExternalStmtList_of_compileSetMappingChain_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {keys : List Expr}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetMappingChain fields dynamicSource field keys value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetMappingChain at hcompile
  by_cases hmapping : isMapping fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots, bind, Except.bind] at hcompile
        rcases hkeys : CompilationModel.compileExprList fields dynamicSource keys with _ | keyExprs
        · simp [hkeys] at hcompile
        · simp [hkeys] at hcompile
          rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
          · simp [hvalue] at hcompile
          · simp [hvalue] at hcompile
            cases slots with
            | nil =>
                simp at hcompile
            | cons slot rest =>
                cases rest with
                | nil =>
                    injection hcompile with hbody
                    subst hbody
                    exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                | cons slot' rest' =>
                    injection hcompile with hbody
                    subst hbody
                    refine LegacyCompatibleExternalStmtList.block _ [] ?_ .nil
                    apply LegacyCompatibleExternalStmtList.let_ "__compat_value" valueExpr
                    apply legacyCompatibleExternalStmtList_append
                    · exact legacyCompatibleExternalStmtList_of_mapLetStmts
                        keyExprs.zipIdx
                        (fun p => s!"__compat_key{p.2}")
                        (fun p => p.1)
                    · exact legacyCompatibleExternalStmtList_of_mapExprStmts _ _
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok
    {fields : List Field}
    {field : String}
    {keyExpr valueExpr : YulExpr}
    {wordOffset : Nat}
    {packed : PackedBits}
    {label : String}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileMappingPackedSlotWrite fields field keyExpr valueExpr wordOffset packed label =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileMappingPackedSlotWrite at hcompile
  by_cases hmapping : isMapping fields field
  · by_cases hvalid : packedBitsValid packed
    · simp [hmapping, hvalid] at hcompile
      cases hslots : findFieldWriteSlots fields field with
      | none =>
          simp [hslots] at hcompile
      | some slots =>
          simp [hslots] at hcompile
          cases slots with
          | nil =>
              simp at hcompile
          | cons slot rest =>
              cases rest with
              | nil =>
                  injection hcompile with hbody
                  subst hbody
                  exact .block _ []
                    (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))))) .nil
              | cons slot' rest' =>
                  injection hcompile with hbody
                  subst hbody
                  refine .block _ [] ?_ .nil
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                  induction (slot :: slot' :: rest') with
                  | nil => exact .nil
                  | cons s rs ih =>
                      exact .block _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))) ih
    · simp [hmapping, hvalid] at hcompile
  · simp [hmapping] at hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetStructMember_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key : Expr}
    {memberName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStructMember fields dynamicSource field key memberName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStructMember at hcompile
  simp only [bind, Except.bind, pure, Except.pure] at hcompile
  by_cases hm2 : isMapping2 fields field
  · simp [hm2] at hcompile
  · simp [hm2] at hcompile
    cases hstruct : findStructMembers fields field with
    | none => simp [hstruct] at hcompile
    | some members =>
        simp [hstruct] at hcompile
        cases hmem : findStructMember members memberName with
        | none => simp [hmem] at hcompile
        | some member =>
            simp [hmem] at hcompile
            cases hpacked : member.packed with
            | none =>
                simp [hpacked, bind, Except.bind] at hcompile
                rcases hkey : CompilationModel.compileExpr fields dynamicSource key with _ | keyExpr
                · simp [hkey] at hcompile
                · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                  · simp [hkey, hvalue] at hcompile
                  · simp [hkey, hvalue] at hcompile
                    exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
            | some packed =>
                simp [hpacked, bind, Except.bind] at hcompile
                rcases hkey : CompilationModel.compileExpr fields dynamicSource key with _ | keyExpr
                · simp [hkey] at hcompile
                · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                  · simp [hkey, hvalue] at hcompile
                  · simp [hkey, hvalue] at hcompile
                    exact legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok hcompile

private theorem legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {field : String}
    {key1 key2 : Expr}
    {memberName : String}
    {value : Expr}
    {bodyIR : List YulStmt}
    (hcompile :
      CompilationModel.compileSetStructMember2 fields dynamicSource field key1 key2 memberName value =
        Except.ok bodyIR) :
    LegacyCompatibleExternalStmtList bodyIR := by
  unfold CompilationModel.compileSetStructMember2 at hcompile
  simp only [bind, Except.bind, pure, Except.pure] at hcompile
  by_cases hm2 : isMapping2 fields field
  · simp [hm2] at hcompile
    cases hstruct : findStructMembers fields field with
    | none => simp [hstruct] at hcompile
    | some members =>
        simp [hstruct] at hcompile
        cases hmem : findStructMember members memberName with
        | none => simp [hmem] at hcompile
        | some member =>
            simp [hmem] at hcompile
            cases hslots : findFieldWriteSlots fields field with
            | none => simp [hslots] at hcompile
            | some slots =>
                simp [hslots, bind, Except.bind] at hcompile
                rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
                · simp [hkey1] at hcompile
                · simp [hkey1] at hcompile
                  rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
                  · simp [hkey2] at hcompile
                  · simp [hkey2] at hcompile
                    rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
                    · simp [hvalue] at hcompile
                    · simp [hvalue] at hcompile
                      cases hpacked : member.packed with
                      | none =>
                          simp [hpacked] at hcompile
                          cases slots with
                          | nil => simp at hcompile
                          | cons slot rest =>
                              cases rest with
                              | nil =>
                                  -- Single slot, unpacked: [expr (sstore [...])]
                                  simp [pure, Except.pure] at hcompile
                                  subst hcompile
                                  exact .expr _ [] .nil
                              | cons slot' rest' =>
                                  -- Multi slot, unpacked: [block (lets ++ expr_stmts)]
                                  injection hcompile with hbody
                                  subst hbody
                                  apply LegacyCompatibleExternalStmtList.block _ []
                                  · apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                    exact legacyCompatibleExternalStmtList_of_mapExprStmts _ _
                                  · exact .nil
                      | some packed =>
                          simp [hpacked] at hcompile
                          cases slots with
                          | nil => simp at hcompile
                          | cons slot rest =>
                              cases rest with
                              | nil =>
                                  -- Single slot, packed: [block [let_, let_, let_, let_, expr]]
                                  simp [pure, Except.pure] at hcompile
                                  subst hcompile
                                  exact .block _ []
                                    (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil))))) .nil
                              | cons slot' rest' =>
                                  -- Multi slot, packed
                                  simp only [pure, Except.pure] at hcompile
                                  injection hcompile with hbody
                                  subst hbody
                                  unfold CompilationModel.compileCompatPackedStorageWrites
                                  simp only [List.append_eq, List.cons_append, List.nil_append]
                                  refine .block _ [] ?_ .nil
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  refine .block _ _ ?_ .nil
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  apply LegacyCompatibleExternalStmtList.let_ _ _ _
                                  simp only [List.map_map]
                                  exact legacyCompatibleExternalStmtList_of_mapBlockStmts _ _
                                    (fun _ => .let_ _ _ _ (.let_ _ _ _ (.expr _ [] .nil)))
  · simp [hm2] at hcompile

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
  unfold CompilationModel.compileSetMapping2 at hcompile
  by_cases hmapping : isMapping2 fields field
  · simp [hmapping] at hcompile
    cases hslots : findFieldWriteSlots fields field with
    | none =>
        simp [hslots] at hcompile
    | some slots =>
        simp [hslots] at hcompile
        rcases hkey1 : CompilationModel.compileExpr fields dynamicSource key1 with _ | key1Expr
        · simp [hkey1] at hcompile
          cases hcompile
        · rcases hkey2 : CompilationModel.compileExpr fields dynamicSource key2 with _ | key2Expr
          · simp [hkey1, hkey2] at hcompile
            cases hcompile
          · rcases hvalue : CompilationModel.compileExpr fields dynamicSource value with _ | valueExpr
            · simp [hkey1, hkey2, hvalue] at hcompile
              cases hcompile
            · simp [hkey1, hkey2, hvalue] at hcompile
              cases slots with
              | nil =>
                simp at hcompile
                cases hcompile
              | cons slot rest =>
                  cases rest with
                  | nil =>
                      injection hcompile with hbody
                      subst hbody
                      exact LegacyCompatibleExternalStmtList.expr _ [] .nil
                  | cons slot' rest' =>
                      injection hcompile with hbody
                      subst hbody
                      simpa using
                        legacyCompatibleExternalStmtList_of_mapping2CompatBlock
                          slot slot' rest' key1Expr key2Expr valueExpr
  · simp [hmapping] at hcompile

private theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv
    {stmt : Stmt}
    {rest : List Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites (stmt :: rest) = false) :
    stmtTouchesUnsupportedContractSurfaceExceptMappingWrites stmt = false ∧
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites rest = false := by
  simpa [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites] using
    (Bool.or_eq_false_iff.mp hsurface)

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
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt with
  | setMapping field key value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMappingUint field key value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMapping2 field key1 key2 value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMapping2_ok hcompile
  | setMappingWord field key wordOffset value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingSlotWrite_ok hcompile
  | setMapping2Word field key1 key2 wordOffset value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMapping2Word_ok hcompile
  | setMappingPackedWord field key wordOffset packed value =>
      unfold CompilationModel.compileStmt at hcompile
      simp only [bind, Except.bind] at hcompile
      rcases hkey : CompilationModel.compileExpr fields .calldata key with _ | keyExpr <;>
        simp [hkey] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr <;>
        simp [hvalue] at hcompile
      exact legacyCompatibleExternalStmtList_of_compileMappingPackedSlotWrite_ok hcompile
  | setMappingChain field keys value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetMappingChain_ok hcompile
  | setStructMember field key memberName value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStructMember_ok hcompile
  | setStructMember2 field key1 key2 memberName value =>
      unfold CompilationModel.compileStmt at hcompile
      exact legacyCompatibleExternalStmtList_of_compileSetStructMember2_ok hcompile
  | letVar _ _ | assignVar _ _ | setStorage _ _ | setStorageAddr _ _
  | storageArrayPush _ _ | storageArrayPop _ | setStorageArrayElement _ _ _
  | require _ | requireError _ _ | revertError _ _
  | «return» _ | returnValues _ | returnArray _ | returnBytes _
  | returnStorageWords _ | mstore _ _ | tstore _ _ | calldatacopy _ _ _
  | returndataCopy _ _ _ | revertReturndata | stop
  | ite _ _ _ | forEach _ _ _ | emit _ _
  | internalCall _ _ | internalCallAssign _ _ _ | rawLog _ _ _
  | externalCallBind _ _ _ | ecm _ _ =>
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked
        (by simpa [stmtTouchesUnsupportedContractSurfaceExceptMappingWrites] using hsurface)
        hcompile

-- SORRY'D: /-- Tier 2 list-level legacy-compatibility witness for the alternate singleton
-- SORRY'D: mapping-write surface. -/
theorem stmtListCompiledLegacyCompatible_of_supportedContractSurface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites stmts = false) :
    StmtListCompiledLegacyCompatible fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv hsurface
      have hstmtSurface := hsplit.1
      have hrestSurface := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro compiledIR hcompile
      exact
        legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
          hnoPacked hstmtSurface hcompile
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
    StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_cons_inv hsurface
      have hstmtSurface := hsplit.1
      have hrestSurface := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro _ compiledIR hcompile
      exact
        YulStmtListCallsDisjointFromInternalTable_of_internalFunctions_nil
          runtimeContract
          hinternal
          compiledIR
          (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface_exceptMappingWrites
            hnoPacked
            hstmtSurface
            hcompile)
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
  induction hsteps with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hlegacy with
          | cons hheadLegacy htailLegacy =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · obtain ⟨compiledIR, hcore⟩ := hheadFree hsurface
                exact .cons
                  (CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible
                    (hcore.withHelpers_of_helperSurfaceClosed hsurface)
                    (hheadLegacy hsurface compiledIR hcore.compileOk)
                    hinternal)
                  (ih htailFree htailLegacy)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                exact .cons hcompiled (ih htailFree htailLegacy)

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
  induction hsteps with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hdisjoint with
          | cons hheadDisjoint htailDisjoint =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · obtain ⟨compiledIR, hcore⟩ := hheadFree hsurface
                exact .cons
                  (CompiledStmtStepWithHelpers.withHelperIR_of_callsDisjoint
                    (hcore.withHelpers_of_helperSurfaceClosed hsurface)
                    (hheadDisjoint hsurface compiledIR hcore.compileOk))
                  (ih htailFree htailDisjoint)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                exact .cons hcompiled (ih htailFree htailDisjoint)

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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hhelperFree with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadFree htailFree ih =>
      cases hinternal with
      | cons hheadInternal htailInternal =>
          cases hresidual with
          | cons hheadResidual htailResidual =>
              cases hlegacy with
              | cons hheadLegacy htailLegacy =>
                  by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
                  · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
                    exact .cons
                      ((hcore.withHelpers_of_helperSurfaceClosed hsurface).withHelperIR_of_legacyCompatible
                        (hheadLegacy hsurface compiledIR hcore.compileOk)
                        hnoInternalFunctions)
                      (ih htailInternal htailResidual htailLegacy)
                  · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                      cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                        simp [hstmt] at hsurface ⊢
                    -- Combine the internal and residual interfaces for this head
                    have hheadStep : stmtTouchesUnsupportedHelperSurface stmt = true →
                        ∃ compiledIR,
                          CompiledStmtStepWithHelpersAndHelperIR
                            runtimeContract spec fields scope stmt compiledIR := by
                      intro _
                      by_cases hactual : stmtTouchesInternalHelperSurface stmt = true
                      · exact hheadInternal hactual
                      · have hactualFalse : stmtTouchesInternalHelperSurface stmt = false := by
                          cases hactual' : stmtTouchesInternalHelperSurface stmt <;>
                            simp [hactual'] at hactual ⊢
                        exact hheadResidual hsurfaceTrue hactualFalse
                    rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                    exact .cons hcompiled (ih htailInternal htailResidual htailLegacy)

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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hinternal :=
        stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
            hcall hassign)
          hexpr
          hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hgeneric with
  | nil => exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hsteps with
      | cons hheadStep htailSteps =>
          cases hlegacy with
          | cons hheadLegacy htailLegacy =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · exact .cons
                  ((hstep.withHelpers_of_helperSurfaceClosed hsurface).withHelperIR_of_legacyCompatible
                    (hheadLegacy hsurface compiledIR hstep.compileOk) hinternal)
                  (ih htailSteps htailLegacy)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                    simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR', hcompiled⟩
                exact .cons hcompiled (ih htailSteps htailLegacy)

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
  induction hgeneric with
  | nil => exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hsteps with
      | cons hheadStep htailSteps =>
          cases hdisjoint with
          | cons hheadDisjoint htailDisjoint =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · exact .cons
                  ((hstep.withHelpers_of_helperSurfaceClosed hsurface).withHelperIR_of_callsDisjoint
                    (hheadDisjoint hsurface compiledIR hstep.compileOk))
                  (ih htailSteps htailDisjoint)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                    simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR', hcompiled⟩
                exact .cons hcompiled (ih htailSteps htailDisjoint)

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
    FunctionBody.ExprCompileCore expr := by
  match expr, hsurface with
  | .literal _, _ => exact .literal _
  | .param _, _ => exact .param _
  | .localVar _, _ => exact .localVar _
  | .caller, _ => exact .caller
  | .contractAddress, _ => exact .contractAddress
  | .msgValue, _ => exact .msgValue
  | .blockTimestamp, _ => exact .blockTimestamp
  | .blockNumber, _ => exact .blockNumber
  | .chainid, _ => exact .chainid
  | .add a b, hsurface | .sub a b, hsurface | .mul a b, hsurface
  | .div a b, hsurface | .mod a b, hsurface
  | .bitAnd a b, hsurface | .bitOr a b, hsurface | .bitXor a b, hsurface
  | .eq a b, hsurface | .ge a b, hsurface | .gt a b, hsurface
  | .lt a b, hsurface | .le a b, hsurface
  | .logicalAnd a b, hsurface | .logicalOr a b, hsurface
  | .shl a b, hsurface | .shr a b, hsurface
  | .min a b, hsurface | .max a b, hsurface
  | .ceilDiv a b, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      constructor
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1
      · exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2
  | .logicalNot a, hsurface | .bitNot a, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface] at hsurface
      constructor
      exact exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface
  | .ite cond thenVal elseVal, hsurface =>
      simp only [exprTouchesUnsupportedContractSurface, Bool.or_eq_false_iff] at hsurface
      exact .ite
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.1)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.1.2)
        (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hsurface.2)

private theorem fieldName_mem_fields_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    fieldName ∈ fields.map (·.name) := by
  have hmem := field_mem_of_findFieldWithResolvedSlot_eq_some hfind
  have hname := fieldName_eq_of_findFieldWithResolvedSlot_eq_some hfind
  rw [List.mem_map]
  exact ⟨f, hmem, hname⟩

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
  simp only [CompilationModel.compileSetStorage] at hcompile
  split at hcompile
  · simp at hcompile
  · rename_i hnotMapping
    split at hcompile
    · rename_i f slot hfind
      exact fieldName_mem_fields_of_findFieldWithResolvedSlot_some hfind
    · simp at hcompile

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
  rcases hcond : CompilationModel.compileExpr fields .calldata cond with _ | condIR
  · simp [hcond] at hcompile
    cases hcompile
  · simp [hcond] at hcompile
    rcases hthen : CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope thenBranch with _ | thenIR
    · simp [hthen] at hcompile
      cases hcompile
    · simp [hthen] at hcompile
      rcases helse : CompilationModel.compileStmtList
          fields [] [] .calldata [] false scope elseBranch with _ | elseIR
      · simp [helse] at hcompile
        cases hcompile
      ·
        simpa [hcond, hthen, helse] using
          (show ∃ condIR thenIR elseIR,
              Except.ok condIR = Except.ok condIR ∧
              Except.ok thenIR = Except.ok thenIR ∧
              Except.ok elseIR = Except.ok elseIR from
            ⟨condIR, thenIR, elseIR, rfl, rfl, rfl⟩)

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

private theorem stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
    {«prefix» «suffix» : List Stmt}
    {stmt : Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface («prefix» ++ stmt :: «suffix») = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  induction «prefix» with
  | nil =>
      simpa [stmtListTouchesUnsupportedContractSurface] using
        (Bool.or_eq_false_iff.mp hsurface).1
  | cons head rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface] at hsurface
      exact ih hsurface.2

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

private theorem validateScopedExprIdentifiers_pair_ok_left
    {context : String}
    {params : List Param}
    {paramScope dynamicParams localScope : List String}
    {constructorArgCount : Option Nat}
    {lhs rhs : Expr}
    (hvalidate :
      (do
        validateScopedExprIdentifiers
          context params paramScope dynamicParams localScope constructorArgCount lhs
        validateScopedExprIdentifiers
          context params paramScope dynamicParams localScope constructorArgCount rhs) =
        Except.ok ()) :
    validateScopedExprIdentifiers
      context params paramScope dynamicParams localScope constructorArgCount lhs =
        Except.ok () := by
  cases hlhs :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams localScope constructorArgCount lhs with
  | error err =>
      simp [hlhs] at hvalidate
      cases hvalidate
  | ok val =>
      cases val
      simpa using hlhs

private theorem validateScopedExprIdentifiers_pair_ok_right
    {context : String}
    {params : List Param}
    {paramScope dynamicParams localScope : List String}
    {constructorArgCount : Option Nat}
    {lhs rhs : Expr}
    (hvalidate :
      (do
        validateScopedExprIdentifiers
          context params paramScope dynamicParams localScope constructorArgCount lhs
        validateScopedExprIdentifiers
          context params paramScope dynamicParams localScope constructorArgCount rhs) =
        Except.ok ()) :
    validateScopedExprIdentifiers
      context params paramScope dynamicParams localScope constructorArgCount rhs =
        Except.ok () := by
  cases hlhs :
      validateScopedExprIdentifiers
        context params paramScope dynamicParams localScope constructorArgCount lhs with
  | error err =>
      simp [hlhs] at hvalidate
      cases hvalidate
  | ok val =>
      cases val
      simpa [hlhs] using hvalidate

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
  induction hcore with
  | literal =>
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
  | param name0 =>
      intro name hmem
      have hparam : name0 ∈ paramScope := by
        by_cases hname : name0 ∈ paramScope
        · exact hname
        · simp [validateScopedExprIdentifiers, hname] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hparamsInScope name0 hparam
  | localVar name0 =>
      intro name hmem
      have hlocal : name0 ∈ localScope := by
        by_cases hname : name0 ∈ localScope
        · exact hname
        · simp [validateScopedExprIdentifiers, hname] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hlocalsInScope name0 hlocal
  | caller | contractAddress | msgValue | blockTimestamp | blockNumber | chainid =>
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
  | add hL hR ihL ihR
  | sub hL hR ihL ihR
  | mul hL hR ihL ihR
  | div hL hR ihL ihR
  | mod hL hR ihL ihR
  | eq hL hR ihL ihR
  | lt hL hR ihL ihR
  | gt hL hR ihL ihR
  | ge hL hR ihL ihR
  | le hL hR ihL ihR
  | bitAnd hL hR ihL ihR
  | bitOr hL hR ihL ihR
  | bitXor hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount rhs) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | logicalNot h ih
  | bitNot h ih =>
      intro name hmem
      simpa [FunctionBody.exprBoundNames] using
        ih
          (by simpa [validateScopedExprIdentifiers] using hvalidate)
          name
          (by simpa [FunctionBody.exprBoundNames] using hmem)
  | shl hS hV ihS ihV
  | shr hS hV ihS ihV =>
      rename_i shift value
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount shift
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount value) =
            Except.ok () := by
        simpa [validateScopedExprIdentifiers] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihS (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihV (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | min hL hR ihL ihR
  | max hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount rhs) =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases validateArithDuplicatedOperandPurity context _ with
        | ok _ => simp [Bind.bind, Except.bind]
        | error e => simp [Bind.bind, Except.bind]
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | ceilDiv hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount rhs) =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases validateArithDuplicatedOperandPurity context _ with
        | ok _ => simp [Bind.bind, Except.bind]
        | error e => simp [Bind.bind, Except.bind]
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
  | ite hC hT hE ihC ihT ihE =>
      rename_i cond thenVal elseVal
      have hC_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams localScope constructorArgCount cond =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v => rfl
      have hT_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams localScope constructorArgCount thenVal =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v =>
            cases ht :
                validateScopedExprIdentifiers
                  context params paramScope dynamicParams localScope constructorArgCount thenVal with
            | error e => simp [hc, ht] at h
            | ok v => rfl
      have hE_ok :
          validateScopedExprIdentifiers
            context params paramScope dynamicParams localScope constructorArgCount elseVal =
            Except.ok () := by
        simp only [validateScopedExprIdentifiers] at hvalidate
        revert hvalidate
        cases exprContainsCallLike cond || exprContainsCallLike thenVal ||
          exprContainsCallLike elseVal with
        | true => simp [Bind.bind, Except.bind]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Pure.pure, Except.pure,
            Bind.bind, Except.bind]
          intro h
          cases hc :
              validateScopedExprIdentifiers
                context params paramScope dynamicParams localScope constructorArgCount cond with
          | error e => simp [hc] at h
          | ok v =>
            cases ht :
                validateScopedExprIdentifiers
                  context params paramScope dynamicParams localScope constructorArgCount thenVal with
            | error e => simp [hc, ht] at h
            | ok v => simpa [hc, ht] using h
      intro name hmem
      simp only [FunctionBody.exprBoundNames] at hmem
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with hmem | hmem
        · exact ihC hC_ok name hmem
        · exact ihT hT_ok name hmem
      · exact ihE hE_ok name hmem
  | logicalAnd hL hR ihL ihR
  | logicalOr hL hR ihL ihR =>
      rename_i lhs rhs
      have hpair :
          (do
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount lhs
            validateScopedExprIdentifiers
              context params paramScope dynamicParams localScope constructorArgCount rhs) =
            Except.ok () := by
        by_cases hcall : exprContainsCallLike lhs = true ∨ exprContainsCallLike rhs = true
        · simp [validateScopedExprIdentifiers, validateLogicalOperandPurity, hcall] at hvalidate
          cases hvalidate
        · simpa [validateScopedExprIdentifiers, validateLogicalOperandPurity, hcall] using hvalidate
      intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
      rcases hmem with hmem | hmem
      · exact ihL (validateScopedExprIdentifiers_pair_ok_left hpair) name hmem
      · exact ihR (validateScopedExprIdentifiers_pair_ok_right hpair) name hmem
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
    StmtListScopeDiscipline fieldNames scope stmts := by
  induction hcore generalizing localScope scope finalScope with
  | nil =>
      simp only [validateScopedStmtListIdentifiers, pure, Except.pure] at hvalidate
      cases hvalidate
      exact StmtListScopeDiscipline.nil
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [hExprVal, bind, Except.bind] at h
      · simp only [hExprVal, bind, Except.bind, pure, Except.pure]
        intro h
        split at h <;> try (simp at h)
        split at h <;> try (simp at h)
        cases h
        exact StmtListScopeDiscipline.letVar
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              simp at hmem
              rcases hmem with rfl | hmem
              · exact List.mem_append.mpr <| Or.inl <| by simp [stmtNextScope, collectStmtNames]
              · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | assignVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      -- assignVar: if !localScope.contains name then throw ...; validateExpr ...; pure localScope
      revert hstmt'
      split
      · intro h; simp [bind, Except.bind] at h
      · intro hstmt'
        simp only [bind, Except.bind, pure, Except.pure] at hstmt'
        rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
        · rw [hExprVal] at hstmt'; exact absurd hstmt' (by simp)
        · rw [hExprVal] at hstmt'; simp at hstmt'; cases hstmt'
          exact StmtListScopeDiscipline.assignVar
            hvalueCore
            (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
              hvalueCore hExprVal hparamsInScope hlocalsInScope)
            (ih hrestValidate
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
              (by
                intro other hmem
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | require hcondCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.require
          hcondCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hcondCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | return_ hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.return_
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | stop hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      simp only [pure, Except.pure] at hstmt'
      cases hstmt'
      refine StmtListScopeDiscipline.stop ?_
      exact ih hrestValidate hparamsInScope hlocalsInScope
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.setStorage
          hfield
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | setStorageAddr hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        exact StmtListScopeDiscipline.setStorageAddr
          hfield
          hvalueCore
          (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
            hvalueCore hExprVal hparamsInScope hlocalsInScope)
          (ih hrestValidate
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
            (by
              intro other hmem
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
  | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hCondVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        rcases hThenVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
        · intro h; simp [hThenVal, bind, Except.bind] at h
        · simp only [hThenVal, bind, Except.bind]
          rcases hElseVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
          · intro h; simp [hElseVal, bind, Except.bind] at h
          · simp only [hElseVal, bind, Except.bind, pure, Except.pure]
            intro h; cases h
            exact StmtListScopeDiscipline.ite
              hcondCore
              (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
                hcondCore hCondVal hparamsInScope hlocalsInScope)
              (ihThen hThenVal hparamsInScope hlocalsInScope)
              (ihElse hElseVal hparamsInScope hlocalsInScope)
              (ihRest hrestValidate
                (by
                  intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
                (by
                  intro other hmem
                  exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))
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

theorem stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
    {spec : FunctionSpec}
    {fieldNames : List String}
    {«prefix» «suffix» : List Stmt}
    (hcore : StmtListScopeCore fieldNames «prefix»)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = «prefix» ++ «suffix») :
    StmtListScopeDiscipline fieldNames (spec.params.map (·.name)) «prefix» := by
  rcases validateFunctionIdentifierReferences_prefix_ok hvalidate hbody with
    ⟨finalLocalScope, hprefixValidate⟩
  apply stmtListScopeDiscipline_of_validateScopedStmtListIdentifiers
    (paramScope := paramScopeNames spec.params)
    (dynamicParams := dynamicParamBases spec.params)
    (localScope := [])
    (finalScope := finalLocalScope)
    hcore
    hprefixValidate
  · intro name hmem
    rw [hparamScope] at hmem
    simpa using hmem
  · intro name hmem
    simp at hmem

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
  induction hcore generalizing localScope scope finalScope with
  | nil =>
      simp only [validateScopedStmtListIdentifiers, pure, Except.pure] at hvalidate
      cases hvalidate
      intro name hmem
      exact hlocalsInScope name hmem
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [hExprVal, bind, Except.bind, pure, Except.pure]
        intro h
        split at h <;> try (simp at h)
        split at h <;> try (simp at h)
        cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            simp at hname
            rcases hname with rfl | hname
            · simp [stmtNextScope, collectStmtNames]
            · exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | assignVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      split
      · intro h; simp [bind, Except.bind] at h
      · intro hstmt'
        simp only [bind, Except.bind, pure, Except.pure] at hstmt'
        rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
        · rw [hExprVal] at hstmt'; exact absurd hstmt' (by simp)
        · rw [hExprVal] at hstmt'; simp at hstmt'; cases hstmt'
          intro other hmem
          exact ih hrestValidate
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
            (by
              intro name hname
              exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
            other hmem
  | require hcondCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | return_ hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | stop hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      simp only [pure, Except.pure] at hstmt'
      cases hstmt'
      intro other hmem
      simp only [List.foldl, stmtNextScope, collectStmtNames] at hmem ⊢
      exact ih hrestValidate hparamsInScope hlocalsInScope other hmem
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | setStorageAddr hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hExprVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        intro h; cases h
        intro other hmem
        exact ih hrestValidate
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
          (by
            intro name hname
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
          other hmem
  | ite hcondCore hthenCore helseCore hrest ihThen ihElse ihRest =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      have hstmt' := hstmt
      unfold validateScopedStmtIdentifiers at hstmt'
      revert hstmt'
      rcases hCondVal : validateScopedExprIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
      · intro h; simp [bind, Except.bind] at h
      · simp only [bind, Except.bind, pure, Except.pure]
        rcases hThenVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
        · intro h; simp [hThenVal, bind, Except.bind] at h
        · simp only [hThenVal, bind, Except.bind]
          rcases hElseVal : validateScopedStmtListIdentifiers context params paramScope dynamicParams localScope constructorArgCount _ with _ | _
          · intro h; simp [hElseVal, bind, Except.bind] at h
          · simp only [hElseVal, bind, Except.bind, pure, Except.pure]
            intro h; cases h
            intro other hmem
            exact ihRest hrestValidate
              (by
                intro name hname
                exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
              (by
                intro name hname
                exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
              other hmem
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
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by
  induction hcore with
  | literal _ | caller | contractAddress | msgValue | blockTimestamp | blockNumber | chainid =>
      intro name hmem; simp [collectExprNames] at hmem
  | param _ | localVar _ =>
      intro name hmem; simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
  | add hL hR ihL ihR
  | sub hL hR ihL ihR
  | mul hL hR ihL ihR
  | div hL hR ihL ihR
  | mod hL hR ihL ihR
  | eq hL hR ihL ihR
  | lt hL hR ihL ihR
  | gt hL hR ihL ihR
  | ge hL hR ihL ihR
  | le hL hR ihL ihR
  | bitAnd hL hR ihL ihR
  | bitOr hL hR ihL ihR
  | bitXor hL hR ihL ihR
  | logicalAnd hL hR ihL ihR | logicalOr hL hR ihL ihR
  | shl hL hR ihL ihR | shr hL hR ihL ihR
  | min hL hR ihL ihR | max hL hR ihL ihR
  | ceilDiv hL hR ihL ihR =>
      intro name hmem
      simp [collectExprNames, FunctionBody.exprBoundNames] at hmem ⊢
      rcases hmem with hmem | hmem
      · exact Or.inl (ihL _ hmem)
      · exact Or.inr (ihR _ hmem)
  | logicalNot h ih | bitNot h ih =>
      intro name hmem; simp [collectExprNames] at hmem
      simpa [FunctionBody.exprBoundNames] using ih _ hmem
  | ite hC hT hE ihC ihT ihE =>
      intro name hmem; simp only [collectExprNames] at hmem; simp only [FunctionBody.exprBoundNames]
      rcases List.mem_append.mp hmem with hmem12 | hmem
      · rcases List.mem_append.mp hmem12 with h | h
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (ihC _ h))))
        · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (ihT _ h))))
      · exact List.mem_append.mpr (Or.inr (ihE _ hmem))

private theorem mem_foldl_stmtNextScope_of_mem_scope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ scope) :
    name ∈ List.foldl stmtNextScope scope stmts := by
  induction stmts generalizing scope with
  | nil => simpa
  | cons stmt rest ih =>
      simp only [List.foldl]
      exact ih (by simp [stmtNextScope]; right; exact hmem)

private theorem stmtListNames_subset_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt}
    {name : String}
    (hmem : name ∈ collectStmtListNames stmts) :
    name ∈ List.foldl stmtNextScope scope stmts := by
  induction stmts generalizing scope with
  | nil => simp [collectStmtListNames] at hmem
  | cons stmt rest ih =>
      simp [collectStmtListNames] at hmem
      simp only [List.foldl]
      rcases hmem with hstmt | hrest
      · exact mem_foldl_stmtNextScope_of_mem_scope (by
          simp [stmtNextScope]; left; exact hstmt)
      · exact ih hrest

private theorem stmtListScopeDiscipline_scope_names
    {fieldNames : List String}
    {scope : List String}
    {stmts : List Stmt}
    (hdisc : StmtListScopeDiscipline fieldNames scope stmts) :
    ∀ name, name ∈ List.foldl stmtNextScope scope stmts →
      name ∈
        (scope ++ collectStmtListBindNames stmts ++
          collectStmtListAssignedNames stmts ++ fieldNames) := by
  induction hdisc with
  | nil =>
      intro name hmem
      simp only [List.foldl] at hmem
      simp [collectStmtListBindNames, collectStmtListAssignedNames]
      exact Or.inl hmem
  | letVar hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hname | hvalue | hscope | hbind | hassign | hfield
      · right; left; exact hname
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; right; left; exact hbind
      · right; right; right; left; exact hassign
      · right; right; right; right; exact hfield
  | assignVar hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hname | hvalue | hscope | hbind | hassign | hfield
      · right; right; left; exact hname
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; right; left; exact hassign
      · right; right; right; right; exact hfield
  | require hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hcond | hscope | hbind | hassign | hfield
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfield
  | return_ hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfield
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfield
  | stop _ ih =>
      intro other hmem
      simp only [List.foldl, stmtNextScope, collectStmtNames, List.nil_append] at hmem
      have htail := ih other hmem
      simp [collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      exact htail
  | setStorage _hfield hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | setStorageAddr _hfield hcore hinScope _ ih =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with hvalue | hscope | hbind | hassign | hfld
      · left; exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · left; exact hscope
      · right; left; exact hbind
      · right; right; left; exact hassign
      · right; right; right; exact hfld
  | @ite scope cond thenBranch elseBranch rest hcore hinScope _ _ _ ihThen ihElse ihRest =>
      intro other hmem
      simp only [List.foldl] at hmem
      have htail := ihRest other hmem
      simp only [List.mem_append, stmtNextScope, collectStmtNames,
        collectStmtListBindNames, collectStmtBindNames,
        collectStmtListAssignedNames, collectStmtAssignedNames] at htail ⊢
      rcases htail with ((((( hcond | hthenNames ) | helseNames ) | hscope ) | hbind ) | hassign ) | hfield
      · left; left; left
        exact hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      · have hmemFoldl := stmtListNames_subset_foldl_stmtNextScope (scope := scope) hthenNames
        have hthenResult := ihThen other hmemFoldl
        simp only [List.mem_append,
          collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames] at hthenResult
        rcases hthenResult with (( hscope | hbind ) | hassign ) | hfield
        · left; left; left; exact hscope
        · left; left; right; left; left; exact hbind
        · left; right; left; left; exact hassign
        · right; exact hfield
      · have hmemFoldl := stmtListNames_subset_foldl_stmtNextScope (scope := scope) helseNames
        have helseResult := ihElse other hmemFoldl
        simp only [List.mem_append,
          collectStmtListBindNames, collectStmtBindNames,
          collectStmtListAssignedNames, collectStmtAssignedNames] at helseResult
        rcases helseResult with (( hscope | hbind ) | hassign ) | hfield
        · left; left; left; exact hscope
        · left; left; right; left; right; exact hbind
        · left; right; left; right; exact hassign
        · right; exact hfield
      · left; left; left; exact hscope
      · left; left; right; right; exact hbind
      · left; right; right; exact hassign
      · right; exact hfield

theorem compiledStmtStep_letVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.letVar name value) [YulStmt.let_ name valueIR] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- none case: contradiction (eval_compileExpr_core_of_scope guarantees some)
      simp [hIR, Option.bind] at heval
    · -- some v case: both source and IR succeed
      simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      -- Value is bounded
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact
          hinScope hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
      rw [hEvalSrc] at hvalueLt
      simp at hvalueLt
      -- Define the post-states
      set state' := state.setVar name v
      set runtime' := { runtime with
        bindings := SourceSemantics.bindValue runtime.bindings name v }
      -- IR execution: execIRStmts for a singleton [let_ name valueIR]
      -- Fuel = 1 + extraFuel + 1; execIRStmts strips one level, execIRStmt uses extraFuel
      have hIRExec : execIRStmts (1 + extraFuel + 1) state [YulStmt.let_ name valueIR] =
          .continue state' := by
        -- 1 + extraFuel + 1 = (extraFuel + 1) + 1 = Nat.succ (extraFuel + 1)
        -- execIRStmts strips the outer succ: execIRStmt (extraFuel + 1) state (let_ ...)
        -- extraFuel + 1 = Nat.succ extraFuel; execIRStmt unfolds to match on evalIRExpr
        show (match execIRStmt (1 + extraFuel) state (YulStmt.let_ name valueIR) with
              | .continue s' => execIRStmts (1 + extraFuel) s' []
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) = .continue state'
        have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
        rw [hfuel_eq]
        simp only [execIRStmt, hIR, state']
        simp [execIRStmts]
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime (.letVar name value) =
          .continue runtime' := by
        simp [SourceSemantics.execStmt, hEvalSrc, runtime']
      -- Fuel equality
      have hfuelEq : [YulStmt.let_ name valueIR].length + extraFuel + 1 =
          1 + extraFuel + 1 := by simp
      -- Post-state invariants
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v
      have hexact_base : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (name :: scope) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
      -- Extend to the full stmtNextScope = collectStmtNames (.letVar name value) ++ scope
      -- = (name :: collectExprNames value) ++ scope
      -- Since collectExprNames value ⊆ exprBoundNames value ⊆ scope (by hcore and hinScope),
      -- the full nextScope ⊆ name :: scope.
      have hNextScopeIncl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.letVar name value)) (name :: scope) := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with rfl | hn | hn
        · simp
        · simp [hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hn)]
        · exact List.mem_cons_of_mem _ hn
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.letVar name value)) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact_base hNextScopeIncl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
        FunctionBody.bindingsBounded_bindValue hbounded name v hvalueLt
      have hscope_base : FunctionBody.scopeNamesPresent
          (name :: scope) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_cons_bindValue hscope
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.letVar name value)) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope_base hNextScopeIncl
      -- Provide witnesses
      refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
      · exact hSrcExec
      · rw [hfuelEq]; exact hIRExec
      · simp [stmtStepMatchesIRExec]
        exact ⟨hruntime', hexact', hbounded', hscope'⟩

theorem compiledStmtStep_assignVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.assignVar name value) [YulStmt.assign name valueIR] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- none case: contradiction
      simp [hIR, Option.bind] at heval
    · -- some v case: both source and IR succeed
      simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      -- Value is bounded
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact
          hinScope hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
      rw [hEvalSrc] at hvalueLt
      simp at hvalueLt
      -- Define the post-states
      set state' := state.setVar name v
      set runtime' := { runtime with
        bindings := SourceSemantics.bindValue runtime.bindings name v }
      -- IR execution
      have hIRExec : execIRStmts (1 + extraFuel + 1) state [YulStmt.assign name valueIR] =
          .continue state' := by
        show (match execIRStmt (1 + extraFuel) state (YulStmt.assign name valueIR) with
              | .continue s' => execIRStmts (1 + extraFuel) s' []
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) = .continue state'
        have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
        rw [hfuel_eq]
        simp only [execIRStmt, hIR, state']
        simp [execIRStmts]
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime (.assignVar name value) =
          .continue runtime' := by
        simp [SourceSemantics.execStmt, hEvalSrc, runtime']
      -- Fuel equality
      have hfuelEq : [YulStmt.assign name valueIR].length + extraFuel + 1 =
          1 + extraFuel + 1 := by simp
      -- Post-state invariants
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v
      have hexact_base : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (name :: scope) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
      have hNextScopeIncl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.assignVar name value)) (name :: scope) := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with rfl | hn | hn
        · simp
        · simp [hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hn)]
        · exact List.mem_cons_of_mem _ hn
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.assignVar name value)) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact_base hNextScopeIncl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
        FunctionBody.bindingsBounded_bindValue hbounded name v hvalueLt
      have hscope_base : FunctionBody.scopeNamesPresent
          (name :: scope) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_cons_bindValue hscope
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.assignVar name value)) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope_base hNextScopeIncl
      -- Provide witnesses
      refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
      · exact hSrcExec
      · rw [hfuelEq]; exact hIRExec
      · simp [stmtStepMatchesIRExec]
        exact ⟨hruntime', hexact', hbounded', hscope'⟩

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
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] where
  compileOk := by
    simp [CompilationModel.compileStmt, hfailCompile]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    -- Get the fail condition evaluation
    rcases FunctionBody.eval_compileRequireFailCond_core_of_scope
        hcore hexact hinScope hbounded hpresent hruntime with
      ⟨failCond', hfailCompile', hfailEval⟩
    rw [hfailCompile] at hfailCompile'
    injection hfailCompile' with hfailEq
    subst hfailEq
    -- Get the source condition evaluation
    have hCondEval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded hpresent hruntime
    rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with ⟨condIR, hcondIR⟩
    rw [hcondIR] at hCondEval
    simp [Except.toOption] at hCondEval
    rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
    · simp [hCondIRVal, Option.bind] at hCondEval
    · simp [hCondIRVal, Option.bind] at hCondEval
      have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
        hCondEval.symm
      by_cases hzero : condVal = 0
      · -- condVal = 0 → require fails → revert
        have hfailEval' : evalIRExpr state failCond = some 1 := by
          rw [hCondSrc, hzero] at hfailEval
          simpa [SourceSemantics.boolWord] using hfailEval
        -- Execute the if_ statement: failCond = 1 → enters revert block
        rcases FunctionBody.execIRStmts_revertWithMessage_revert
            (fuel := extraFuel) (state := state) message with
          ⟨revState, hrev⟩
        have hstmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                .revert revState := by
          simp [execIRStmt, hfailEval', hrev]
        have hIRExec :
            execIRStmts (1 + extraFuel + 1) state
              [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] =
                .revert revState := by
          have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
          rw [this]; simp [execIRStmts, hstmt]
        have hSrcExec :
            SourceSemantics.execStmt fields runtime (.require cond message) = .revert := by
          simp [SourceSemantics.execStmt, hCondSrc, hzero]
        have hfuelEq :
            [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
              extraFuel + 1 = 1 + extraFuel + 1 := by simp
        refine ⟨.revert, .revert revState, hSrcExec, ?_, ?_⟩
        · rw [hfuelEq]; exact hIRExec
        · simp [stmtStepMatchesIRExec]
      · -- condVal ≠ 0 → require passes → continue
        have hfailEval' : evalIRExpr state failCond = some 0 := by
          have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
            rw [hCondSrc]; simp [hzero]
          simpa [this, SourceSemantics.boolWord] using hfailEval
        have hstmt' :
            execIRStmt (extraFuel + 1) state
              (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                .continue state := by
          simp [execIRStmt, hfailEval']
        have hIRExec :
            execIRStmts (1 + extraFuel + 1) state
              [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] =
                .continue state := by
          have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
          rw [this]; simp [execIRStmts, hstmt']
        have hSrcExec :
            SourceSemantics.execStmt fields runtime (.require cond message) =
              .continue runtime := by
          simp [SourceSemantics.execStmt, hCondSrc, hzero]
        have hfuelEq :
            [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
              extraFuel + 1 = 1 + extraFuel + 1 := by simp
        -- Prove stmtNextScope inclusion: collectExprNames cond ++ scope ⊆ scope
        have hNextScopeIncl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.require cond message)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hn | hn
          · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hn)
          · exact hn
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.require cond message)) runtime.bindings state :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hNextScopeIncl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.require cond message)) runtime.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hNextScopeIncl
        refine ⟨.continue runtime, .continue state, hSrcExec, ?_, ?_⟩
        · rw [hfuelEq]; exact hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨hruntime, hexact', hbounded, hscope'⟩
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
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] where
  compileOk := by
    simp [CompilationModel.compileStmt, hvalueIR, pure, Except.pure, bind, Except.bind]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    set compiledIR :=
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hwhole := FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope
        (fields := fields) (runtime := runtime) (state := state) (scope := scope)
        (value := value) (tailIR := []) (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    simp only [List.append_nil] at hwhole
    rcases hwhole with ⟨valueIR', hvalueIR', hwhole⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- heval now relates evalIRExpr to evalExpr; extract that evalExpr = some v
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      have hRetVal : (SourceSemantics.evalExpr fields runtime value).getD 0 = v := by
        rw [hEvalSrc]; rfl
      -- Fuel equality
      have hfuelEq : compiledIR.length + extraFuel + 1 =
          sizeOf compiledIR + wholeExtraFuel + 1 := by
        rw [hWF]
        have : compiledIR.length ≤ sizeOf compiledIR := by
          show 2 ≤ sizeOf compiledIR
          have : 0 ≤ sizeOf (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) :=
            Nat.zero_le _
          have : 0 ≤ sizeOf (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) :=
            Nat.zero_le _
          show 2 ≤ 1 + sizeOf (YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) +
                       (1 + sizeOf (YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) + 1)
          omega
        omega
      -- Provide explicit witnesses
      set state' := { state with memory := fun o => if o = 0 then v else state.memory o }
      refine ⟨.return v runtime, .return v state', ?_, ?_, ?_⟩
      · simp [SourceSemantics.execStmt, hEvalSrc]
      · rw [hRetVal] at hwhole; rw [hfuelEq]; exact hwhole
      · simp [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames]
        exact FunctionBody.runtimeStateMatchesIR_setMemory hruntime 0 v

theorem compiledStmtStep_stop
    {fields : List Field}
    {scope : List String} :
    CompiledStmtStep fields scope .stop [YulStmt.expr (YulExpr.call "stop" [])] where
  compileOk := by
    simp [CompilationModel.compileStmt, pure, Except.pure]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Use the helper with wholeFuel aligned to the fuel budget
    set compiledIR := [YulStmt.expr (YulExpr.call "stop" [])]
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hwhole := FunctionBody.execIRStmts_compiled_stop_core_append_wholeFuel
      (state := state) (tailIR := []) (extraFuel := wholeExtraFuel)
    simp only [List.append_nil] at hwhole
    -- Show the fuel values match
    have hfuelEq : compiledIR.length + extraFuel + 1 =
        sizeOf compiledIR + wholeExtraFuel + 1 := by
      rw [hWF]
      have : compiledIR.length ≤ sizeOf compiledIR := by
        show 1 ≤ sizeOf compiledIR
        change 1 ≤ sizeOf ([YulStmt.expr (YulExpr.call "stop" [])] : List YulStmt)
        decide
      omega
    refine ⟨.stop runtime, .stop state, ?_, ?_, ?_⟩
    · simp [SourceSemantics.execStmt]
    · rw [hfuelEq]; exact hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using hruntime

private theorem encodeStorageAt_writeUintSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot query value : Nat}
    (hneq : query ≠ slot) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintSlots world [slot] value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp [SourceSemantics.writeUintSlots, hneq]
  · simp [SourceSemantics.writeUintSlots]
  · simp [SourceSemantics.writeUintSlots]

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
  apply SourceSemantics.encodeStorageAt_congr
  · simp only [SourceSemantics.writeUintSlots]
    rw [show slots.contains query = false from by simpa using hnotMem]
    simp
  · simp [SourceSemantics.writeUintSlots]
  · simp [SourceSemantics.writeUintSlots]

set_option maxHeartbeats 800000 in
private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key query value : Nat}
    (hneq : query ≠ Compiler.Proofs.abstractMappingSlot slot key) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · simp only [SourceSemantics.writeUintKeyedMappingSlots, List.foldl_cons, List.foldl_nil]
    simp [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot] at hneq ⊢
    simp [hneq]
    exact Verity.Core.Uint256.ext (Nat.mod_eq_of_lt (world.storage query).isLt)
  · simp [SourceSemantics.writeUintKeyedMappingSlots]
  · simp [SourceSemantics.writeUintKeyedMappingSlots]

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
  apply SourceSemantics.encodeStorageAt_congr
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots, hneq]
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingChainSlots]

private def mappingWordTargetSlot (slot key wordOffset : Nat) : Nat :=
  SourceSemantics.wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset)

private def mapping2WordTargetSlot (slot key1 key2 wordOffset : Nat) : Nat :=
  SourceSemantics.wordNormalize
    (Compiler.Proofs.abstractMappingSlot
      (Compiler.Proofs.abstractMappingSlot slot key1)
      key2 + wordOffset)

private theorem uint256_add_val_eq_mod (a b : Nat) :
    (Verity.Core.Uint256.ofNat a + Verity.Core.Uint256.ofNat b).val =
      (a + b) % Compiler.Constants.evmModulus := by
  change ((a % Compiler.Constants.evmModulus) + (b % Compiler.Constants.evmModulus)) %
      Compiler.Constants.evmModulus =
    (a + b) % Compiler.Constants.evmModulus
  exact (Nat.add_mod a b Compiler.Constants.evmModulus).symm

private theorem mappingWordTargetSlot_eq_uint256_add (slot key wordOffset : Nat) :
    mappingWordTargetSlot slot key wordOffset =
      (Verity.Core.Uint256.ofNat wordOffset +
        Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val := by
  unfold mappingWordTargetSlot SourceSemantics.wordNormalize
  simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity]

private theorem mapping2WordTargetSlot_eq_uint256_add (slot key1 key2 wordOffset : Nat) :
    mapping2WordTargetSlot slot key1 key2 wordOffset =
      (Verity.Core.Uint256.ofNat wordOffset +
        Verity.Core.Uint256.ofNat
          (Compiler.Proofs.solidityMappingSlot
            (Compiler.Proofs.solidityMappingSlot slot key1) key2)).val := by
  unfold mapping2WordTargetSlot SourceSemantics.wordNormalize
  simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity]

private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    (hneq : query ≠ mappingWordTargetSlot slot key wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq : query = (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mappingWordTargetSlot slot key wordOffset := by
        rw [mappingWordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod (Compiler.Proofs.solidityMappingSlot slot key) wordOffset
            Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMappingWordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMappingWordSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingWordSlots]

private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset query value : Nat}
    {packed : PackedBits}
    (hneq : query ≠ mappingWordTargetSlot slot key wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq : query = (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mappingWordTargetSlot slot key wordOffset := by
        rw [mappingWordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot key)).val =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) % Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot slot key % Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot slot key + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod (Compiler.Proofs.solidityMappingSlot slot key) wordOffset
            Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
  · simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]

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

private theorem findResolvedFieldAtSlot_go_eq_copy
    (remaining : List Field) (idx : Nat) (slot : Nat) :
    SourceSemantics.findResolvedFieldAtSlot.go slot remaining idx =
      findResolvedFieldAtSlotCopy.go slot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
    simp only [SourceSemantics.findResolvedFieldAtSlot.go, findResolvedFieldAtSlotCopy.go]
    split <;> simp_all

private theorem findResolvedFieldAtSlotCopy_eq
    (fields : List Field) (slot : Nat) :
    SourceSemantics.findResolvedFieldAtSlot fields slot =
      findResolvedFieldAtSlotCopy fields slot := by
  simp only [SourceSemantics.findResolvedFieldAtSlot, findResolvedFieldAtSlotCopy]
  exact findResolvedFieldAtSlot_go_eq_copy fields 0 slot

private theorem findDynamicArrayElementAtSlot_scanElements_eq_copy
    (baseSlot : Nat) (elems : List Verity.Core.Uint256) (idx : Nat) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot.scanElements targetSlot baseSlot elems idx =
      findDynamicArrayElementAtSlotCopy.scanElements targetSlot baseSlot elems idx := by
  induction elems generalizing idx with
  | nil => rfl
  | cons v rest ih =>
    simp only [SourceSemantics.findDynamicArrayElementAtSlot.scanElements,
               findDynamicArrayElementAtSlotCopy.scanElements]
    split <;> simp_all

private theorem findDynamicArrayElementAtSlot_go_eq_copy
    (remaining : List Field) (world : Verity.ContractState)
    (idx : Nat) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot.go world targetSlot remaining idx =
      findDynamicArrayElementAtSlotCopy.go world targetSlot remaining idx := by
  induction remaining generalizing idx with
  | nil => rfl
  | cons field rest ih =>
    simp only [SourceSemantics.findDynamicArrayElementAtSlot.go,
               findDynamicArrayElementAtSlotCopy.go]
    simp only [findDynamicArrayElementAtSlot_scanElements_eq_copy]
    split
    · split <;> simp_all
    · simp_all

private theorem findDynamicArrayElementAtSlotCopy_eq
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) :
    SourceSemantics.findDynamicArrayElementAtSlot fields world targetSlot =
      findDynamicArrayElementAtSlotCopy fields world targetSlot := by
  simp only [SourceSemantics.findDynamicArrayElementAtSlot, findDynamicArrayElementAtSlotCopy]
  exact findDynamicArrayElementAtSlot_go_eq_copy fields world 0 targetSlot

private theorem encodeStorageAt_eq_copy
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat} :
    SourceSemantics.encodeStorageAt fields world slot =
      encodeStorageAtCopy fields world slot := by
  simp only [SourceSemantics.encodeStorageAt, encodeStorageAtCopy,
             findResolvedFieldAtSlotCopy_eq, findDynamicArrayElementAtSlotCopy_eq]
  split <;> simp_all
  split <;> simp_all

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
  induction seen with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp at hmem
      by_cases hEq : entry.1 = slot
      · subst hEq
        simp only [List.find?]
        cases entry.2.2 with
        | none => simp [packedSlotsConflict]
        | some _ => simp [packedSlotsConflict]
      · have hrest : slot ∈ List.map (fun entry => entry.1) rest := by
          rcases hmem with ⟨rfl, _⟩ | ⟨_, _, hmem'⟩
          · exact absurd rfl hEq
          · exact List.mem_map.mpr ⟨(slot, _, _), hmem', rfl⟩
        have hih := ih hrest
        change List.find? _ (entry :: rest) ≠ none
        rw [List.find?_cons]
        split
        · simp
        · exact hih

private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hcurrent : slot ∈ current.map (fun entry => entry.1))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by
  induction current generalizing seen with
  | nil =>
      simp at hcurrent
  | cons entry rest ih =>
      simp at hcurrent
      have hpnone : entry.2.2 = none := hunpacked entry.2.2 (by simp)
      have hunpackedRest :
          ∀ packed ∈ rest.map (fun restEntry => restEntry.2.2), packed = none := by
        intro packed hmem
        exact hunpacked packed (by simp [hmem])
      -- entry = (entry.1, entry.2.1, entry.2.2) and entry.2.2 = none
      obtain ⟨e1, e21, e22⟩ := entry
      simp at hpnone
      subst hpnone
      -- Now entry = (e1, e21, none)
      rcases hcurrent with ⟨rfl, _⟩ | ⟨_, _, hrest⟩
      · -- slot = e1
        have hfindSeen := list_findSlotPackedNone_ne_none hseen
        simp only [firstInFieldConflictCopy]
        cases hf : seen.find? (fun seenEntry => seenEntry.1 == e1 && packedSlotsConflict seenEntry.2.2 none)
        · exact absurd hf hfindSeen
        · simp
      · have hrest' : slot ∈ rest.map (fun entry => entry.1) :=
          List.mem_map.mpr ⟨(slot, _, _), hrest, rfl⟩
        intro hnone
        simp only [firstInFieldConflictCopy] at hnone
        cases hfind : seen.find? (fun seenEntry => seenEntry.1 == e1 && packedSlotsConflict seenEntry.2.2 none)
        · rw [hfind] at hnone
          simp at hnone
          have hseen' :
              slot ∈ (((e1, e21, none) :: seen).map (fun seenEntry => seenEntry.1)) := by
            simp [hseen]
          exact (ih hseen' hrest' hunpackedRest) hnone
        · rw [hfind] at hnone; simp at hnone

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
  induction fields generalizing seen idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at hfind
  | cons field rest ih =>
      simp only [findFieldWithResolvedSlotCopyFrom] at hfind
      simp only [findFieldWriteSlotsCopyFrom] at hwrite
      simp only [firstFieldWriteSlotConflictCopyFrom]
      by_cases hname : field.name == fieldName
      · -- field.name matches: hfind and hwrite resolve here
        simp [hname] at hfind hwrite
        obtain ⟨rfl, rfl⟩ := hfind
        subst hwrite
        -- Need: firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) ≠ none
        -- targetSlot ∈ writeSlots = (field.slot.getD idx :: field.aliasSlots)
        -- fieldWriteEntriesAt produces entries with first components matching writeSlots
        -- and all packed bits = field.packedBits = none
        -- The first components of fieldWriteEntriesAt entries are exactly the write slots
        have hwriteEntrySlots :
            (fieldWriteEntriesAt idx field).map (fun entry => entry.1) =
              field.slot.getD idx :: field.aliasSlots := by
          simp only [fieldWriteEntriesAt, List.map_cons, List.map_map]
          congr 1
          show List.map (fun x : Nat × Nat => x.1)
            field.aliasSlots.zipIdx = field.aliasSlots
          exact List.zipIdx_map_fst 0 field.aliasSlots
        have htarget_in_entries :
            targetSlot ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
          rw [hwriteEntrySlots]; exact hslot
        have hunpacked_entries :
            ∀ packed ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.2.2),
              packed = none := by
          unfold fieldWriteEntriesAt
          simp only [List.map_cons, List.map_map, List.mem_cons]
          rintro packed (rfl | hmem)
          · exact hunpacked
          · rw [List.mem_map] at hmem
            obtain ⟨_, _, rfl⟩ := hmem
            exact hunpacked
        have hconflict := firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
          hseen htarget_in_entries hunpacked_entries
        cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
        | none => exact absurd hc hconflict
        | some _ => simp
      · -- field.name doesn't match: recurse
        simp [hname] at hfind hwrite
        have hseen' :
            targetSlot ∈ ((fieldWriteEntriesAt idx field).reverse ++ seen).map
              (fun entry => entry.1) := by
          rw [List.map_append, List.mem_append]
          exact Or.inr hseen
        cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
        | some _ => simp
        | none => exact ih hseen' hfind hwrite

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

private theorem findResolvedFieldAtSlotCopyFrom_of_member
    {fields : List Field}
    {idx : Nat}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    {writeSlots : List Nat}
    {targetSlot : Nat}
    {seen : List (Nat × String × Option PackedBits)}
    (hnoConflict : firstFieldWriteSlotConflictCopyFrom seen idx fields = none)
    (hfind : findFieldWithResolvedSlotCopyFrom fields idx fieldName = some (f, slot))
    (hwrite : findFieldWriteSlotsCopyFrom fields idx fieldName = some writeSlots)
    (hslot : targetSlot ∈ writeSlots)
    (hunpacked : f.packedBits = none) :
    findResolvedFieldAtSlotCopyFrom fields idx targetSlot = some f := by
  induction fields generalizing seen idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at hfind
  | cons field rest ih =>
    simp only [findFieldWithResolvedSlotCopyFrom] at hfind
    simp only [findFieldWriteSlotsCopyFrom] at hwrite
    simp only [firstFieldWriteSlotConflictCopyFrom] at hnoConflict
    simp only [findResolvedFieldAtSlotCopyFrom]
    by_cases hname : field.name == fieldName
    · -- field.name matches: f = field, writeSlots = slot :: aliasSlots
      simp [hname] at hfind hwrite
      obtain ⟨rfl, rfl⟩ := hfind
      subst hwrite
      simp only [List.mem_cons] at hslot
      rcases hslot with rfl | hmem
      · simp
      · simp [hmem]
    · -- field.name doesn't match: recurse
      simp [hname] at hfind hwrite
      cases hc : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field) with
      | some conflict => rw [hc] at hnoConflict; simp at hnoConflict
      | none =>
        rw [hc] at hnoConflict
        -- After simp, condition is Prop-level: = or ∈
        by_cases hcapture :
            field.slot.getD idx = targetSlot ∨ targetSlot ∈ field.aliasSlots
        · exfalso
          have hwriteEntrySlots :
              (fieldWriteEntriesAt idx field).map (fun entry => entry.1) =
                field.slot.getD idx :: field.aliasSlots := by
            simp only [fieldWriteEntriesAt, List.map_cons, List.map_map]
            congr 1; exact List.zipIdx_map_fst 0 field.aliasSlots
          have htargetInEntries :
              targetSlot ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
            rw [hwriteEntrySlots]
            rcases hcapture with rfl | h
            · exact .head _
            · exact .tail _ h
          have htargetInSeen :
              targetSlot ∈ ((fieldWriteEntriesAt idx field).reverse ++ seen).map
                (fun entry => entry.1) := by
            rw [List.map_append, List.mem_append, List.map_reverse]
            exact Or.inl (List.mem_reverse.mpr htargetInEntries)
          exact firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
            htargetInSeen hfind hwrite hslot hunpacked hnoConflict
        · push_neg at hcapture
          simp [hcapture.1, hcapture.2]
          exact ih hnoConflict hfind hwrite

private theorem findResolvedFieldAtSlotCopy_go_eq_CopyFrom
    (flds : List Field) (i s : Nat) :
    findResolvedFieldAtSlotCopy.go s flds i = findResolvedFieldAtSlotCopyFrom flds i s := by
  induction flds generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    simp only [findResolvedFieldAtSlotCopy.go, findResolvedFieldAtSlotCopyFrom]
    split <;> simp_all

private theorem firstInFieldConflict_eq_Copy
    (seen current : List (Nat × String × Option PackedBits)) :
    firstFieldWriteSlotConflict.go.firstInFieldConflict seen current =
      firstInFieldConflictCopy seen current := by
  induction current generalizing seen with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨slot, ownerName, packed⟩ := entry
    simp only [firstFieldWriteSlotConflict_firstInFieldConflict_cons,
               firstInFieldConflictCopy]
    cases seen.find? (fun entry => entry.1 == slot && packedSlotsConflict entry.2.2 packed) with
    | none => exact ih _
    | some _ => rfl

private theorem firstFieldWriteSlotConflict_go_eq_CopyFrom
    (seen : List (Nat × String × Option PackedBits))
    (i : Nat) (flds : List Field) :
    firstFieldWriteSlotConflict.go seen i flds =
      firstFieldWriteSlotConflictCopyFrom seen i flds := by
  induction flds generalizing seen i with
  | nil => rfl
  | cons fld rest ih =>
    rw [firstFieldWriteSlotConflict_go_cons]
    dsimp only []
    simp only [firstFieldWriteSlotConflictCopyFrom, fieldWriteEntriesAt]
    rw [firstInFieldConflict_eq_Copy]
    cases firstInFieldConflictCopy seen _ with
    | none => exact ih _ _
    | some _ => rfl

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
  -- Bridge result
  show findResolvedFieldAtSlotCopy.go targetSlot fields 0 = some f
  rw [findResolvedFieldAtSlotCopy_go_eq_CopyFrom]
  -- Bridge hypotheses
  have hfindCopy : findFieldWithResolvedSlotCopyFrom fields 0 fieldName = some (f, slot) :=
    findFieldWithResolvedSlot_eq_CopyFrom fields fieldName ▸ hfind
  have hwriteCopy : findFieldWriteSlotsCopyFrom fields 0 fieldName = some writeSlots :=
    findFieldWriteSlots_eq_CopyFrom fields fieldName ▸ hwrite
  have hnoConflictCopy : firstFieldWriteSlotConflictCopyFrom [] 0 fields = none :=
    firstFieldWriteSlotConflict_go_eq_CopyFrom [] 0 fields ▸ hnoConflict
  exact findResolvedFieldAtSlotCopyFrom_of_member
    hnoConflictCopy hfindCopy hwriteCopy hslot hunpacked

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

private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by
  simpa [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hnotAddr, hnotDyn]

private theorem encodeStorageAt_eq_storageAddr_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storageAddr slot).val := by
  simpa [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, haddr, hnotDyn]

private theorem encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (Compiler.Proofs.abstractMappingSlot slot key) = value := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeUintKeyedMappingSlots
      world [slot] key value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeUintKeyedMappingSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (Compiler.Proofs.abstractMappingSlot slot key) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeUintKeyedMappingSlots world [slot] key value)
      (Compiler.Proofs.abstractMappingSlot slot key)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (Compiler.Proofs.abstractMappingSlot slot key)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  simp only [hdyn']
  simp only [SourceSemantics.writeUintKeyedMappingSlots, List.foldl_cons, List.foldl_nil]
  simp only [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot]
  simp only [ite_true, Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hvalue

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
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.mappingSlotChain slot keys) = value := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMappingChainSlots
      world [slot] keys value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingChainSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.mappingSlotChain slot keys) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingChainSlots world [slot] keys value)
      (SourceSemantics.mappingSlotChain slot keys)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (SourceSemantics.mappingSlotChain slot keys)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  simp only [hdyn']
  simp only [SourceSemantics.writeAddressKeyedMappingChainSlots, List.map_cons, List.map_nil,
    List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq, ite_true]
  simp only [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hvalue

private theorem encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (mappingWordTargetSlot slot key wordOffset) = value := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMappingWordSlots
      world [slot] key wordOffset value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingWordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (mappingWordTargetSlot slot key wordOffset) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingWordSlots world [slot] key wordOffset value)
      (mappingWordTargetSlot slot key wordOffset)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (mappingWordTargetSlot slot key wordOffset)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMappingWordSlots, mappingWordTargetSlot,
    SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat]
  exact hvalue

private theorem encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key wordOffset value : Nat}
    {packed : PackedBits}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mappingWordTargetSlot slot key wordOffset) = none) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset) =
      SourceSemantics.packedWordWrite
        (world.storage (mappingWordTargetSlot slot key wordOffset)).val
        value
        packed := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
      world [slot] key wordOffset packed value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMappingPackedWordSlots
        world [slot] key wordOffset packed value)
      (mappingWordTargetSlot slot key wordOffset)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (mappingWordTargetSlot slot key wordOffset)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMappingPackedWordSlots, mappingWordTargetSlot,
    SourceSemantics.wordNormalize, SourceSemantics.packedWordWrite,
    Verity.Core.Uint256.val_ofNat]
  have hlt :
      (((Verity.Core.Uint256.ofNat (world.storage (mappingWordTargetSlot slot key wordOffset)).val).and
        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
        (Verity.Core.Uint256.shl packed.offset
          (Verity.Core.Uint256.and value (packedMaskNat packed)))).val <
        Compiler.Constants.evmModulus := by
    exact
      ((((Verity.Core.Uint256.ofNat (world.storage (mappingWordTargetSlot slot key wordOffset)).val).and
        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).or
        (Verity.Core.Uint256.shl packed.offset
          (Verity.Core.Uint256.and value (packedMaskNat packed)))).isLt)
  simpa [mappingWordTargetSlot, SourceSemantics.wordNormalize,
    Compiler.Proofs.abstractMappingSlot_eq_solidity] using hlt

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
  apply SourceSemantics.encodeStorageAt_congr
  · simp only [SourceSemantics.writeAddressKeyedMapping2Slots, List.foldl_cons, List.foldl_nil]
    simp [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot] at hneq ⊢
    simp [hneq]
    exact Verity.Core.Uint256.ext (Nat.mod_eq_of_lt (world.storage query).isLt)
  · simp [SourceSemantics.writeAddressKeyedMapping2Slots]
  · simp [SourceSemantics.writeAddressKeyedMapping2Slots]

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
          key2) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2) = value := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMapping2Slots
      world [slot] key1 key2 value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMapping2Slots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMapping2Slots world [slot] key1 key2 value)
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1) key2)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  simp only [hdyn']
  simp only [SourceSemantics.writeAddressKeyedMapping2Slots, List.foldl_cons, List.foldl_nil]
  simp only [Compiler.Proofs.abstractStoreMappingEntry, Compiler.Proofs.abstractMappingSlot]
  simp only [ite_true, Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hvalue

private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset query value : Nat}
    (hneq :
      query ≠ mapping2WordTargetSlot slot key1 key2 wordOffset) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      query =
      SourceSemantics.encodeStorageAt fields world query := by
  apply SourceSemantics.encodeStorageAt_congr
  · by_cases hEq :
        query =
          (Compiler.Proofs.solidityMappingSlot
            (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
            Compiler.Constants.evmModulus
    · exfalso
      have htarget : query = mapping2WordTargetSlot slot key1 key2 wordOffset := by
        rw [mapping2WordTargetSlot_eq_uint256_add]
        have hslotEq :
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat
                (Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1) key2)).val =
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
              Compiler.Constants.evmModulus := by
          change
            (wordOffset % Compiler.Constants.evmModulus +
                Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1) key2 %
                  Compiler.Constants.evmModulus) %
              Compiler.Constants.evmModulus =
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2 + wordOffset) %
              Compiler.Constants.evmModulus
          rw [Nat.add_comm]
          exact (Nat.add_mod
            (Compiler.Proofs.solidityMappingSlot
              (Compiler.Proofs.solidityMappingSlot slot key1) key2)
            wordOffset Compiler.Constants.evmModulus).symm
        exact hEq.trans hslotEq.symm
      exact hneq htarget
    · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots, List.map_cons, List.map_nil]
      intro hbad
      exact False.elim (hEq hbad)
  · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]
  · simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]

private theorem encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
    {fields : List Field}
    {world : Verity.ContractState}
    {slot key1 key2 wordOffset value : Nat}
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (mapping2WordTargetSlot slot key1 key2 wordOffset) = value := by
  rw [encodeStorageAt_eq_copy]
  simp only [encodeStorageAtCopy, hresolved]
  have harray : (SourceSemantics.writeAddressKeyedMapping2WordSlots
      world [slot] key1 key2 wordOffset value).storageArray = world.storageArray := by
    simp [SourceSemantics.writeAddressKeyedMapping2WordSlots]
  have hdyn' : findDynamicArrayElementAtSlotCopy fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (mapping2WordTargetSlot slot key1 key2 wordOffset) = none := by
    have h1 := findDynamicArrayElementAtSlotCopy_eq fields
      (SourceSemantics.writeAddressKeyedMapping2WordSlots world [slot] key1 key2 wordOffset value)
      (mapping2WordTargetSlot slot key1 key2 wordOffset)
    have h2 := findDynamicArrayElementAtSlotCopy_eq fields world
      (mapping2WordTargetSlot slot key1 key2 wordOffset)
    rw [← h1, SourceSemantics.findDynamicArrayElementAtSlot_congr_storageArray _ _ _ _ harray,
        h2, hdyn]
  rw [hdyn']
  simp [SourceSemantics.writeAddressKeyedMapping2WordSlots, mapping2WordTargetSlot,
    SourceSemantics.wordNormalize, Verity.Core.Uint256.val_ofNat]
  exact hvalue

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
  induction slots generalizing storage with
  | nil =>
      simp [abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      by_cases hEq : query = slot
      · subst hEq
        simpa [abstractStoreStorageOrMappingMany, Compiler.Proofs.abstractStoreStorageOrMapping_eq] using
          (ih (storage := fun s => if s = query then value else storage s))
      · simp [abstractStoreStorageOrMappingMany, ih,
          Compiler.Proofs.abstractStoreStorageOrMapping_eq, hEq]
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
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = slot
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    rw [encodeStorageAt_eq_storage_of_resolvedSlot hresolved hnotAddr hnotDyn]
    simp [SourceSemantics.writeUintSlots, Verity.Core.Uint256.val_ofNat]
    exact (Nat.mod_eq_of_lt hvalue).symm
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeUintSlots_singleton_other hEq).symm

private theorem runtimeStateMatchesIR_writeAddressSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (haddr : SourceSemantics.fieldUsesAddressStorage f = true)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Compiler.Constants.evmModulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressSlots runtime.world [slot] value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot
            (value &&& Compiler.Constants.addressMask) } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = slot
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    rw [encodeStorageAt_eq_storageAddr_of_resolvedSlot hresolved haddr hnotDyn]
    simp [SourceSemantics.writeAddressSlots, Verity.wordToAddress, Verity.Core.Address.ofNat,
          Verity.Core.Uint256.val_ofNat, Verity.Core.Address.modulus, Compiler.Constants.addressMask]
    rw [Nat.mod_eq_of_lt hvalue]
    simpa [Compiler.Constants.addressMask, Verity.Core.Address.modulus] using
      (Nat.and_two_pow_sub_one_eq_mod (n := 160) value)
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    symm
    apply SourceSemantics.encodeStorageAt_congr
    · simp [SourceSemantics.writeAddressSlots]
    · simp [SourceSemantics.writeAddressSlots, hEq]
    · simp [SourceSemantics.writeAddressSlots]

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
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintSlots runtime.world slots value }
      { state with
          storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [abstractStoreStorageOrMappingMany_eq]
  by_cases hmem : slots.contains query = true
  · simp only [hmem, ↓reduceIte]
    have hq : query ∈ slots := by simpa using hmem
    rw [encodeStorageAt_eq_storage_of_resolvedSlot (hresolved query hq) hnotAddr hnotDyn]
    simp only [SourceSemantics.writeUintSlots, hmem, ↓reduceIte, Verity.Core.Uint256.val_ofNat]
    exact (Nat.mod_eq_of_lt hvalue).symm
  · simp only [hmem, ↓reduceIte]
    rw [hstorage]
    have hnotMem : query ∉ slots := by simpa using hmem
    exact (encodeStorageAt_writeUintSlots_other hnotMem).symm

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
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeUintKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = Compiler.Proofs.solidityMappingSlot slot key
  · subst hEq
    simp only [↓reduceIte]
    exact (encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
      (fields := fields) (world := runtime.world) (slot := slot) (key := key) (value := value)
      hresolved hdyn hvalue).symm
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key := key) (query := query) (value := value) hEq).symm

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
        (SourceSemantics.mappingSlotChain slot keys) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingChainSlots
            runtime.world [slot] keys value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (SourceSemantics.mappingSlotChain slot keys)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = SourceSemantics.mappingSlotChain slot keys
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (SourceSemantics.mappingSlotChain slot keys) =
        (runtime.world.storage (SourceSemantics.mappingSlotChain slot keys)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact (encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_eq_written
      (fields := fields) (world := runtime.world) (slot := slot) (keys := keys) (value := value)
      hresolved hdyn hvalue).symm
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeAddressKeyedMappingChainSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (keys := keys)
      (query := query) (value := value) hEq).symm

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
        (Compiler.Proofs.abstractMappingSlot slot key) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with world := SourceSemantics.writeAddressKeyedMappingSlots runtime.world [slot] key value }
      { state with
          storage := Compiler.Proofs.abstractStoreMappingEntry state.storage slot key value } := by
  -- writeAddressKeyedMappingSlots has the same storage/storageAddr/storageArray as writeUintKeyedMappingSlots
  -- so encodeStorageAt produces identical results; we bridge via encodeStorageAt_congr
  have hbridge : ∀ q, SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeAddressKeyedMappingSlots runtime.world [slot] key value) q =
      SourceSemantics.encodeStorageAt fields
      (SourceSemantics.writeUintKeyedMappingSlots runtime.world [slot] key value) q := by
    intro q
    apply SourceSemantics.encodeStorageAt_congr
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
    · simp [SourceSemantics.writeAddressKeyedMappingSlots, SourceSemantics.writeUintKeyedMappingSlots]
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  rw [hbridge]
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query = Compiler.Proofs.solidityMappingSlot slot key
  · subst hEq
    simp only [↓reduceIte]
    exact (encodeStorageAt_writeUintKeyedMappingSlots_singleton_eq_written
      (fields := fields) (world := runtime.world) (slot := slot) (key := key) (value := value)
      hresolved hdyn hvalue).symm
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeUintKeyedMappingSlots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key := key) (query := query) (value := value) hEq).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordSlots
            runtime.world [slot] key wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mappingWordTargetSlot slot key wordOffset)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = mappingWordTargetSlot slot key wordOffset
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) =
        (runtime.world.storage (mappingWordTargetSlot slot key wordOffset)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact (encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_eq_written
      (fields := fields) (world := runtime.world) (slot := slot) (key := key)
      (wordOffset := wordOffset) (value := value) hresolved hdyn hvalue).symm
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeAddressKeyedMappingWordSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (key := key)
      (wordOffset := wordOffset) (query := query) (value := value) hEq).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key wordOffset value : Nat}
    {packed : PackedBits}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mappingWordTargetSlot slot key wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) = none) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMappingPackedWordSlots
            runtime.world [slot] key wordOffset packed value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mappingWordTargetSlot slot key wordOffset)
            (SourceSemantics.packedWordWrite
              (state.storage (mappingWordTargetSlot slot key wordOffset))
              value
              packed) } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = mappingWordTargetSlot slot key wordOffset
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    -- After simp [hstorage], the packedWordWrite arg becomes encodeStorageAt fields runtime.world slot
    -- but _eq_written expects (runtime.world.storage slot).val. Show they're equal.
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (mappingWordTargetSlot slot key wordOffset) =
        (runtime.world.storage (mappingWordTargetSlot slot key wordOffset)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_eq_written
      (fields := fields) (world := runtime.world) (slot := slot) (key := key)
      (wordOffset := wordOffset) (packed := packed) (value := value) hresolved hdyn).symm
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeAddressKeyedMappingPackedWordSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (key := key)
      (wordOffset := wordOffset) (packed := packed) (query := query) (value := value) hEq).symm

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
          key2) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2Slots runtime.world [slot] key1 key2 value }
      { state with
          storage :=
            Compiler.Proofs.abstractStoreMappingEntry
              state.storage
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2
              value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  simp only [Compiler.Proofs.abstractStoreMappingEntry]
  by_cases hEq : query =
      Compiler.Proofs.solidityMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2
  · subst hEq
    simp only [↓reduceIte]
    rw [Compiler.Proofs.abstractMappingSlot_eq_solidity] at hresolved hdyn
    exact (encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_eq_written
      (fields := fields) (world := runtime.world)
      (slot := slot) (key1 := key1) (key2 := key2) (value := value)
      hresolved hdyn hvalue).symm
  · simp only [hEq, ↓reduceIte]
    rw [hstorage]
    rw [Compiler.Proofs.abstractMappingSlot_eq_solidity] at hEq
    exact (encodeStorageAt_writeAddressKeyedMapping2Slots_singleton_other (fields := fields)
      (world := runtime.world) (slot := slot) (key1 := key1) (key2 := key2)
      (query := query) (value := value) hEq).symm

private theorem runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {slot key1 key2 wordOffset value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hresolved :
      findResolvedFieldAtSlotCopy fields
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hdyn :
      findDynamicArrayElementAtSlotCopy fields runtime.world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) = none)
    (hvalue : value < Verity.Core.Uint256.modulus) :
    FunctionBody.runtimeStateMatchesIR fields
      { runtime with
          world := SourceSemantics.writeAddressKeyedMapping2WordSlots
            runtime.world [slot] key1 key2 wordOffset value }
      { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (mapping2WordTargetSlot slot key1 key2 wordOffset)
            value } := by
  rcases hruntime with
    ⟨hstorage, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, htransient, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = mapping2WordTargetSlot slot key1 key2 wordOffset
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    have henc : SourceSemantics.encodeStorageAt fields runtime.world
        (mapping2WordTargetSlot slot key1 key2 wordOffset) =
        (runtime.world.storage (mapping2WordTargetSlot slot key1 key2 wordOffset)).val := by
      rw [encodeStorageAt_eq_copy]
      simp only [encodeStorageAtCopy, hresolved, hdyn]
    simp only [hstorage, henc]
    exact (encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_eq_written
      (fields := fields) (world := runtime.world)
      (slot := slot) (key1 := key1) (key2 := key2) (wordOffset := wordOffset)
      (value := value) hresolved hdyn hvalue).symm
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq]
    simp only [hEq, ↓reduceIte]
    rw [hstorage]
    exact (encodeStorageAt_writeAddressKeyedMapping2WordSlots_singleton_other
      (fields := fields) (world := runtime.world) (slot := slot) (key1 := key1)
      (key2 := key2) (wordOffset := wordOffset) (query := query) (value := value) hEq).symm

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
            storage := abstractStoreStorageOrMappingMany state.storage slots value } := by
  induction slots generalizing state fuel with
  | nil =>
      simp [execIRStmts, abstractStoreStorageOrMappingMany]
  | cons slot rest ih =>
      let nextState :=
        { state with
            storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot value }
      have hstmt :
          execIRStmt (rest.length + fuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, YulExpr.ident name])) =
              .continue nextState := by
        apply execIRStmt_sstore_lit_expr_succ_of_eval
        simp only [evalIRExpr]; exact hvalue
      have hvalueNext : IRState.getVar nextState name = value := by
        simp only [nextState, IRState.getVar]; exact hvalue
      have htail :=
        ih (fuel := fuel) (state := nextState) hvalueNext
      simp only [execIRStmts, List.map, List.length_cons]
      have hfuel : rest.length + 1 + fuel = rest.length + fuel + 1 := by omega
      rw [hfuel, hstmt]
      simp only [abstractStoreStorageOrMappingMany]
      convert htail using 2 <;> omega

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
  have hlet :
      execIRStmt (slots.length + fuel + 1) state
        (YulStmt.let_ tempName valueIR) =
          .continue (state.setVar tempName value) := by
    simp [execIRStmt, hvalue]
  have hslots :=
    execIRStmts_sstore_lit_ident_slots_continue
      fuel
      (state.setVar tempName value)
      slots
      tempName
      value
      (by simp [IRState.getVar, IRState.setVar])
  simpa [execIRStmts, hlet] using hslots

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

private theorem singletonBlock_sizeOf_slack (body : List YulStmt) :
    sizeOf [YulStmt.block body] - [YulStmt.block body].length = sizeOf body + 2 := by
  simp [YulStmt.block.sizeOf_spec]
  omega

private theorem compatValue_not_mem_scope_of_reservedPrefix
    {scope : List String}
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope) :
    "__compat_value" ∉ scope := by
  exact hscopeReserved.1

private theorem compatScratch_startsWith_reserved
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__" = true := by
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_value".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_packed".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_word".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_cleared".toSubstring.take "__".length) "__".toSubstring = true
    simp [Substring.beq, String.toSubstring, Substring.take]
    constructor
    · rfl
    · unfold String.substrEq
      simp
      constructor
      · decide
      · unfold String.substrEq.loop
        simp
        right
        constructor
        · rfl
        · unfold String.substrEq.loop
          simp
          right
          constructor
          · rfl
          · unfold String.substrEq.loop
            simp
            left
            decide

private theorem compatScratch_not_internalImmutable
    {name : String}
    (h :
      name = "__compat_value" ∨
      name = "__compat_packed" ∨
      name = "__compat_slot_word" ∨
      name = "__compat_slot_cleared") :
    name.startsWith "__immutable_" = false := by
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_value".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_packed".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  rcases h with h | h
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_word".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3
  · subst h
    unfold String.startsWith
    change Substring.beq ("__compat_slot_cleared".toSubstring.take "__immutable_".length)
      "__immutable_".toSubstring = false
    simp [Substring.beq, String.toSubstring, Substring.take]
    intro hlen
    unfold String.substrEq
    simp
    intro h1
    intro h2
    unfold String.substrEq.loop
    simp
    constructor
    · decide
    · intro hchar
      unfold String.substrEq.loop
      simp
      constructor
      · decide
      · intro hchar2
        unfold String.substrEq.loop
        simp
        constructor
        · decide
        · intro hchar3
          cases hchar3

private theorem validateIdentifierShapes_fieldName_ne_reservedScratch
    {spec : CompilationModel}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : name ∈ spec.fields.map (·.name)) :
    name ≠ "__compat_value" ∧
    name ≠ "__compat_packed" ∧
    name ≠ "__compat_slot_word" ∧
    name ≠ "__compat_slot_cleared" := by
  rcases List.mem_map.mp hmem with ⟨field, hfield, rfl⟩
  have hreserved :=
    CompilationModel.validateIdentifierShapes_field_avoidReservedCompilerPrefix hvalidate hfield
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_value".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inl rfl)
      have himm : "__compat_value".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_packed".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inl rfl)
      have himm : "__compat_packed".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_slot_word".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inr <| Or.inl rfl)
      have himm : "__compat_slot_word".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inr <| Or.inl rfl)
      simpa [hEq, hprefix, himm])
  · intro hEq
    exact hreserved (by
      have hprefix : "__compat_slot_cleared".startsWith "__" = true := by
        exact compatScratch_startsWith_reserved (Or.inr <| Or.inr <| Or.inr rfl)
      have himm : "__compat_slot_cleared".startsWith "__immutable_" = false := by
        exact compatScratch_not_internalImmutable (Or.inr <| Or.inr <| Or.inr rfl)
      simpa [hEq, hprefix, himm])

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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    have hname := hscopeNames "__compat_value" hmem
    have hname' :
        "__compat_value" ∈ fn.params.map (·.name) ∨
        "__compat_value" ∈ collectStmtListBindNames fn.body ∨
        "__compat_value" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_value" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inl rfl))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inl rfl))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inl rfl))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_packed" hmem
    have hname' :
        "__compat_packed" ∈ fn.params.map (·.name) ∨
        "__compat_packed" ∈ collectStmtListBindNames fn.body ∨
        "__compat_packed" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_packed" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inl rfl)))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_slot_word" hmem
    have hname' :
        "__compat_slot_word" ∈ fn.params.map (·.name) ∨
        "__compat_slot_word" ∈ collectStmtListBindNames fn.body ∨
        "__compat_slot_word" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_slot_word" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inl rfl))))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.2.1 rfl
  · intro hmem
    have hname := hscopeNames "__compat_slot_cleared" hmem
    have hname' :
        "__compat_slot_cleared" ∈ fn.params.map (·.name) ∨
        "__compat_slot_cleared" ∈ collectStmtListBindNames fn.body ∨
        "__compat_slot_cleared" ∈ collectStmtListAssignedNames fn.body ∨
        "__compat_slot_cleared" ∈ spec.fields.map (·.name) := by
      simpa [List.mem_append, or_assoc] using hname
    rcases hname' with hparam | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
          hvalidate hfn hparam) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    rcases hrest with hlocal | hrest
    · exact
        (CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
          hvalidate hfn hlocal) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    rcases hrest with hassign | hfield
    · exact
        (CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
          hvalidate hfn hassign) (compatScratch_startsWith_reserved (Or.inr (Or.inr (Or.inr rfl))))
    · exact (validateIdentifierShapes_fieldName_ne_reservedScratch hvalidate hfield).2.2.2 rfl

private theorem findFieldWriteSlots_of_findFieldWithResolvedSlot
    {fields : List Field} {name : String} {f : Field} {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    findFieldWriteSlots fields name = some (slot :: f.aliasSlots) := by
  rw [findFieldWriteSlots_eq_CopyFrom, findFieldWithResolvedSlot_eq_CopyFrom] at *
  revert h
  suffices ∀ idx,
      findFieldWithResolvedSlotCopyFrom fields idx name = some (f, slot) →
      findFieldWriteSlotsCopyFrom fields idx name = some (slot :: f.aliasSlots) by
    exact this 0
  intro idx h
  induction fields generalizing idx with
  | nil => simp [findFieldWithResolvedSlotCopyFrom] at h
  | cons hd tl ih =>
    unfold findFieldWithResolvedSlotCopyFrom at h
    unfold findFieldWriteSlotsCopyFrom
    by_cases hname : hd.name == name
    · rw [if_pos hname] at h ⊢
      simp at h
      rcases h with ⟨hf, hslot⟩
      rw [← hf, ← hslot]
    · rw [if_neg hname] at h ⊢
      exact ih (idx + 1) h

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
    (hNotMapping : isMapping fields fieldName = false)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, halias, hunpacked, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
    have hresolvedSlot :
        findResolvedFieldAtSlotCopy fields slot = some f :=
      findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
        hnoConflict hfind hwriteSlots hunpacked
    have hvalueSourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at hvalueSourceEval
    simp [Except.toOption] at hvalueSourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcore hexact hinScope hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeUintSlots runtime.world [slot] valueNat }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setStorage fieldName value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hValueSrc, runtime']
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
              .continue state' :=
        execIRStmt_sstore_lit_expr_succ_of_eval
          extraFuel state slot valueIR valueNat hIRValue
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setStorage fieldName value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hv | hs
        · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
        · exact hs
      have hexact' := FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
        (bindingsExactlyMatchIRVarsOnScope_writeUintSlot (slot := slot) (value := valueNat) hexact)
        hincl
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨runtimeStateMatchesIR_writeUintSlot hruntime hresolvedSlot hnotAddr hnotDyn hvalueLt,
        hexact', hbounded, hscope'⟩

private theorem compiledStmtStep_setStorageAddr_singleSlot_preserves
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
    ∀ runtime state extraFuel,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf
          [YulStmt.expr
            (YulExpr.call "sstore"
              [YulExpr.lit slot,
                YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] -
        [YulStmt.expr
          (YulExpr.call "sstore"
            [YulExpr.lit slot,
              YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])].length ≤
        extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.setStorageAddr fieldName value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.lit slot,
                  YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])].length +
              extraFuel + 1)
            state
            [YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.lit slot,
                  YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] =
          irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.setStorageAddr fieldName value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR :=
    [YulStmt.expr
      (YulExpr.call "sstore"
        [YulExpr.lit slot,
          YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])]
  have hresolvedSlot : findResolvedFieldAtSlotCopy fields slot =
      some { name := fieldName, ty := FieldType.address } :=
    findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
      hnoConflict hfind hwriteSlots (by rfl)
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcore hexact hinScope hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
      hruntime
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hvalueSourceEval
  rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
  · simp [hIRValue, Option.bind] at hvalueSourceEval
  · simp [hIRValue, Option.bind] at hvalueSourceEval
    have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
      hvalueSourceEval.symm
    have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hValueSrc] at hvalueLt
    simp at hvalueLt
    have hMaskedEvalRaw :
        evalIRExpr state
          (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
            some ((valueNat % Compiler.Constants.evmModulus) &&&
              (Compiler.Constants.addressMask % Compiler.Constants.evmModulus)) := by
      simpa using FunctionBody.evalIRExpr_and_of_eval
        (state := state)
        (lhs := valueIR)
        (rhs := YulExpr.hex Compiler.Constants.addressMask)
        (b := Compiler.Constants.addressMask)
        hIRValue
        (by simp [evalIRExpr, Compiler.Constants.addressMask])
    have hMaskedEval :
        evalIRExpr state
          (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]) =
            some (valueNat &&& Compiler.Constants.addressMask) := by
      simpa [Nat.mod_eq_of_lt hvalueLt, Compiler.Constants.addressMask] using hMaskedEvalRaw
    set state' := { state with
        storage :=
          Compiler.Proofs.abstractStoreStorageOrMapping state.storage slot
            (valueNat &&& Compiler.Constants.addressMask) }
    set runtime' := { runtime with
        world := SourceSemantics.writeAddressSlots runtime.world [slot] valueNat }
    have hSrcExec : SourceSemantics.execStmt fields runtime
        (.setStorageAddr fieldName value) = .continue runtime' := by
      simp [SourceSemantics.execStmt, hwriteSlots, hValueSrc, runtime']
    have hExecStmt :
        execIRStmt (extraFuel + 1) state
          (YulStmt.expr
            (YulExpr.call "sstore"
              [YulExpr.lit slot,
                YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])) =
          .continue state' :=
      execIRStmt_sstore_lit_expr_succ_of_eval
        extraFuel state slot
        (YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask])
        (valueNat &&& Compiler.Constants.addressMask)
        hMaskedEval
    have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
    have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
        .continue state' := by
      simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
    have hincl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.setStorageAddr fieldName value)) scope := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with hv | hs
      · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
      · exact hs
    have hexact' := FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (bindingsExactlyMatchIRVarsOnScope_writeUintSlot
        (state := state) (slot := slot)
        (value := valueNat &&& Compiler.Constants.addressMask) hexact)
      hincl
    have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
    refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
    simp [stmtStepMatchesIRExec]
    exact ⟨runtimeStateMatchesIR_writeAddressSlot hruntime hresolvedSlot (by rfl) (by rfl) hvalueLt,
      hexact', hbounded, hscope'⟩

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
      [YulStmt.expr
        (YulExpr.call "sstore"
          [YulExpr.lit slot,
            YulExpr.call "and" [valueIR, YulExpr.hex Compiler.Constants.addressMask]])] where
  compileOk := by
    have hNotMapping : isMapping fields fieldName = false :=
      isMapping_false_of_findFieldWithResolvedSlot_address hfind rfl
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, hwriteSlots, hvalueIR]
  preserves := compiledStmtStep_setStorageAddr_singleSlot_preserves
    hcore hinScope hfind hwriteSlots hnoConflict hvalueIR

private theorem compiledStmtStep_mstore_single_preserves
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
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] -
        [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.mstore offset value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.mstore offset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])]
  have hOffsetEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreOffset hexact hinScopeOffset hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
      hruntime
  have hValueEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hoffsetIR] at hOffsetEval
  rw [hvalueIR] at hValueEval
  simp [Except.toOption] at hOffsetEval hValueEval
  rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
  · simp [hIROffset, Option.bind] at hOffsetEval
  · simp [hIROffset, Option.bind] at hOffsetEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hValueEval
    · simp [hIRValue, Option.bind] at hValueEval
      have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
        hOffsetEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hValueEval.symm
      -- Source execution: mstore just checks both exprs evaluate and returns state unchanged
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.mstore offset value) = .continue runtime := by
        simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc]
      -- IR execution
      set state' := { state with
          memory := fun o => if o = offsetNat then valueNat else state.memory o }
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.mstore offset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with ho | hv | hs
        · exact hinScopeOffset n (collectExprNames_mem_exprBoundNames_of_core hcoreOffset n ho)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Post-state invariants: memory update doesn't affect runtimeStateMatchesIR
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.mstore offset value))
          runtime.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope, state'] using hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.mstore offset value))
          runtime.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime state' := by
        simpa [FunctionBody.runtimeStateMatchesIR, state'] using hruntime
      exact ⟨_, _, hSrcExec, hIRExec,
        hruntime', hexact', hbounded, hscope'⟩

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
      [YulStmt.expr (YulExpr.call "mstore" [offsetIR, valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_mstore_single_preserves
    hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

private theorem compiledStmtStep_tstore_single_preserves
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
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] -
        [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])].length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime (.tstore offset value) = sourceResult ∧
        execIRStmts
            ([YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])].length +
              extraFuel + 1)
            state
            [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] = irExec ∧
        stmtStepMatchesIRExec fields
          (stmtNextScope scope (.tstore offset value))
          sourceResult
          irExec := by
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])]
  have hOffsetEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreOffset hexact hinScopeOffset hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeOffset)
      hruntime
  have hValueEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hoffsetIR] at hOffsetEval
  rw [hvalueIR] at hValueEval
  simp [Except.toOption] at hOffsetEval hValueEval
  rcases hIROffset : evalIRExpr state offsetIR with _ | offsetNat
  · simp [hIROffset, Option.bind] at hOffsetEval
  · simp [hIROffset, Option.bind] at hOffsetEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hValueEval
    · simp [hIRValue, Option.bind] at hValueEval
      have hOffsetSrc : SourceSemantics.evalExpr fields runtime offset = some offsetNat :=
        hOffsetEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hValueEval.symm
      -- Get the modulus bound on valueNat for runtimeStateMatchesIR_setTransientStorage
      have hValueLt : SourceSemantics.evalExpr fields runtime value < Compiler.Constants.evmModulus :=
        FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hValueLt
      simp at hValueLt
      -- Source execution: tstore updates transientStorage
      set runtime' := {
        runtime with
        world := {
          runtime.world with
          transientStorage := fun o =>
            if o = offsetNat then valueNat else runtime.world.transientStorage o
        }
      }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.tstore offset value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hOffsetSrc, hValueSrc, runtime']
      -- IR execution: tstore updates transientStorage
      set state' := { state with
          transientStorage := fun o => if o = offsetNat then valueNat else state.transientStorage o }
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExprs, hIROffset, hIRValue, state']
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion for tstore (same structure as mstore)
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.tstore offset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with ho | hv | hs
        · exact hinScopeOffset n (collectExprNames_mem_exprBoundNames_of_core hcoreOffset n ho)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Bindings: getVar only depends on vars, not transientStorage
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.tstore offset value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (by simpa [FunctionBody.bindingsExactlyMatchIRVarsOnScope, state', runtime'] using hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.tstore offset value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
        simpa [runtime'] using hbounded
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setTransientStorage hruntime offsetNat valueNat hValueLt
      exact ⟨_, _, hSrcExec, hIRExec,
        hruntime', hexact', hbounded', hscope'⟩

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
      [YulStmt.expr (YulExpr.call "tstore" [offsetIR, valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, hoffsetIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_tstore_single_preserves
    hcoreOffset hinScopeOffset hcoreValue hinScopeValue hoffsetIR hvalueIR

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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call "sstore"
      [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  -- Case split on IR eval results to extract concrete Nat values
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Define post-states
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreMappingEntry
              state.storage slot keyNat valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeUintKeyedMappingSlots
            runtime.world [slot] keyNat valueNat }
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingUint fieldName key value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime']
      -- IR execution
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExpr, hIRKey, hIRValue,
          Compiler.Proofs.abstractStoreMappingEntry_eq, state']
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingUint fieldName key value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Post-state invariants
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingUint fieldName key value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingUint fieldName key value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨runtimeStateMatchesIR_writeUintKeyedMappingSlot
          hruntime hresolvedNone hdynNone hvalueLt,
        hexact', hbounded, hscope'⟩

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
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

private theorem compileExprList_core_ok
    {fields : List Field}
    {exprs : List Expr}
    (hcore : ∀ expr ∈ exprs, FunctionBody.ExprCompileCore expr) :
    ∃ exprIRs, CompilationModel.compileExprList fields .calldata exprs = Except.ok exprIRs := by
  induction exprs with
  | nil =>
      exact ⟨[], rfl⟩
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail : ∀ e ∈ rest, FunctionBody.ExprCompileCore e := by
        intro e he
        exact hcore e (by simp [he])
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
      rcases ih htail with ⟨restIR, hrestIR⟩
      exact ⟨exprIR :: restIR, by
        rw [CompilationModel.compileExprList, hexprIR, hrestIR]
        rfl
      ⟩
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

private theorem eval_compileExpr_core_some_of_scope
    {fields : List Field}
    {scope : List String}
    {expr : Expr}
    {exprIR : YulExpr}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    (hcore : FunctionBody.ExprCompileCore expr)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hcompiled : CompilationModel.compileExpr fields .calldata expr = Except.ok exprIR) :
    ∃ value,
      SourceSemantics.evalExpr fields runtime expr = some value ∧
      evalIRExpr state exprIR = some value := by
  have hpresent : FunctionBody.exprBoundNamesPresent expr runtime.bindings :=
    FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
  have heval :
      evalIRExpr state exprIR = some (SourceSemantics.evalExpr fields runtime expr) := by
    have h :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded hpresent hruntime
    simpa [hcompiled] using h
  rcases he : SourceSemantics.evalExpr fields runtime expr with _ | value
  · cases hIR : evalIRExpr state exprIR <;> simp [hIR, he] at heval
  · have hIRsome : evalIRExpr state exprIR = some value := by
      cases hIR : evalIRExpr state exprIR with
      | none =>
          simp [hIR, he] at heval
      | some actual =>
          simp [hIR, he] at heval
          subst heval
          exact rfl
    exact ⟨value, rfl, hIRsome⟩

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
  induction exprs generalizing exprIRs with
  | nil =>
      simp [CompilationModel.compileExprList] at hcompiled
      cases hcompiled
      exact ⟨[], rfl, .nil⟩
  | cons expr rest ih =>
      have hhead : FunctionBody.ExprCompileCore expr := hcore expr (by simp)
      have htail :
          ∀ expr' ∈ rest, FunctionBody.ExprCompileCore expr' := by
        intro expr' hexpr'
        exact hcore expr' (by simp [hexpr'])
      have htailScope :
          ∀ expr' ∈ rest, FunctionBody.exprBoundNamesInScope expr' scope := by
        intro expr' hexpr'
        exact hinScope expr' (by simp [hexpr'])
      rcases compileExprList_core_ok (fields := fields) htail with ⟨restIRs, hrestIRs⟩
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hhead with ⟨exprIR, hexprIR⟩
      rw [CompilationModel.compileExprList, hexprIR, hrestIRs] at hcompiled
      injection hcompiled with hcompiledTail
      subst hcompiledTail
      rcases eval_compileExpr_core_some_of_scope
          (expr := expr) (exprIR := exprIR) hhead hexact (hinScope expr (by simp))
          hbounded hscope hruntime hexprIR with
        ⟨headVal, hheadVal, hheadEval⟩
      rcases ih htail htailScope hrestIRs with
        ⟨restVals, hrestVals, hrestEval⟩
      refine ⟨headVal :: restVals, ?_, ?_⟩
      · simp [SourceSemantics.evalExprList, hheadVal, hrestVals]
      · exact .cons hheadEval hrestEval

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
  have hgeneral :
      ∀ {startExpr : YulExpr} {startSlot : Nat},
        evalIRExpr state startExpr = some startSlot →
        evalIRExpr state
            (keyIRs.foldl
              (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
              startExpr) =
          some (List.foldl Compiler.Proofs.abstractMappingSlot startSlot keyVals) := by
    induction hkeys with
    | nil =>
        intro startExpr startSlot hstart
        simpa using hstart
    | @cons exprIR value keyIRs keyVals hexpr hrest ih =>
        intro startExpr startSlot hstart
        have hnext :
            evalIRExpr state (YulExpr.call "mappingSlot" [startExpr, exprIR]) =
              some (Compiler.Proofs.abstractMappingSlot startSlot value) := by
          simp [evalIRExpr, evalIRCall, evalIRExprs, hstart, hexpr,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
        simpa [List.foldl] using
          ih (startExpr := YulExpr.call "mappingSlot" [startExpr, exprIR])
            (startSlot := Compiler.Proofs.abstractMappingSlot startSlot value) hnext
  simpa [SourceSemantics.mappingSlotChain] using
    hgeneral (startExpr := YulExpr.lit baseSlot) (startSlot := baseSlot) (by simp [evalIRExpr])

private theorem execIRStmt_sstore_of_eval
    {state : IRState}
    {slotExpr valueExpr : Compiler.Yul.YulExpr}
    {slotVal valueVal : Nat}
    {fuel : Nat}
    (hslot : evalIRExpr state slotExpr = some slotVal)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
        [slotExpr, valueExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
          slotVal valueVal } := by
  cases slotExpr with
  | lit n => simp [execIRStmt, evalIRExpr, hvalue, hslot]
  | hex n => simp [execIRStmt, evalIRExpr, hvalue, hslot]
  | str s => simp [evalIRExpr] at hslot
  | ident name => simp [execIRStmt, hslot, hvalue]
  | call fname args =>
    cases args with
    | nil => simp [execIRStmt, hslot, hvalue]
    | cons arg rest =>
      cases rest with
      | nil => simp [execIRStmt, hslot, hvalue]
      | cons arg2 rest =>
        cases rest with
        | nil =>
          by_cases hfunc : fname = "mappingSlot"
          · subst hfunc
            simp only [evalIRExpr, evalIRCall, evalIRExprs,
              Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
              Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext] at hslot
            cases hb : evalIRExpr state arg with
            | none => simp [hb] at hslot
            | some bv =>
              cases hk : evalIRExpr state arg2 with
              | none => simp [hb, hk] at hslot
              | some kv =>
                simp [hb, hk] at hslot
                simp [execIRStmt, hb, hk, hvalue,
                  Compiler.Proofs.abstractStoreMappingEntry_eq,
                  Compiler.Proofs.abstractStoreStorageOrMapping_eq,
                  Compiler.Proofs.abstractMappingSlot_eq_solidity, ← hslot]
          · simp [execIRStmt, hslot, hvalue, hfunc]
        | cons arg3 rest => simp [execIRStmt, hslot, hvalue]

private theorem execIRStmt_sstore_foldl_mappingSlot
    {state : IRState}
    {baseSlot : Nat}
    {keyIRs : List Compiler.Yul.YulExpr}
    {keyVals : List Nat}
    {valueExpr : Compiler.Yul.YulExpr}
    {valueVal : Nat}
    {fuel : Nat}
    (hkeys : List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) keyIRs keyVals)
    (hvalue : evalIRExpr state valueExpr = some valueVal) :
    execIRStmt (Nat.succ fuel) state
      (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
        [keyIRs.foldl
          (fun slotExpr keyExpr => Compiler.Yul.YulExpr.call "mappingSlot" [slotExpr, keyExpr])
          (Compiler.Yul.YulExpr.lit baseSlot), valueExpr])) =
      .continue { state with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
          (SourceSemantics.mappingSlotChain baseSlot keyVals) valueVal } := by
  suffices ∀ (startExpr : Compiler.Yul.YulExpr) (startSlot : Nat)
      (kIRs : List Compiler.Yul.YulExpr) (kVals : List Nat),
      List.Forall₂ (fun exprIR value => evalIRExpr state exprIR = some value) kIRs kVals →
      evalIRExpr state startExpr = some startSlot →
      execIRStmt (Nat.succ fuel) state
        (Compiler.Yul.YulStmt.expr (Compiler.Yul.YulExpr.call "sstore"
          [kIRs.foldl
            (fun slotExpr keyExpr => Compiler.Yul.YulExpr.call "mappingSlot" [slotExpr, keyExpr])
            startExpr, valueExpr])) =
        .continue { state with
          storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage
            (kVals.foldl Compiler.Proofs.abstractMappingSlot startSlot) valueVal } by
    simpa [SourceSemantics.mappingSlotChain] using
      this (Compiler.Yul.YulExpr.lit baseSlot) baseSlot keyIRs keyVals hkeys (by simp [evalIRExpr])
  intro startExpr startSlot kIRs kVals hf hstart
  induction hf generalizing startExpr startSlot with
  | nil =>
    simp only [List.foldl]
    exact execIRStmt_sstore_of_eval hstart hvalue
  | @cons exprIR keyVal kIRs' kVals' hexpr _ ih =>
    simp only [List.foldl]
    have hnext : evalIRExpr state
        (Compiler.Yul.YulExpr.call "mappingSlot" [startExpr, exprIR]) =
          some (Compiler.Proofs.abstractMappingSlot startSlot keyVal) := by
      simp [evalIRExpr, evalIRCall, evalIRExprs, hstart, hexpr,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
        Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext]
    exact ih (Compiler.Yul.YulExpr.call "mappingSlot" [startExpr, exprIR])
      (Compiler.Proofs.abstractMappingSlot startSlot keyVal) hnext

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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let writeSlotExpr :=
    keyIRs.foldl
      (fun slotExpr keyExpr => YulExpr.call "mappingSlot" [slotExpr, keyExpr])
      (YulExpr.lit slot)
  let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])]
  -- Evaluate value expression
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hvalueSourceEval
  rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
  · simp [hIRValue, Option.bind] at hvalueSourceEval
  · simp [hIRValue, Option.bind] at hvalueSourceEval
    have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
      hvalueSourceEval.symm
    -- Evaluate key list expressions
    rcases eval_compileExprList_core_of_scope
        hcoreKeys hexact hinScopeKeys hbounded hscope hruntime hkeyIRs with
      ⟨resolvedKeys, hkeysEval, hkeyIRVals⟩
    -- Slot safety
    rcases hslotSafety runtime resolvedKeys hkeysEval with
      ⟨hresolvedNone, hdynNone⟩
    -- Compute the foldl slot expression
    have hWriteSlotEval :
        evalIRExpr state writeSlotExpr =
          some (SourceSemantics.mappingSlotChain slot resolvedKeys) :=
      evalIRExpr_mappingSlotChain hkeyIRVals
    -- Value boundedness
    have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
        hcoreValue hexact hinScopeValue hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
        hruntime
    rw [hValueSrc] at hvalueLt
    simp at hvalueLt
    -- Define post-states
    set state' := { state with
        storage :=
          Compiler.Proofs.abstractStoreStorageOrMapping
            state.storage
            (SourceSemantics.mappingSlotChain slot resolvedKeys)
            valueNat }
    set runtime' := { runtime with
        world := SourceSemantics.writeAddressKeyedMappingChainSlots
          runtime.world [slot] resolvedKeys valueNat }
    -- Source execution
    have hSrcExec : SourceSemantics.execStmt fields runtime
        (.setMappingChain fieldName keys value) = .continue runtime' := by
      simp [SourceSemantics.execStmt, hwriteSlots, hkeysEval, hValueSrc, runtime']
    -- IR execution
    have hExecStmt :
        execIRStmt (extraFuel + 1) state
          (YulStmt.expr (YulExpr.call "sstore" [writeSlotExpr, valueIR])) =
            .continue state' := by
      exact execIRStmt_sstore_foldl_mappingSlot hkeyIRVals hIRValue
    have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
    have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
        .continue state' := by
      simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
    -- Scope inclusion
    have hincl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.setMappingChain fieldName keys value)) scope := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with hk | hv | hs
      · -- name from collectExprListNames keys — prove ∃ expr ∈ keys with name ∈ collectExprNames expr
        suffices ∀ (ks : List Expr),
            (∀ e, e ∈ ks → FunctionBody.ExprCompileCore e) →
            (∀ e, e ∈ ks → FunctionBody.exprBoundNamesInScope e scope) →
            n ∈ collectExprListNames ks → n ∈ scope from
          this keys hcoreKeys hinScopeKeys hk
        intro ks hcore' hscope' hmem
        induction ks with
        | nil => simp [collectExprListNames] at hmem
        | cons hd tl ih =>
          simp [collectExprListNames] at hmem
          rcases hmem with hhd | htl
          · exact hscope' hd (by simp) n
              (collectExprNames_mem_exprBoundNames_of_core (hcore' hd (by simp)) n hhd)
          · exact ih (fun e he => hcore' e (by simp [he]))
              (fun e he => hscope' e (by simp [he])) htl
      · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
      · exact hs
    -- Post-state invariants
    have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (stmtNextScope scope (.setMappingChain fieldName keys value))
        runtime'.bindings state' :=
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
        (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
        hincl
    have hscope' : FunctionBody.scopeNamesPresent
        (stmtNextScope scope (.setMappingChain fieldName keys value))
        runtime'.bindings :=
      FunctionBody.scopeNamesPresent_of_included hscope hincl
    have hbounded' : FunctionBody.bindingsBounded runtime'.bindings := by
      simpa [runtime'] using hbounded
    have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
      runtimeStateMatchesIR_writeAddressKeyedMappingChainSlot
        hruntime hresolvedNone hdynNone hvalueLt
    exact ⟨_, _, hSrcExec, hIRExec,
      hruntime', hexact', hbounded', hscope'⟩

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
            (YulExpr.lit slot), valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetMappingChain,
      hmapping, hwriteSlots, hkeyIRs, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves
    hcoreKeys hinScopeKeys hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIRs hvalueIR

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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call "sstore"
      [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  -- Case split on IR eval results to extract concrete Nat values
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Define post-states
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreMappingEntry
              state.storage slot keyNat valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeAddressKeyedMappingSlots
            runtime.world [slot] keyNat valueNat }
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMapping fieldName key value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime']
      -- IR execution
      have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr
              (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
              .continue state' := by
        simp [execIRStmt, evalIRExpr, hIRKey, hIRValue,
          Compiler.Proofs.abstractStoreMappingEntry_eq, state']
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
          .continue state' := by
        simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMapping fieldName key value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Post-state invariants
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMapping fieldName key value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMapping fieldName key value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingSlot
          hruntime hresolvedNone hdynNone hvalueLt,
        hexact', hbounded, hscope'⟩

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
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      -- Get boundedness of valueNat
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Define post-states
      set targetSlot := mappingWordTargetSlot slot keyNat wordOffset
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreStorageOrMapping
              state.storage targetSlot valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordSlots
            runtime.world [slot] keyNat wordOffset valueNat }
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingWord fieldName key wordOffset value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, runtime']
      -- Scope inclusion: stmtNextScope only adds expr names already in scope
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      -- Post-state invariants
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setMappingWord fieldName key wordOffset value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      -- IR execution: case split on wordOffset
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      by_cases hzero : wordOffset = 0
      · -- wordOffset = 0: slot expr is just mappingSlot, uses abstractStoreMappingEntry
        subst hzero
        have hTargetZero :
            mappingWordTargetSlot slot keyNat 0 = Compiler.Proofs.abstractMappingSlot slot keyNat := by
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (Nat.mod_eq_of_lt hlt)
        have hStoreEq : Compiler.Proofs.abstractStoreMappingEntry state.storage slot keyNat valueNat =
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage
              (mappingWordTargetSlot slot keyNat 0) valueNat := by
          simp [Compiler.Proofs.abstractStoreStorageOrMapping,
            Compiler.Proofs.abstractStoreMappingEntry, hTargetZero]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          have hTargetZero' : targetSlot = Compiler.Proofs.solidityMappingSlot slot keyNat := by
            simpa [targetSlot, Compiler.Proofs.abstractMappingSlot_eq_solidity] using hTargetZero
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey, hIRValue,
            state', hTargetZero', Compiler.Proofs.abstractStoreMappingEntry_eq,
            Compiler.Proofs.abstractStoreStorageOrMapping_eq]
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
            hruntime hresolvedNone hdynNone hvalueLt,
          hexact', hbounded, hscope'⟩
      · -- wordOffset ≠ 0: slot expr is add [mappingSlot [...], lit wordOffset]
        -- Use keccak axiom: mappingSlot + wordOffset < evmModulus
        -- Reduce the if-then-else: wordOffset ≠ 0 means we take the else branch
        have hbeq : (wordOffset == 0) = false := by
          simp [beq_iff_eq, hzero]
        have hTargetMod :
            (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
              Compiler.Constants.evmModulus = targetSlot := by
          rw [show targetSlot =
            (Verity.Core.Uint256.ofNat wordOffset +
              Verity.Core.Uint256.ofNat
                (Compiler.Proofs.solidityMappingSlot slot keyNat)).val by
              simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset]
          simpa [Nat.add_comm] using
            (uint256_add_val_eq_mod wordOffset
              (Compiler.Proofs.solidityMappingSlot slot keyNat)).symm
        have hTargetAdd :
            targetSlot =
              (Verity.Core.Uint256.ofNat wordOffset +
                Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val := by
          simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset
        have hStoreEq :
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat =
              fun s =>
                if s =
                    (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
                      Compiler.Constants.evmModulus then
                  valueNat
                else
                  state.storage s := by
          funext s
          rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, ← hTargetMod]
        -- The compiled IR with the if-else reduced
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "sstore"
                [YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR],
                   YulExpr.lit wordOffset], valueIR])) =
                .continue state' := by
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
            hIRKey, hIRValue,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
            Compiler.Proofs.abstractMappingSlot_eq_solidity,
            state', hTargetMod, hStoreEq]
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "add"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR],
                 YulExpr.lit wordOffset], valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        -- Now show the goal with the if-else reduced matches
        refine ⟨.continue runtime', .continue state', hSrcExec, ?_, ?_⟩
        · -- IR execution: reduce the if-then-else, then use hIRExec
          simp only [List.length_singleton, hbeq, ite_false]
          exact hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩

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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMappingWord fieldName key wordOffset value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingSlotWrite,
      hmapping, hwriteSlots, hkeyIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hwriteSlots hslotSafety hkeyIR hvalueIR

private theorem uint256_and_val_eq_land_mod (a b : Nat) :
    (Verity.Core.Uint256.and a b).val =
      ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  simp only [Verity.Core.Uint256.and, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
  have hlt : Nat.land (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) <
      Compiler.Constants.evmModulus := by
    have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
      exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
    have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
      exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    exact Nat.and_lt_two_pow (a % Compiler.Constants.evmModulus)
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using hb)
  exact Nat.mod_eq_of_lt hlt

private theorem uint256_or_val_eq_lor_mod (a b : Nat) :
    (Verity.Core.Uint256.or a b).val =
      ((a % Compiler.Constants.evmModulus) ||| (b % Compiler.Constants.evmModulus)) := by
  simp only [Verity.Core.Uint256.or, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS]
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have hb : b % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have hlt : Nat.lor (a % Compiler.Constants.evmModulus) (b % Compiler.Constants.evmModulus) <
      Compiler.Constants.evmModulus := by
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    exact Nat.or_lt_two_pow
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using ha)
      (by simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using hb)
  exact Nat.mod_eq_of_lt hlt

private theorem uint256_not_val_eq_xor_allOnes_mod (a : Nat) :
    (Verity.Core.Uint256.not a).val =
      Nat.xor (a % Compiler.Constants.evmModulus) (Compiler.Constants.evmModulus - 1) := by
  have ha : a % Compiler.Constants.evmModulus < Compiler.Constants.evmModulus := by
    exact Nat.mod_lt _ (by simp [Compiler.Constants.evmModulus])
  have ha256 : a % Compiler.Constants.evmModulus < 2 ^ 256 := by
    simpa [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl] using ha
  have hxor_eq : Nat.xor (a % Compiler.Constants.evmModulus) (2 ^ 256 - 1) =
      2 ^ 256 - 1 - (a % Compiler.Constants.evmModulus) := by
    have key :
        (BitVec.ofNat 256 (a % Compiler.Constants.evmModulus) ^^^ BitVec.allOnes 256).toNat =
          2 ^ 256 - 1 - (a % Compiler.Constants.evmModulus) := by
      rw [BitVec.xor_allOnes]
      simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha256]
    have lhs_eq :
        Nat.xor (a % Compiler.Constants.evmModulus) (2 ^ 256 - 1) =
          (BitVec.ofNat 256 (a % Compiler.Constants.evmModulus) ^^^ BitVec.allOnes 256).toNat := by
      simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha256, BitVec.toNat_allOnes]
      rfl
    rw [lhs_eq, key]
  rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
  simp only [Verity.Core.Uint256.not, Verity.Core.Uint256.val_ofNat, Verity.Core.MAX_UINT256,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS]
  rw [hxor_eq, Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 - (a % 2 ^ 256) < 2 ^ 256)]

private theorem uint256_shl_val_eq_mul_pow_mod
    (shift value : Nat)
    (hshift : shift < 256) :
    (Verity.Core.Uint256.shl shift value).val =
      ((value % Compiler.Constants.evmModulus) * 2 ^ shift) % Compiler.Constants.evmModulus := by
  have hshiftLt : shift < Compiler.Constants.evmModulus := by
    rw [show Compiler.Constants.evmModulus = 2 ^ 256 by rfl]
    omega
  simp only [Verity.Core.Uint256.shl, Verity.Core.Uint256.val_ofNat,
    Verity.Core.Uint256.modulus, Compiler.Constants.evmModulus, Verity.Core.UINT256_MODULUS,
    Nat.mod_eq_of_lt hshiftLt]
  rw [Nat.shiftLeft_eq]

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let writeSlotExpr :=
    let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
    if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
  let blockBody :=
    [ YulStmt.let_ "__compat_value" valueIR
    , YulStmt.let_ "__compat_packed"
        (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])
    , YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [writeSlotExpr])
    , YulStmt.let_ "__compat_slot_cleared"
        (YulExpr.call "and"
          [YulExpr.ident "__compat_slot_word",
            YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])
    , YulStmt.expr
        (YulExpr.call "sstore"
          [writeSlotExpr,
            YulExpr.call "or"
              [YulExpr.ident "__compat_slot_cleared",
                YulExpr.call "shl"
                  [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]]) ]
  let compiledIR := [YulStmt.block blockBody]
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      set targetSlot := mappingWordTargetSlot slot keyNat wordOffset
      set oldWordNat := state.storage targetSlot
      set storedWordNat := SourceSemantics.packedWordWrite oldWordNat valueNat packed
      have hMappingBaseEval :
          evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKey] : List.Forall₂
              (fun exprIR value => evalIRExpr state exprIR = some value)
              [keyIR] [keyNat]))
      have hpackedOffsetLt : packed.offset < 256 := by
        have hvalid := hpacked
        simp [CompilationModel.packedBitsValid] at hvalid
        omega
      have hWriteSlotEval : evalIRExpr state writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      set state1 := state.setVar "__compat_value" valueNat
      have hCompatValue :
          ∀ fuel, execIRStmt (fuel + 1) state (YulStmt.let_ "__compat_value" valueIR) =
            .continue state1 := by
        intro fuel
        simp [state1, execIRStmt, hIRValue]
      have hPackedEval :
          evalIRExpr state1
            (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)]) =
              some (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val := by
        simpa [uint256_and_val_eq_land_mod] using
          FunctionBody.evalIRExpr_and_of_eval
            (state := state1)
            (lhs := YulExpr.ident "__compat_value")
            (rhs := YulExpr.lit (packedMaskNat packed))
            (a := valueNat)
            (b := packedMaskNat packed)
            (by simp [evalIRExpr, state1, IRState.getVar, IRState.setVar])
            (by simp [evalIRExpr])
      set state2 := state1.setVar "__compat_packed" (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val
      have hCompatPacked :
          ∀ fuel, execIRStmt (fuel + 1) state1
            (YulStmt.let_ "__compat_packed"
              (YulExpr.call "and" [YulExpr.ident "__compat_value", YulExpr.lit (packedMaskNat packed)])) =
            .continue state2 := by
        intro fuel
        simp [state2, execIRStmt, hPackedEval]
      have hexact_state1 :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state1 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (value := valueNat) hexact hcompatValue
      have hexact_state2 :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state2 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hexact_state1 hcompatPacked
      have hruntimeCompat1 : FunctionBody.runtimeStateMatchesIR fields runtime state1 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_value") (value := valueNat) hruntime
      have hruntimeCompat2 : FunctionBody.runtimeStateMatchesIR fields runtime state2 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hruntimeCompat1
      have hIRKeyState2 : evalIRExpr state2 keyIR = some keyNat := by
        have h := FunctionBody.eval_compileExpr_core_of_scope
            hcoreKey hexact_state2 hinScopeKey hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
            hruntimeCompat2
        rw [hkeyIR] at h
        simp [Except.toOption, hKeySrc] at h
        cases h' : evalIRExpr state2 keyIR <;> simp [h'] at h
        simpa using congrArg some h
      have hMappingBaseEval2 :
          evalIRExpr state2 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state2)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKeyState2] : List.Forall₂
              (fun exprIR value => evalIRExpr state2 exprIR = some value)
              [keyIR] [keyNat]))
      have hWriteSlotEval2 : evalIRExpr state2 writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state2 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval2)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state2)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval2
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state2
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      have hSlotWordEval :
          evalIRExpr state2 (YulExpr.call "sload" [writeSlotExpr]) = some oldWordNat := by
        simp [evalIRExpr, evalIRCall, evalIRExprs, hWriteSlotEval2,
          Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
          Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext, oldWordNat, state2, state1]
      set state3 := state2.setVar "__compat_slot_word" oldWordNat
      have hexact_state3 : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state3 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact_state2 hcompatSlotWord
      have hruntimeCompat3 : FunctionBody.runtimeStateMatchesIR fields runtime state3 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntimeCompat2
      have hCompatSlotWord :
          ∀ fuel, execIRStmt (fuel + 1) state2
            (YulStmt.let_ "__compat_slot_word" (YulExpr.call "sload" [writeSlotExpr])) =
            .continue state3 := by
        intro fuel
        simp [state3, execIRStmt, hSlotWordEval]
      have hSlotClearedEval :
          evalIRExpr state3
            (YulExpr.call "and"
              [YulExpr.ident "__compat_slot_word",
                YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]]) =
              some (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
        have hNotEval :
            evalIRExpr state3
              (YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]) =
                some (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val := by
          simpa [uint256_not_val_eq_xor_allOnes_mod] using
            (FunctionBody.evalIRExpr_not_of_eval
              (state := state3)
              (expr := YulExpr.lit (packedShiftedMaskNat packed))
              (value := packedShiftedMaskNat packed)
              (by simp [evalIRExpr]))
        have hAndEval :=
          FunctionBody.evalIRExpr_and_of_eval
            (state := state3)
            (lhs := YulExpr.ident "__compat_slot_word")
            (rhs := YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)])
            (a := oldWordNat)
            (b := (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val)
            (by simp [evalIRExpr, state3, state2, state1, IRState.getVar, IRState.setVar])
            hNotEval
        have hAndBridge :
            ((oldWordNat % Compiler.Constants.evmModulus) &&&
                ((Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val %
                  Compiler.Constants.evmModulus)) =
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val := by
          have hNotLt :
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed)).isLt
          have hNotOfNat :
              Verity.Core.Uint256.ofNat ((Verity.Core.Uint256.not (packedShiftedMaskNat packed)).val) =
                Verity.Core.Uint256.not (packedShiftedMaskNat packed) := by
            ext
            simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hNotLt]
          simpa [Nat.mod_eq_of_lt hNotLt, hNotOfNat] using
            (uint256_and_val_eq_land_mod oldWordNat
              ((Verity.Core.Uint256.ofNat (packedShiftedMaskNat packed)).not.val)).symm
        simpa [hAndBridge] using hAndEval
      set state4 := state3.setVar "__compat_slot_cleared"
        (Verity.Core.Uint256.and oldWordNat
          (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val
      have hexact_state4 : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state4 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant hexact_state3 hcompatSlotCleared
      have hruntimeCompat4 : FunctionBody.runtimeStateMatchesIR fields runtime state4 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntimeCompat3
      have hCompatSlotCleared :
          ∀ fuel, execIRStmt (fuel + 1) state3
            (YulStmt.let_ "__compat_slot_cleared"
              (YulExpr.call "and"
                [YulExpr.ident "__compat_slot_word",
                  YulExpr.call "not" [YulExpr.lit (packedShiftedMaskNat packed)]])) =
            .continue state4 := by
        intro fuel
        simp [state4, execIRStmt, hSlotClearedEval]
      have hStoredEval :
          evalIRExpr state4
            (YulExpr.call "or"
              [YulExpr.ident "__compat_slot_cleared",
                YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]) =
              some storedWordNat := by
        have hpackedOffsetLtMod : packed.offset < Compiler.Constants.evmModulus := by
          have hevmmodGt256 : 256 < Compiler.Constants.evmModulus := by
            decide
          exact lt_trans hpackedOffsetLt hevmmodGt256
        have hShlEval :
            evalIRExpr state4
              (YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]) =
                some (Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val := by
          simpa [Nat.mod_eq_of_lt hpackedOffsetLtMod, uint256_shl_val_eq_mul_pow_mod, hpackedOffsetLt] using
            (FunctionBody.evalIRExpr_shl_of_eval
              (state := state4)
              (shiftExpr := YulExpr.lit packed.offset)
              (valueExpr := YulExpr.ident "__compat_packed")
              (shift := packed.offset)
              (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
              (by simp [evalIRExpr])
              (by simp [evalIRExpr, state4, state3, state2, state1, IRState.getVar, IRState.setVar]))
        have hOrEval :=
          FunctionBody.evalIRExpr_or_of_eval
            (state := state4)
            (lhs := YulExpr.ident "__compat_slot_cleared")
            (rhs := YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"])
            (a := (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
            (b := (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val)
            (by simp [evalIRExpr, state4, state3, state2, state1, IRState.getVar, IRState.setVar])
            hShlEval
        have hClearedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.and oldWordNat
                  (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val) =
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))) := by
          have hClearedLt :
              (Verity.Core.Uint256.and oldWordNat
                (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hClearedLt]
        have hShiftedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val) =
              (Verity.Core.Uint256.shl packed.offset
                (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) := by
          have hShiftedLt :
              (Verity.Core.Uint256.shl packed.offset
                (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hShiftedLt]
        have hPackedOfNat :
            Verity.Core.Uint256.ofNat
                ((Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val) =
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)) := by
          have hPackedLt :
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val <
                Compiler.Constants.evmModulus :=
            (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).isLt
          ext
          simp [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt hPackedLt]
        have hClearedLt :
            (Verity.Core.Uint256.and oldWordNat
              (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val <
              Compiler.Constants.evmModulus :=
          (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).isLt
        have hShiftedLt :
            (Verity.Core.Uint256.shl packed.offset
              (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val <
              Compiler.Constants.evmModulus :=
          (Verity.Core.Uint256.shl packed.offset
            (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).isLt
        have hOrBridge :
            ((((Verity.Core.Uint256.and oldWordNat
                    (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val %
                  Compiler.Constants.evmModulus) |||
                ((Verity.Core.Uint256.shl packed.offset
                      (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val %
                  Compiler.Constants.evmModulus))) =
              (((Verity.Core.Uint256.ofNat
                      ((Verity.Core.Uint256.and oldWordNat
                        (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)).or
                  (Verity.Core.Uint256.ofNat
                    ((Verity.Core.Uint256.shl packed.offset
                      (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val))).val) := by
          simpa [uint256_or_val_eq_lor_mod, Nat.mod_eq_of_lt hClearedLt, Nat.mod_eq_of_lt hShiftedLt]
            using
              (uint256_or_val_eq_lor_mod
                ((Verity.Core.Uint256.and oldWordNat
                  (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
                ((Verity.Core.Uint256.shl packed.offset
                  (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val).val)).symm
        rw [hOrBridge] at hOrEval
        rw [hShiftedOfNat] at hOrEval
        simpa [storedWordNat, SourceSemantics.packedWordWrite, hClearedOfNat, hPackedOfNat]
          using hOrEval
      set state' := { state4 with
        storage := Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot storedWordNat }
      have hIRKeyState4 : evalIRExpr state4 keyIR = some keyNat := by
        have h :=
          FunctionBody.eval_compileExpr_core_of_scope
            hcoreKey hexact_state4 hinScopeKey hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
            hruntimeCompat4
        rw [hkeyIR] at h
        simp [Except.toOption, hKeySrc] at h
        cases h' : evalIRExpr state4 keyIR <;> simp [h'] at h
        simpa using congrArg some h
      have hMappingBaseEval4 :
          evalIRExpr state4 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
            some (Compiler.Proofs.abstractMappingSlot slot keyNat) := by
        simpa using
          (evalIRExpr_mappingSlotChain
            (state := state4)
            (baseSlot := slot)
            (keyIRs := [keyIR])
            (keyVals := [keyNat])
            (by simp [hIRKeyState4] : List.Forall₂
              (fun exprIR value => evalIRExpr state4 exprIR = some value)
              [keyIR] [keyNat]))
      have hWriteSlotEval4 : evalIRExpr state4 writeSlotExpr = some targetSlot := by
        dsimp [writeSlotExpr, targetSlot]
        by_cases hzero : wordOffset = 0
        · subst hzero
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [Verity.Core.Uint256.val_ofNat, mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (show evalIRExpr state4 (YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]) =
              some (Compiler.Proofs.solidityMappingSlot slot keyNat % Compiler.Constants.evmModulus) by
                simpa [Nat.mod_eq_of_lt hlt, Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                  hMappingBaseEval4)
        · have hAddEval :=
            FunctionBody.evalIRExpr_add_of_eval
              (state := state4)
              (lhs := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR])
              (rhs := YulExpr.lit wordOffset)
              (a := Compiler.Proofs.abstractMappingSlot slot keyNat)
              (b := wordOffset)
              hMappingBaseEval4
              (by simp [evalIRExpr])
          have hAddEval' :
              evalIRExpr state4
                (YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], YulExpr.lit wordOffset]) =
                some ((Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat (Compiler.Proofs.solidityMappingSlot slot keyNat)).val) := by
            rw [uint256_add_val_eq_mod]
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hAddEval
          simpa [hzero, targetSlot, mappingWordTargetSlot_eq_uint256_add] using hAddEval'
      have hSstore :
          ∀ fuel, execIRStmt (fuel + 1) state4
            (YulStmt.expr
              (YulExpr.call "sstore"
                [writeSlotExpr,
                  YulExpr.call "or"
                      [YulExpr.ident "__compat_slot_cleared",
                        YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])) =
            .continue state' := by
        intro fuel
        simpa [state', state4, state3, state2, state1] using
          (execIRStmt_sstore_of_eval
            (state := state4)
            (slotExpr := writeSlotExpr)
            (valueExpr := YulExpr.call "or"
              [YulExpr.ident "__compat_slot_cleared",
                YulExpr.call "shl" [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]])
            (slotVal := targetSlot)
            (valueVal := storedWordNat)
            (fuel := fuel)
            hWriteSlotEval4
            hStoredEval)
      have hSizeOfListBound : ∀ (l : List YulStmt), l.length + 1 ≤ sizeOf l := by
        intro l
        induction l with
        | nil => simp
        | cons h t ih =>
            show t.length + 1 + 1 ≤ 1 + sizeOf h + sizeOf t
            omega
      have hbodyFuelLe : 6 ≤ extraFuel := by
        have hBodyLen : blockBody.length = 5 := by
          simp [blockBody]
        have hBodyBound := hSizeOfListBound blockBody
        have hBlockSizeOf : 6 ≤ sizeOf [YulStmt.block blockBody] - [YulStmt.block blockBody].length := by
          rw [singletonBlock_sizeOf_slack]
          omega
        exact le_trans hBlockSizeOf hslack
      let bodyExtraFuel := extraFuel - 6
      have hbodyFuelEq : bodyExtraFuel + 6 = extraFuel := by
        dsimp [bodyExtraFuel]
        omega
      have hBody :
          execIRStmts extraFuel state blockBody = .continue state' := by
        rw [← hbodyFuelEq]
        simp [execIRStmts, blockBody, bodyExtraFuel,
          hCompatValue (bodyExtraFuel + 4),
          hCompatPacked (bodyExtraFuel + 3),
          hCompatSlotWord (bodyExtraFuel + 2),
          hCompatSlotCleared (bodyExtraFuel + 1),
          hSstore bodyExtraFuel]
      have hWhole :
          execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = .continue state' := by
        have hblock := execIRStmts_single_block_of_continue
          extraFuel state state' blockBody hBody
        simpa [compiledIR, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hblock
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setMappingPackedWord fieldName key wordOffset packed value) =
            .continue
              { runtime with
                  world := SourceSemantics.writeAddressKeyedMappingPackedWordSlots
                    runtime.world [slot] keyNat wordOffset packed valueNat } := by
        simp [SourceSemantics.execStmt, hwriteSlots, hKeySrc, hValueSrc, hpacked,
          SourceSemantics.writeAddressKeyedMappingPackedWordSlots]
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hruntime1 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_value") (value := valueNat) hruntime
      have hruntime2 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hruntime1
      have hruntime3 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_slot_word") (value := oldWordNat) hruntime2
      have hruntime4 :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
          (name := "__compat_slot_cleared")
          (value := (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
          hruntime3
      have hruntime' :
          FunctionBody.runtimeStateMatchesIR fields
            { runtime with
                world := SourceSemantics.writeAddressKeyedMappingPackedWordSlots
                  runtime.world [slot] keyNat wordOffset packed valueNat }
            state' := by
        simpa [state', targetSlot, oldWordNat, storedWordNat] using
          runtimeStateMatchesIR_writeAddressKeyedMappingPackedWordSlot
            (runtime := runtime)
            (state := state4)
            (slot := slot) (key := keyNat) (wordOffset := wordOffset) (packed := packed)
            (value := valueNat) hruntime4 hresolvedNone hdynNone
      have hexact1 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_value") (value := valueNat) hexact hcompatValue
      have hexact2 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_packed")
          (value := (Verity.Core.Uint256.and valueNat (packedMaskNat packed)).val)
          hexact1 hcompatPacked
      have hexact3 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_slot_word") (value := oldWordNat)
          hexact2 hcompatSlotWord
      have hexact4 :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          (tempName := "__compat_slot_cleared")
          (value := (Verity.Core.Uint256.and oldWordNat
            (Verity.Core.Uint256.not (packedShiftedMaskNat packed))).val)
          hexact3 hcompatSlotCleared
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setMappingPackedWord fieldName key wordOffset packed value))
          runtime.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact4) hincl
      refine ⟨_, _, hSrcExec, hWhole, ?_⟩
      simp [stmtStepMatchesIRExec]
      exact ⟨hruntime', hexact', hbounded, hscope'⟩
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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
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
                     [YulExpr.lit packed.offset, YulExpr.ident "__compat_packed"]]])]] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileMappingPackedSlotWrite,
      hmapping, hpacked, hwriteSlots, hkeyIR, hvalueIR, Bool.not_true, bne_self_eq_false,
      ite_false, ite_true, pure, Except.pure, bind, Except.bind]
    rfl
  preserves := compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue
    hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared
    hpacked hwriteSlots hslotSafety hkeyIR hvalueIR

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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  have hkeySourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey hexact hinScopeKey hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey)
      hruntime
  have hvalueSourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreValue hexact hinScopeValue hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
      hruntime
  rw [hkeyIR] at hkeySourceEval
  rw [hvalueIR] at hvalueSourceEval
  simp [Except.toOption] at hkeySourceEval hvalueSourceEval
  rcases hIRKey : evalIRExpr state keyIR with _ | keyNat
  · simp [hIRKey, Option.bind] at hkeySourceEval
  · simp [hIRKey, Option.bind] at hkeySourceEval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at hvalueSourceEval
    · simp [hIRValue, Option.bind] at hvalueSourceEval
      have hKeySrc : SourceSemantics.evalExpr fields runtime key = some keyNat :=
        hkeySourceEval.symm
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        hvalueSourceEval.symm
      rcases hslotSafety runtime keyNat hKeySrc with ⟨hresolvedNone, hdynNone⟩
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      set targetSlot := mappingWordTargetSlot slot keyNat wordOffset
      set state' := { state with
          storage :=
            Compiler.Proofs.abstractStoreStorageOrMapping
              state.storage targetSlot valueNat }
      set runtime' := { runtime with
          world := SourceSemantics.writeAddressKeyedMappingWordSlots
            runtime.world [slot] keyNat wordOffset valueNat }
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setStructMember fieldName key memberName value) = .continue runtime' := by
        simp [SourceSemantics.execStmt, hwriteSlots, hmembers, hmember, hKeySrc, hValueSrc, runtime']
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setStructMember fieldName key memberName value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hk | hv | hs
        · exact hinScopeKey n (collectExprNames_mem_exprBoundNames_of_core hcoreKey n hk)
        · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
        · exact hs
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setStructMember fieldName key memberName value))
          runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
          hincl
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.setStructMember fieldName key memberName value))
          runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope hincl
      have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
      by_cases hzero : wordOffset = 0
      · subst hzero
        have hTargetZero :
            mappingWordTargetSlot slot keyNat 0 = Compiler.Proofs.abstractMappingSlot slot keyNat := by
          have hlt :
              Compiler.Proofs.solidityMappingSlot slot keyNat < Compiler.Constants.evmModulus := by
            simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Compiler.Proofs.abstractMappingSlot_lt_evmModulus slot keyNat)
          simpa [mappingWordTargetSlot, SourceSemantics.wordNormalize,
            Compiler.Proofs.abstractMappingSlot_eq_solidity] using
            (Nat.mod_eq_of_lt hlt)
        have hStoreEq : Compiler.Proofs.abstractStoreMappingEntry state.storage slot keyNat valueNat =
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage
              (mappingWordTargetSlot slot keyNat 0) valueNat := by
          simp [Compiler.Proofs.abstractStoreStorageOrMapping,
            Compiler.Proofs.abstractStoreMappingEntry, hTargetZero]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "sstore"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])) =
                .continue state' := by
          have hTargetZero' : targetSlot = Compiler.Proofs.solidityMappingSlot slot keyNat := by
            simpa [targetSlot, Compiler.Proofs.abstractMappingSlot_eq_solidity] using hTargetZero
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey, hIRValue,
            state', hTargetZero', Compiler.Proofs.abstractStoreMappingEntry_eq,
            Compiler.Proofs.abstractStoreStorageOrMapping_eq]
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR], valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
            hruntime hresolvedNone hdynNone hvalueLt,
          hexact', hbounded, hscope'⟩
      · -- wordOffset ≠ 0: slot expr is add [mappingSlot [...], lit wordOffset]
        -- Use keccak axiom: mappingSlot + wordOffset < evmModulus
        have hbeq : (wordOffset == 0) = false := by
          simp [beq_iff_eq, hzero]
        have hTargetAdd :
            targetSlot =
              (Verity.Core.Uint256.ofNat wordOffset +
                Verity.Core.Uint256.ofNat
                  (Compiler.Proofs.solidityMappingSlot slot keyNat)).val := by
          simpa [targetSlot] using mappingWordTargetSlot_eq_uint256_add slot keyNat wordOffset
        have hTargetMod :
            (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
              Compiler.Constants.evmModulus = targetSlot := by
          rw [hTargetAdd]
          simpa [Nat.add_comm] using
            (uint256_add_val_eq_mod wordOffset
              (Compiler.Proofs.solidityMappingSlot slot keyNat)).symm
        have hStoreEq :
            Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat =
              fun s =>
                if s =
                    (Compiler.Proofs.solidityMappingSlot slot keyNat + wordOffset) %
                      Compiler.Constants.evmModulus then
                  valueNat
                else
                  state.storage s := by
          funext s
          rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, ← hTargetMod]
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr (YulExpr.call "sstore"
                [YulExpr.call "add"
                  [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR],
                   YulExpr.lit wordOffset], valueIR])) =
                .continue state' := by
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
            hIRKey, hIRValue,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
            Compiler.Proofs.abstractMappingSlot_eq_solidity,
            state', hTargetMod, hStoreEq]
        have hIRExec : execIRStmts (1 + extraFuel + 1) state
            [YulStmt.expr (YulExpr.call "sstore"
              [YulExpr.call "add"
                [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR],
                 YulExpr.lit wordOffset], valueIR])] =
            .continue state' := by
          simp [execIRStmts, hfuelEq, hExecStmt]
        refine ⟨.continue runtime', .continue state', hSrcExec, ?_, ?_⟩
        · simp only [List.length_singleton, hbeq, ite_false]
          exact hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMappingWordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩

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
    (hnotMapping2 : isMapping2 fields fieldName = false)
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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none)
    (hkeyIR : CompilationModel.compileExpr fields .calldata key = Except.ok keyIR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember fieldName key memberName value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyIR]
           if wordOffset == 0 then mappingBase
           else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetStructMember,
      CompilationModel.compileMappingSlotWrite, hmapping, hnotMapping2, hmembers, hmember,
      hwriteSlots, hkeyIR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves
    hcoreKey hinScopeKey hcoreValue hinScopeValue hmembers hmember hwriteSlots
    hslotSafety hkeyIR hvalueIR

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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call "sstore"
      [YulExpr.call "mappingSlot"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])]
  -- Evaluate key1 expression
  have hkey1SourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey1 hexact hinScopeKey1 hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
      hruntime
  rw [hkey1IR] at hkey1SourceEval
  simp [Except.toOption] at hkey1SourceEval
  rcases hIRKey1 : evalIRExpr state key1IR with _ | key1Nat
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
    -- Evaluate key2 expression
    have hkey2SourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcoreKey2 hexact hinScopeKey2 hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
        hruntime
    rw [hkey2IR] at hkey2SourceEval
    simp [Except.toOption] at hkey2SourceEval
    rcases hIRKey2 : evalIRExpr state key2IR with _ | key2Nat
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
      -- Evaluate value expression
      have hvalueSourceEval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hvalueIR] at hvalueSourceEval
      simp [Except.toOption] at hvalueSourceEval
      rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
      · simp [hIRValue, Option.bind] at hvalueSourceEval
      · simp [hIRValue, Option.bind] at hvalueSourceEval
        have hKey1Src : SourceSemantics.evalExpr fields runtime key1 = some key1Nat :=
          hkey1SourceEval.symm
        have hKey2Src : SourceSemantics.evalExpr fields runtime key2 = some key2Nat :=
          hkey2SourceEval.symm
        have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          hvalueSourceEval.symm
        rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
        -- Get boundedness of valueNat
        have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
            hcoreValue hexact hinScopeValue hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
            hruntime
        rw [hValueSrc] at hvalueLt
        simp at hvalueLt
        -- Define post-states
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreMappingEntry
                state.storage
                (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                key2Nat
                valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMapping2Slots
              runtime.world [slot] key1Nat key2Nat valueNat }
        -- Source execution
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMapping2 fieldName key1 key2 value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime']
        -- IR execution
        have hExecStmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.expr
                (YulExpr.call "sstore"
                  [YulExpr.call "mappingSlot"
                    [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
                .continue state' := by
          simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey1, hIRKey2, hIRValue,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
            Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
            Compiler.Proofs.abstractStoreMappingEntry_eq, state']
        have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
        have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue state' := by
          simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
        -- Scope inclusion
        have hincl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.setMapping2 fieldName key1 key2 value)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hk1 | hk2 | hv | hs
          · exact hinScopeKey1 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey1 n hk1)
          · exact hinScopeKey2 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey2 n hk2)
          · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
          · exact hs
        -- Post-state invariants
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeMappingSlot hexact)
            hincl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping2 fieldName key1 key2 value))
            runtime'.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hincl
        refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
        simp [stmtStepMatchesIRExec]
        exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2Slot
            hruntime hresolvedNone hdynNone hvalueLt,
          hexact', hbounded, hscope'⟩

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
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetMapping2,
      hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call "sstore"
      [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
       let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
       if wordOffset == 0 then mappingSlot2
       else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])]
  -- Evaluate key1 expression
  have hkey1SourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey1 hexact hinScopeKey1 hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
      hruntime
  rw [hkey1IR] at hkey1SourceEval
  simp [Except.toOption] at hkey1SourceEval
  rcases hIRKey1 : evalIRExpr state key1IR with _ | key1Nat
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
    -- Evaluate key2 expression
    have hkey2SourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcoreKey2 hexact hinScopeKey2 hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
        hruntime
    rw [hkey2IR] at hkey2SourceEval
    simp [Except.toOption] at hkey2SourceEval
    rcases hIRKey2 : evalIRExpr state key2IR with _ | key2Nat
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
      -- Evaluate value expression
      have hvalueSourceEval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hvalueIR] at hvalueSourceEval
      simp [Except.toOption] at hvalueSourceEval
      rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
      · simp [hIRValue, Option.bind] at hvalueSourceEval
      · simp [hIRValue, Option.bind] at hvalueSourceEval
        have hKey1Src : SourceSemantics.evalExpr fields runtime key1 = some key1Nat :=
          hkey1SourceEval.symm
        have hKey2Src : SourceSemantics.evalExpr fields runtime key2 = some key2Nat :=
          hkey2SourceEval.symm
        have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          hvalueSourceEval.symm
        rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
        -- Get boundedness of valueNat
        have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
            hcoreValue hexact hinScopeValue hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
            hruntime
        rw [hValueSrc] at hvalueLt
        simp at hvalueLt
        -- Define post-states
        set targetSlot := mapping2WordTargetSlot slot key1Nat key2Nat wordOffset
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage targetSlot valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMapping2WordSlots
              runtime.world [slot] key1Nat key2Nat wordOffset valueNat }
        -- Source execution
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setMapping2Word fieldName key1 key2 wordOffset value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hKey1Src, hKey2Src, hValueSrc, runtime']
        -- Scope inclusion
        have hincl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hk1 | hk2 | hv | hs
          · exact hinScopeKey1 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey1 n hk1)
          · exact hinScopeKey2 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey2 n hk2)
          · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
          · exact hs
        -- Post-state invariants
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
            hincl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setMapping2Word fieldName key1 key2 wordOffset value))
            runtime'.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hincl
        by_cases hzero : wordOffset = 0
        · -- wordOffset = 0: slot expr is mappingSlot [mappingSlot [lit slot, key1IR], key2IR]
          subst hzero
          have hTargetZero :
              mapping2WordTargetSlot slot key1Nat key2Nat 0 =
                Compiler.Proofs.abstractMappingSlot
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat := by
            have hlt :
                Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat <
                  Compiler.Constants.evmModulus := by
              simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                (Compiler.Proofs.abstractMappingSlot_lt_evmModulus
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
            simpa [mapping2WordTargetSlot, SourceSemantics.wordNormalize,
              Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Nat.mod_eq_of_lt hlt)
          have hStoreEq :
              Compiler.Proofs.abstractStoreMappingEntry
                state.storage
                (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                key2Nat
                valueNat =
              Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage
                (Compiler.Proofs.abstractMappingSlot
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
                valueNat := by
            funext s
            simp [Compiler.Proofs.abstractStoreMappingEntry_eq,
              Compiler.Proofs.abstractStoreStorageOrMapping_eq,
              Compiler.Proofs.abstractMappingSlot]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call "sstore"
                    [YulExpr.call "mappingSlot"
                      [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
              .continue state' := by
            simpa [state', targetSlot, hTargetZero, hStoreEq] using
              (show
                execIRStmt (extraFuel + 1) state
                  (YulStmt.expr
                    (YulExpr.call "sstore"
                      [YulExpr.call "mappingSlot"
                        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
                  .continue
                    { state with
                      storage := Compiler.Proofs.abstractStoreMappingEntry
                        state.storage
                        (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                        key2Nat
                        valueNat } by
                simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey1, hIRKey2, hIRValue,
                  Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
                  Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
                  Compiler.Proofs.abstractStoreMappingEntry_eq])
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩
        · -- wordOffset ≠ 0: slot expr is add [mappingSlot [mappingSlot [...], ...], lit wordOffset]
          -- Use keccak axiom: nested mappingSlot + wordOffset < evmModulus
          have hbeq : (wordOffset == 0) = false := by
            simp [beq_iff_eq, hzero]
          have hTargetAdd :
              targetSlot =
                (Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat
                    (Compiler.Proofs.solidityMappingSlot
                      (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val := by
            simpa [targetSlot] using
              mapping2WordTargetSlot_eq_uint256_add slot key1Nat key2Nat wordOffset
          have hTargetMod :
              (Compiler.Proofs.solidityMappingSlot
                (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat + wordOffset) %
                Compiler.Constants.evmModulus = targetSlot := by
            rw [hTargetAdd]
            simpa [Nat.add_comm] using
              (uint256_add_val_eq_mod wordOffset
                (Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).symm
          have hStoreEq :
              Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat =
                fun s =>
                  if s =
                      (Verity.Core.Uint256.ofNat wordOffset +
                        Verity.Core.Uint256.ofNat
                          (Compiler.Proofs.solidityMappingSlot
                            (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val then
                    valueNat
                  else
                    state.storage s := by
            funext s
            rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hTargetAdd]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call "sstore"
                    [YulExpr.call "add"
                      [YulExpr.call "mappingSlot"
                        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR],
                       YulExpr.lit wordOffset], valueIR])) =
                .continue state' := by
              simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
                hIRKey1, hIRKey2, hIRValue,
                Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
                Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
                Compiler.Proofs.abstractMappingSlot_eq_solidity,
                state', hTargetMod, hStoreEq]
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp only [compiledIR, hbeq, ite_false]
            simp [execIRStmts, hfuelEq, hExecStmt]
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setMapping2Word fieldName key1 key2 wordOffset value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetMapping2Word,
      hmapping2, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
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
  intro runtime state extraFuel hexact hscope hbounded hruntime hslack
  let compiledIR := [YulStmt.expr
    (YulExpr.call "sstore"
      [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
       let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
       if wordOffset == 0 then mappingSlot2
       else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])]
  -- Evaluate key1 expression
  have hkey1SourceEval :=
    FunctionBody.eval_compileExpr_core_of_scope
      hcoreKey1 hexact hinScopeKey1 hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey1)
      hruntime
  rw [hkey1IR] at hkey1SourceEval
  simp [Except.toOption] at hkey1SourceEval
  rcases hIRKey1 : evalIRExpr state key1IR with _ | key1Nat
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
  · simp [hIRKey1, Option.bind] at hkey1SourceEval
    -- Evaluate key2 expression
    have hkey2SourceEval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcoreKey2 hexact hinScopeKey2 hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeKey2)
        hruntime
    rw [hkey2IR] at hkey2SourceEval
    simp [Except.toOption] at hkey2SourceEval
    rcases hIRKey2 : evalIRExpr state key2IR with _ | key2Nat
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
    · simp [hIRKey2, Option.bind] at hkey2SourceEval
      -- Evaluate value expression
      have hvalueSourceEval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcoreValue hexact hinScopeValue hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
          hruntime
      rw [hvalueIR] at hvalueSourceEval
      simp [Except.toOption] at hvalueSourceEval
      rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
      · simp [hIRValue, Option.bind] at hvalueSourceEval
      · simp [hIRValue, Option.bind] at hvalueSourceEval
        have hKey1Src : SourceSemantics.evalExpr fields runtime key1 = some key1Nat :=
          hkey1SourceEval.symm
        have hKey2Src : SourceSemantics.evalExpr fields runtime key2 = some key2Nat :=
          hkey2SourceEval.symm
        have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
          hvalueSourceEval.symm
        rcases hslotSafety runtime key1Nat key2Nat hKey1Src hKey2Src with ⟨hresolvedNone, hdynNone⟩
        -- Get boundedness of valueNat
        have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
            hcoreValue hexact hinScopeValue hbounded
            (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScopeValue)
            hruntime
        rw [hValueSrc] at hvalueLt
        simp at hvalueLt
        -- Define post-states
        set targetSlot := mapping2WordTargetSlot slot key1Nat key2Nat wordOffset
        set state' := { state with
            storage :=
              Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage targetSlot valueNat }
        set runtime' := { runtime with
            world := SourceSemantics.writeAddressKeyedMapping2WordSlots
              runtime.world [slot] key1Nat key2Nat wordOffset valueNat }
        -- Source execution
        have hSrcExec : SourceSemantics.execStmt fields runtime
            (.setStructMember2 fieldName key1 key2 memberName value) = .continue runtime' := by
          simp [SourceSemantics.execStmt, hwriteSlots, hmembers, hmember,
            hKey1Src, hKey2Src, hValueSrc, runtime']
        -- Scope inclusion
        have hincl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.setStructMember2 fieldName key1 key2 memberName value)) scope := by
          intro n hn
          simp [stmtNextScope, collectStmtNames] at hn
          rcases hn with hk1 | hk2 | hv | hs
          · exact hinScopeKey1 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey1 n hk1)
          · exact hinScopeKey2 n (collectExprNames_mem_exprBoundNames_of_core hcoreKey2 n hk2)
          · exact hinScopeValue n (collectExprNames_mem_exprBoundNames_of_core hcoreValue n hv)
          · exact hs
        -- Post-state invariants
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.setStructMember2 fieldName key1 key2 memberName value))
            runtime'.bindings state' :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
            (bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact)
            hincl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.setStructMember2 fieldName key1 key2 memberName value))
            runtime'.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hincl
        by_cases hzero : wordOffset = 0
        · -- wordOffset = 0: slot expr is mappingSlot [mappingSlot [lit slot, key1IR], key2IR]
          subst hzero
          have hTargetZero :
              mapping2WordTargetSlot slot key1Nat key2Nat 0 =
                Compiler.Proofs.abstractMappingSlot
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat := by
            have hlt :
                Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat <
                  Compiler.Constants.evmModulus := by
              simpa [Compiler.Proofs.abstractMappingSlot_eq_solidity] using
                (Compiler.Proofs.abstractMappingSlot_lt_evmModulus
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
            simpa [mapping2WordTargetSlot, SourceSemantics.wordNormalize,
              Compiler.Proofs.abstractMappingSlot_eq_solidity] using
              (Nat.mod_eq_of_lt hlt)
          have hStoreEq :
              Compiler.Proofs.abstractStoreMappingEntry
                state.storage
                (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                key2Nat
                valueNat =
              Compiler.Proofs.abstractStoreStorageOrMapping
                state.storage
                (Compiler.Proofs.abstractMappingSlot
                  (Compiler.Proofs.abstractMappingSlot slot key1Nat) key2Nat)
                valueNat := by
            funext s
            simp [Compiler.Proofs.abstractStoreMappingEntry_eq,
              Compiler.Proofs.abstractStoreStorageOrMapping_eq,
              Compiler.Proofs.abstractMappingSlot]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call "sstore"
                    [YulExpr.call "mappingSlot"
                      [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
              .continue state' := by
            simpa [state', targetSlot, hTargetZero, hStoreEq] using
              (show
                execIRStmt (extraFuel + 1) state
                  (YulStmt.expr
                    (YulExpr.call "sstore"
                      [YulExpr.call "mappingSlot"
                        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR], valueIR])) =
                  .continue
                    { state with
                      storage := Compiler.Proofs.abstractStoreMappingEntry
                        state.storage
                        (Compiler.Proofs.abstractMappingSlot slot key1Nat)
                        key2Nat
                        valueNat } by
                simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs, hIRKey1, hIRKey2, hIRValue,
                  Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
                  Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
                  Compiler.Proofs.abstractStoreMappingEntry_eq])
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp [compiledIR, execIRStmts, hfuelEq, hExecStmt]
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩
        · -- wordOffset ≠ 0: slot expr is add [mappingSlot [mappingSlot [...], ...], lit wordOffset]
          -- Use keccak axiom: nested mappingSlot + wordOffset < evmModulus
          have hbeq : (wordOffset == 0) = false := by
            simp [beq_iff_eq, hzero]
          have hTargetAdd :
              targetSlot =
                (Verity.Core.Uint256.ofNat wordOffset +
                  Verity.Core.Uint256.ofNat
                    (Compiler.Proofs.solidityMappingSlot
                      (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val := by
            simpa [targetSlot] using
              mapping2WordTargetSlot_eq_uint256_add slot key1Nat key2Nat wordOffset
          have hTargetMod :
              (Compiler.Proofs.solidityMappingSlot
                (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat + wordOffset) %
                Compiler.Constants.evmModulus = targetSlot := by
            rw [hTargetAdd]
            simpa [Nat.add_comm] using
              (uint256_add_val_eq_mod wordOffset
                (Compiler.Proofs.solidityMappingSlot
                  (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).symm
          have hStoreEq :
              Compiler.Proofs.abstractStoreStorageOrMapping state.storage targetSlot valueNat =
                fun s =>
                  if s =
                      (Verity.Core.Uint256.ofNat wordOffset +
                        Verity.Core.Uint256.ofNat
                          (Compiler.Proofs.solidityMappingSlot
                            (Compiler.Proofs.solidityMappingSlot slot key1Nat) key2Nat)).val then
                    valueNat
                  else
                    state.storage s := by
            funext s
            rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hTargetAdd]
          have hExecStmt :
              execIRStmt (extraFuel + 1) state
                (YulStmt.expr
                  (YulExpr.call "sstore"
                    [YulExpr.call "add"
                      [YulExpr.call "mappingSlot"
                        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR], key2IR],
                       YulExpr.lit wordOffset], valueIR])) =
                .continue state' := by
              simp [execIRStmt, evalIRExpr, evalIRCall, evalIRExprs,
                hIRKey1, hIRKey2, hIRValue,
                Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackendContext,
                Compiler.Proofs.YulGeneration.evalBuiltinCallWithContext,
                Compiler.Proofs.abstractMappingSlot_eq_solidity,
                state', hTargetMod, hStoreEq]
          have hfuelEq : 1 + extraFuel = extraFuel + 1 := by omega
          have hIRExec : execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
              .continue state' := by
            simp only [compiledIR, hbeq, ite_false]
            simp [execIRStmts, hfuelEq, hExecStmt]
          refine ⟨.continue runtime', .continue state', hSrcExec, hIRExec, ?_⟩
          simp [stmtStepMatchesIRExec]
          exact ⟨runtimeStateMatchesIR_writeAddressKeyedMapping2WordSlot
              hruntime hresolvedNone hdynNone hvalueLt,
            hexact', hbounded, hscope'⟩

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none)
    (hkey1IR : CompilationModel.compileExpr fields .calldata key1 = Except.ok key1IR)
    (hkey2IR : CompilationModel.compileExpr fields .calldata key2 = Except.ok key2IR)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStructMember2 fieldName key1 key2 memberName value)
      [YulStmt.expr
        (YulExpr.call "sstore"
          [let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1IR]
           let mappingSlot2 := YulExpr.call "mappingSlot" [mappingBase, key2IR]
           if wordOffset == 0 then mappingSlot2
           else YulExpr.call "add" [mappingSlot2, YulExpr.lit wordOffset], valueIR])] where
  compileOk := by
    simp only [CompilationModel.compileStmt, CompilationModel.compileSetStructMember2,
      hmapping2, hmembers, hmember, hwriteSlots, hkey1IR, hkey2IR, hvalueIR]
    rfl
  preserves := compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves
    hcoreKey1 hinScopeKey1 hcoreKey2 hinScopeKey2 hcoreValue hinScopeValue
    hmembers hmember hwriteSlots hslotSafety hkey1IR hkey2IR hvalueIR

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
    (hNotMapping : isMapping fields fieldName = false)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.setStorage fieldName value)
      [YulStmt.block
        ([YulStmt.let_ "__compat_value" valueIR] ++
          (slot :: f.aliasSlots).map (fun writeSlot =>
            YulStmt.expr
              (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hNotMapping, hfind, hwriteSlots, halias, hunpacked, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slots := slot :: f.aliasSlots
    let blockBody :=
      [YulStmt.let_ "__compat_value" valueIR] ++
        slots.map (fun writeSlot =>
          YulStmt.expr
            (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
    let compiledIR := [YulStmt.block blockBody]
    have heval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    rcases hIRValue : evalIRExpr state valueIR with _ | valueNat
    · simp [hIRValue, Option.bind] at heval
    · simp [hIRValue, Option.bind] at heval
      have hValueSrc : SourceSemantics.evalExpr fields runtime value = some valueNat :=
        heval.symm
      have hvalueEval : evalIRExpr state valueIR = some valueNat := hIRValue
      -- Prove sizeOf of any YulStmt list ≥ length + 1
      have hSizeOfListBound : ∀ (l : List YulStmt), l.length + 1 ≤ sizeOf l := by
        intro l
        induction l with
        | nil => simp
        | cons h t ih =>
          show t.length + 1 + 1 ≤ 1 + sizeOf h + sizeOf t
          omega
      have hbodyFuelLe : slots.length + 2 ≤ extraFuel := by
        have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
          simpa [compiledIR] using hslack
        have hlen : compiledIR.length = 1 := by simp [compiledIR]
        -- blockBody.length = 1 + slots.length (let_ + map)
        have hBodyLen : blockBody.length = 1 + slots.length := by
          simp [blockBody, slots]; omega
        have hBodyBound := hSizeOfListBound blockBody
        -- sizeOf compiledIR = 1 + sizeOf (YulStmt.block blockBody) + 1
        have hCompSizeOf : sizeOf compiledIR = 1 + sizeOf (YulStmt.block blockBody) + 1 := by
          dsimp only [compiledIR]; rfl
        -- sizeOf (YulStmt.block body) ≥ 1 + sizeOf body
        have hBlockSizeOf : 1 + sizeOf blockBody ≤ sizeOf (YulStmt.block blockBody) := by
          simp [YulStmt.block.sizeOf_spec]
        omega
      let bodyExtraFuel := extraFuel - (slots.length + 2)
      have hbodyFuelEq : slots.length + bodyExtraFuel + 2 = extraFuel := by
        dsimp [bodyExtraFuel]
        omega
      have hresolvedSlots :
          ∀ writeSlot ∈ slots, findResolvedFieldAtSlotCopy fields writeSlot = some f := by
        intro writeSlot hmem
        exact
          findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_member
            hnoConflict hfind hwriteSlots hmem hunpacked
      have hbody :
          execIRStmts extraFuel state blockBody =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                      (state.setVar "__compat_value" valueNat).storage
                      slots
                      valueNat } := by
        have := execIRStmts_let_then_sstore_lit_ident_slots_continue
          bodyExtraFuel state slots "__compat_value" valueIR valueNat hvalueEval
        rw [hbodyFuelEq] at this
        simpa [blockBody, slots] using this
      have hwhole :
          execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                    (state.setVar "__compat_value" valueNat).storage
                    slots
                    valueNat } := by
        have hblock := execIRStmts_single_block_of_continue
          extraFuel state
          { state.setVar "__compat_value" valueNat with
              storage :=
                abstractStoreStorageOrMappingMany
                  (state.setVar "__compat_value" valueNat).storage
                  slots
                  valueNat }
          blockBody
          hbody
        convert hblock using 2
        simp [compiledIR]; omega
      -- Prove value bound
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope
          hcore hexact hinScope hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
          hruntime
      rw [hValueSrc] at hvalueLt
      simp at hvalueLt
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime
          (.setStorage fieldName value) = .continue
            { runtime with
                world := SourceSemantics.writeUintSlots runtime.world (slot :: f.aliasSlots) valueNat } := by
        simp [SourceSemantics.execStmt, hwriteSlots, hValueSrc, slots]
      -- Scope inclusion
      have hincl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.setStorage fieldName value)) scope := by
        intro n hn
        simp [stmtNextScope, collectStmtNames] at hn
        rcases hn with hv | hs
        · exact hinScope n (collectExprNames_mem_exprBoundNames_of_core hcore n hv)
        · exact hs
      have hscope' := FunctionBody.scopeNamesPresent_of_included hscope hincl
      -- Runtime state match
      have hruntimeSet :
          FunctionBody.runtimeStateMatchesIR fields runtime (state.setVar "__compat_value" valueNat) :=
        FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields
          { runtime with world := SourceSemantics.writeUintSlots runtime.world slots valueNat }
          { (state.setVar "__compat_value" valueNat) with
              storage := abstractStoreStorageOrMappingMany
                (state.setVar "__compat_value" valueNat).storage slots valueNat } :=
        runtimeStateMatchesIR_writeUintSlots hruntimeSet hresolvedSlots hnotAddr hnotDyn hvalueLt
      -- Bindings match
      have hexactSet :
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
            (state.setVar "__compat_value" valueNat) :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
          hexact (compatValue_not_mem_scope_of_reservedPrefix hscopeReserved)
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.setStorage fieldName value)) runtime.bindings
          { (state.setVar "__compat_value" valueNat) with
              storage := abstractStoreStorageOrMappingMany
                (state.setVar "__compat_value" valueNat).storage slots valueNat } :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
          (bindingsExactlyMatchIRVarsOnScope_writeUintSlots hexactSet) hincl
      refine ⟨_, _, hSrcExec, hwhole, ?_⟩
      simp [stmtStepMatchesIRExec, slots]
      exact ⟨hruntime', hexact', hbounded, hscope'⟩

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
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR, CompiledStmtStep spec.fields scope (.setStorage fieldName value) compiledIR := by
  by_cases halias : f.aliasSlots = []
  · refine ⟨[YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])], ?_⟩
    apply compiledStmtStep_setStorage_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := ?_)
      (halias := halias)
      (hunpacked := hunpacked)
      (hnoConflict := hnoConflict)
      (hnotAddr := hnotAddr)
      (hnotDyn := hnotDyn)
      (hNotMapping := hNotMapping)
      (hvalueIR := hvalueIR)
    simpa [halias] using hwriteSlots
  · refine
      ⟨[YulStmt.block
          ([YulStmt.let_ "__compat_value" valueIR] ++
            (slot :: f.aliasSlots).map (fun writeSlot =>
              YulStmt.expr
                (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))],
        ?_⟩
    apply compiledStmtStep_setStorage_aliasSlots
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := hwriteSlots)
      (halias := halias)
      (hscopeReserved := scopeAvoidsReservedCompilerPrefix_of_validateIdentifierShapes
        hvalidate hfn hscopeNames)
      (hunpacked := hunpacked)
      (hnoConflict := hnoConflict)
      (hnotAddr := hnotAddr)
      (hnotDyn := hnotDyn)
      (hNotMapping := hNotMapping)
      (hvalueIR := hvalueIR)

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {«prefix» «suffix» : List Stmt}
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
        «prefix»)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes
    (scope := List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
    (hvalidate := hvalidate)
    (hfn := hfn)
    (hscopeNames := ?_)
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hNotMapping := hNotMapping)
    (hvalueIR := hvalueIR)
  intro name hmem
  have hscopeNames := stmtListScopeDiscipline_scope_names hprefix name hmem
  have collectStmtListBindNames_prefix_subset :
      ∀ (a b : List Stmt), ∀ x, x ∈ collectStmtListBindNames a →
        x ∈ collectStmtListBindNames (a ++ b) := by
    intro a b x hx
    induction a with
    | nil => simp [collectStmtListBindNames] at hx
    | cons s rest ih =>
        simp only [collectStmtListBindNames, List.mem_append, List.cons_append] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ih h)
  have collectStmtListAssignedNames_prefix_subset :
      ∀ (a b : List Stmt), ∀ x, x ∈ collectStmtListAssignedNames a →
        x ∈ collectStmtListAssignedNames (a ++ b) := by
    intro a b x hx
    induction a with
    | nil => simp [collectStmtListAssignedNames] at hx
    | cons s rest ih =>
        simp only [collectStmtListAssignedNames, List.mem_append, List.cons_append] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (ih h)
  simp only [List.mem_append] at hscopeNames ⊢
  rcases hscopeNames with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr
      (by rw [hbody]; exact collectStmtListBindNames_prefix_subset _ _ _ h)))
  · exact Or.inl (Or.inr
      (by rw [hbody]; exact collectStmtListAssignedNames_prefix_subset _ _ _ h))
  · exact Or.inr h

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {«prefix» «suffix» : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) «prefix»)
    (hbody : fn.body = «prefix» ++ .setStorage fieldName value :: «suffix»)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hNotMapping : isMapping spec.fields fieldName = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) «prefix»)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    (hvalidate := hvalidateShapes)
    (hfn := hfn)
    (hprefix := stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
      hprefixCore hvalidateRefs hparamScope
      (by simpa [List.append_assoc] using hbody))
    (hbody := hbody)
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hNotMapping := hNotMapping)
    (hvalueIR := hvalueIR)

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
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExec, FunctionBody.stmtResultMatchesIRExec] at hmatch ⊢
  · exact False.elim (hnotContinue _ rfl)
  · exact hmatch
  · exact hmatch

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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcond with ⟨condIR, hcondIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields) (scope := scope) (inScopeNames := scope) (stmts := thenBranch)
      hthen with ⟨thenIR, hthenIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields) (scope := scope) (inScopeNames := scope) (stmts := elseBranch)
      helse with ⟨elseIR, helseIR⟩
  have helseNonempty : elseBranch.isEmpty = false := by
    cases elseBranch with
    | nil => exfalso; exact FunctionBody.stmtListTerminalCore_ne_nil helse rfl
    | cons => simp
  let tempName :=
    CompilationModel.pickFreshName "__ite_cond"
      (scope ++ collectExprNames cond ++
        collectStmtListNames thenBranch ++ collectStmtListNames elseBranch)
  let compiledIR :=
    [YulStmt.block
      [ YulStmt.let_ tempName condIR
      , YulStmt.if_ (YulExpr.ident tempName) thenIR
      , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]]
  refine ⟨compiledIR, ?_⟩
  refine
    { compileOk := ?_
      preserves := ?_ }
  · show CompilationModel.compileStmt fields [] [] .calldata [] false scope
        (.ite cond thenBranch elseBranch) = Except.ok compiledIR
    unfold CompilationModel.compileStmt
    simp only [hcondIR, hthenIR, helseIR, Except.bind, helseNonempty, ↓reduceIte]
    rfl
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hsizeOf_eq : sizeOf compiledIR = 1 + sizeOf (YulStmt.block
        [ YulStmt.let_ tempName condIR
        , YulStmt.if_ (YulExpr.ident tempName) thenIR
        , YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident tempName]) elseIR ]) + 1 := by
      rfl
    have hlength_eq : compiledIR.length = 1 := by rfl
    have hwholeFuel :
        compiledIR.length + extraFuel + 1 =
          sizeOf compiledIR + wholeExtraFuel + 1 := by
      rw [hWF, hsizeOf_eq, hlength_eq]
      have : sizeOf compiledIR - compiledIR.length ≤ extraFuel := hslack
      rw [hsizeOf_eq, hlength_eq] at this
      omega
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    -- Extract the Nat condition value via the eval bridge
    have heval := FunctionBody.eval_compileExpr_core_of_scope
        hcond hexact hinScope hbounded hpresent hruntime
    rw [hcondIR] at heval; simp [Except.toOption] at heval
    rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
    · simp [hCondIRVal, Option.bind] at heval
    · simp [hCondIRVal, Option.bind] at heval
      have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
        heval.symm
      have hcondEval : evalIRExpr state condIR = some condVal := hCondIRVal
      by_cases hcondZero : condVal = 0
      · -- Condition is zero → take else branch
        have hBindIte :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope) (inScopeNames := scope)
            (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch)
            (value := condVal) hexact FunctionBody.scopeNamesIncluded_refl
        have hRuntimeIte :=
          FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
            (name := tempName) (value := condVal) hruntime
        have hElse6 : sizeOf elseIR + 6 ≤ sizeOf compiledIR := by
          change sizeOf elseIR + 6 ≤ sizeOf compiledIR
          simp_wf
          omega
        let branchExtraFuel :=
          sizeOf compiledIR - (sizeOf elseIR + 5) + wholeExtraFuel - 1
        rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
            (fields := fields) (runtime := runtime)
            (state := state.setVar tempName condVal) (scope := scope)
            (inScopeNames := scope) (stmts := elseBranch)
            (extraFuel := branchExtraFuel)
            helse
            FunctionBody.scopeNamesIncluded_refl
            hscope hBindIte hbounded hRuntimeIte with
          ⟨elseIR', helseIR', helseSem⟩
        rw [helseIR] at helseIR'
        have helseEq : elseIR' = elseIR := (Except.ok.inj helseIR').symm
        rw [show elseIR' = elseIR from helseEq] at helseSem
        -- Fuel alignment: convert helseSem fuel to the form _ite_else expects
        have hfuelAlign : sizeOf elseIR + branchExtraFuel + 1 =
            sizeOf elseIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
              (sizeOf elseIR + 5) + wholeExtraFuel) := by
          simp only [List.append_nil, branchExtraFuel]
          have := hElse6
          omega
        have helseSem' :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime elseBranch)
              (execIRStmts (sizeOf elseIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
                  (sizeOf elseIR + 5) + wholeExtraFuel))
                (state.setVar tempName condVal) elseIR) := by
          rw [← hfuelAlign]; exact helseSem
        -- Apply _ite_else to get match for the whole ITE statement list
        have hiteMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime
                [Stmt.ite cond thenBranch elseBranch])
              (execIRStmts (sizeOf compiledIR + wholeExtraFuel + 1)
                state compiledIR) := by
          have := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
              (fields := fields) (runtime := runtime) (state := state)
              (scope := scope) (cond := cond)
              (thenBranch := thenBranch) (elseBranch := elseBranch) (rest := [])
              (extraFuel := wholeExtraFuel) (tempName := tempName)
              (condIR := condIR) (thenIR := thenIR) (elseIR := elseIR)
              (tailIR := []) (condValue := condVal)
              (sourceCondValue := condVal)
              helse helseSem' hCondSrc
              (by simp [hcondZero])
              hcondEval hcondZero rfl
          simp only [List.append_nil] at this
          exact this
        -- execStmt (.ite ...) = execStmtList elseBranch (by source semantics)
        have hexecStmtElse : SourceSemantics.execStmt fields runtime
            (Stmt.ite cond thenBranch elseBranch) =
            SourceSemantics.execStmtList fields runtime elseBranch := by
          simp [SourceSemantics.execStmt, hCondSrc, hcondZero]
        -- execStmtList [.ite ...] = execStmtList elseBranch (by terminal_ite_else_eq)
        have hsourceEq :=
          FunctionBody.execStmtList_terminal_core_ite_else_eq
            (fields := fields) (runtime := runtime) (scope := scope)
            (cond := cond) (thenBranch := thenBranch)
            (elseBranch := elseBranch) (rest := [])
            (condValue := condVal) helse hCondSrc
            (by simp [hcondZero])
        -- Rewrite hiteMatch source from execStmtList [.ite ...] to execStmtList elseBranch
        rw [hsourceEq] at hiteMatch
        -- Now hiteMatch : stmtResultMatchesIRExec fields
        --   (execStmtList fields runtime elseBranch) (execIRStmts ... state compiledIR)
        -- Convert to stmtResultMatchesIRExec about execStmt
        have hbodyMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmt fields runtime
                (Stmt.ite cond thenBranch elseBranch))
              (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
          rw [hexecStmtElse, hwholeFuel]; exact hiteMatch
        refine ⟨_, _, rfl, rfl, ?_⟩
        exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
            hbodyMatch
            (by rw [hexecStmtElse]
                exact FunctionBody.execStmtList_terminal_core_not_continue
                  (fields := fields) (runtime := runtime) (scope := scope)
                  (stmts := elseBranch) helse)
      · -- Condition is nonzero → take then branch
        have hBindIte :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope) (inScopeNames := scope)
            (cond := cond) (thenBranch := thenBranch) (elseBranch := elseBranch)
            (value := condVal) hexact FunctionBody.scopeNamesIncluded_refl
        have hRuntimeIte :=
          FunctionBody.runtimeStateMatchesIR_setVar_irrelevant
            (name := tempName) (value := condVal) hruntime
        have hThen5 : sizeOf thenIR + 5 ≤ sizeOf compiledIR := by
          change sizeOf thenIR + 5 ≤ sizeOf compiledIR
          simp_wf
          omega
        let branchExtraFuel :=
          sizeOf compiledIR - (sizeOf thenIR + 5) + wholeExtraFuel
        rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
            (fields := fields) (runtime := runtime)
            (state := state.setVar tempName condVal) (scope := scope)
            (inScopeNames := scope) (stmts := thenBranch)
            (extraFuel := branchExtraFuel)
            hthen
            FunctionBody.scopeNamesIncluded_refl
            hscope hBindIte hbounded hRuntimeIte with
          ⟨thenIR', hthenIR', hthenSem⟩
        rw [hthenIR] at hthenIR'
        have hthenEq : thenIR' = thenIR := (Except.ok.inj hthenIR').symm
        rw [show thenIR' = thenIR from hthenEq] at hthenSem
        -- Fuel alignment for then branch (has +1 on both sides, so direct)
        have hthenSem' :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime thenBranch)
              (execIRStmts (sizeOf thenIR + (sizeOf (compiledIR ++ ([] : List YulStmt)) -
                  (sizeOf thenIR + 5) + wholeExtraFuel) + 1)
                (state.setVar tempName condVal) thenIR) := by
          simp only [List.append_nil, branchExtraFuel] at hthenSem ⊢
          exact hthenSem
        -- Apply _ite_then to get match for the whole ITE statement list
        have hiteMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmtList fields runtime
                [Stmt.ite cond thenBranch elseBranch])
              (execIRStmts (sizeOf compiledIR + wholeExtraFuel + 1)
                state compiledIR) := by
          have := FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
              (fields := fields) (runtime := runtime) (state := state)
              (scope := scope) (cond := cond)
              (thenBranch := thenBranch) (elseBranch := elseBranch) (rest := [])
              (extraFuel := wholeExtraFuel) (tempName := tempName)
              (condIR := condIR) (thenIR := thenIR) (elseIR := elseIR)
              (tailIR := []) (condValue := condVal)
              (sourceCondValue := condVal)
              hthen hthenSem' hCondSrc
              (by simp [hcondZero])
              hcondEval
              (by intro hzero; exact hcondZero hzero) rfl
          simp only [List.append_nil] at this
          exact this
        -- execStmt (.ite ...) = execStmtList thenBranch (by source semantics)
        have hexecStmtThen : SourceSemantics.execStmt fields runtime
            (Stmt.ite cond thenBranch elseBranch) =
            SourceSemantics.execStmtList fields runtime thenBranch := by
          simp [SourceSemantics.execStmt, hCondSrc, hcondZero]
        -- execStmtList [.ite ...] = execStmtList thenBranch
        have hsourceEq :=
          FunctionBody.execStmtList_terminal_core_ite_then_eq
            (fields := fields) (runtime := runtime) (scope := scope)
            (cond := cond) (thenBranch := thenBranch)
            (elseBranch := elseBranch) (rest := [])
            (condValue := condVal) hthen hCondSrc
            (by simp [hcondZero])
        rw [hsourceEq] at hiteMatch
        have hbodyMatch :
            FunctionBody.stmtResultMatchesIRExec fields
              (SourceSemantics.execStmt fields runtime
                (Stmt.ite cond thenBranch elseBranch))
              (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
          rw [hexecStmtThen, hwholeFuel]; exact hiteMatch
        refine ⟨_, _, rfl, rfl, ?_⟩
        exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
            hbodyMatch
            (by rw [hexecStmtThen]
                exact FunctionBody.execStmtList_terminal_core_not_continue
                  (fields := fields) (runtime := runtime) (scope := scope)
                  (stmts := thenBranch) hthen)
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

private theorem stmtListTouchesUnsupportedContractSurface_append
    {«prefix» «suffix» : List Stmt} :
    stmtListTouchesUnsupportedContractSurface («prefix» ++ «suffix») =
      (stmtListTouchesUnsupportedContractSurface «prefix» ||
        stmtListTouchesUnsupportedContractSurface «suffix») := by
  induction «prefix» with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface, ih, Bool.or_assoc]

private theorem stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_append
    {«prefix» «suffix» : List Stmt} :
    stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites («prefix» ++ «suffix») =
      (stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «prefix» ||
        stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «suffix») := by
  induction «prefix» with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites, ih, Bool.or_assoc]

private theorem stmtListCompileCore_of_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    FunctionBody.StmtListCompileCore scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) := by
  induction clauses generalizing scope with
  | nil =>
      simpa using FunctionBody.StmtListCompileCore.nil (scope := scope)
  | cons clause rest ih =>
      refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ ih
      · cases clause with
        | mk family n m p q message =>
            cases family with
            | binary guard =>
                cases guard <;> repeat constructor
            | andEqLt =>
                exact .logicalAnd (.eq (.literal n) (.literal m)) (.lt (.literal p) (.literal q))
            | orEqLt =>
                exact .logicalOr (.eq (.literal n) (.literal m)) (.lt (.literal p) (.literal q))
      · intro name hmem
        cases clause with
        | mk family n m p q message =>
            cases family with
            | binary guard =>
                cases guard <;> simp [FunctionBody.exprBoundNames] at hmem
            | andEqLt =>
                simp [FunctionBody.exprBoundNames] at hmem
            | orEqLt =>
                simp [FunctionBody.exprBoundNames] at hmem

private theorem foldl_stmtNextScope_requireLiteralGuardFamilyClauses
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    List.foldl stmtNextScope scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) = scope := by
  induction clauses generalizing scope with
  | nil =>
      rfl
  | cons clause rest ih =>
      cases clause with
      | mk family n m p q message =>
          cases family with
          | binary guard =>
              cases guard <;>
                simp [stmtNextScope, Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
                  collectStmtNames, collectExprNames, ih]
          | andEqLt =>
              simp [stmtNextScope, Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
                collectStmtNames, collectExprNames, ih]
          | orEqLt =>
              simp [stmtNextScope, Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
                collectStmtNames, collectExprNames, ih]

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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStorage_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind)
      (halias := by rfl)
      (hunpacked := by rfl)
      (hnoConflict := hnoConflict)
      (hnotAddr := by rfl)
      (hnotDyn := by rfl)
      (hNotMapping := isMapping_false_of_findFieldWithResolvedSlot_uint256 hfind rfl)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStorageAddr_singleSlot
      (hcore := hcore)
      (hinScope := hinScope)
      (hfind := hfind)
      (hwriteSlots := by simpa using findFieldWriteSlots_of_findFieldWithResolvedSlot hfind)
      (hnoConflict := hnoConflict)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_mstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.mstore offset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
    ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_mstore_single
      (hcoreOffset := hcoreOffset)
      (hinScopeOffset := hinScopeOffset)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hoffsetIR := hoffsetIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

private theorem stmtListGenericCore_singleton_tstore_single
    {fields : List Field}
    {scope : List String}
    {offset value : Expr}
    (hcoreOffset : FunctionBody.ExprCompileCore offset)
    (hinScopeOffset : FunctionBody.exprBoundNamesInScope offset scope)
    (hcoreValue : FunctionBody.ExprCompileCore value)
    (hinScopeValue : FunctionBody.exprBoundNamesInScope value scope) :
    StmtListGenericCore fields scope [Stmt.tstore offset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreOffset with
    ⟨offsetIR, hoffsetIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_tstore_single
      (hcoreOffset := hcoreOffset)
      (hinScopeOffset := hinScopeOffset)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hoffsetIR := hoffsetIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
    StmtListGenericCore fields scope [Stmt.setMappingUint fieldName key value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingUint_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
  rcases compileExprList_core_ok (fields := fields) hcoreKeys with ⟨keyIRs, hkeyIRs⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingChain_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKeys := hcoreKeys)
      (hinScopeKeys := hinScopeKeys)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIRs := hkeyIRs)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingWord fieldName key wordOffset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingWord_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMappingPackedWord fieldName key wordOffset packed value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hcompatValue := hcompatValue)
      (hcompatPacked := hcompatPacked)
      (hcompatSlotWord := hcompatSlotWord)
      (hcompatSlotCleared := hcompatSlotCleared)
      (hpacked := hpacked)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
    (hnotMapping2 : isMapping2 fields fieldName = false)
    (hmembers : findStructMembers fields fieldName = some members)
    (hmember :
      findStructMember members memberName =
        some { name := memberName, wordOffset := wordOffset, packed := none })
    (hwriteSlots : findFieldWriteSlots fields fieldName = some [slot])
    (hslotSafety :
      ∀ runtime keyNat,
        SourceSemantics.evalExpr fields runtime key = some keyNat →
          findResolvedFieldAtSlotCopy fields
            (mappingWordTargetSlot slot keyNat wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mappingWordTargetSlot slot keyNat wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember fieldName key memberName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey with
    ⟨keyIR, hkeyIR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStructMember_singleSlot_of_slotSafety
      (hmapping := hmapping)
      (hnotMapping2 := hnotMapping2)
      (hcoreKey := hcoreKey)
      (hinScopeKey := hinScopeKey)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hmembers := hmembers)
      (hmember := hmember)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkeyIR := hkeyIR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping2_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setMapping2Word fieldName key1 key2 wordOffset value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none ∧
          findDynamicArrayElementAtSlotCopy fields runtime.world
            (mapping2WordTargetSlot slot keyNat1 keyNat2 wordOffset) = none) :
    StmtListGenericCore fields scope [Stmt.setStructMember2 fieldName key1 key2 memberName value] := by
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey1 with
    ⟨key1IR, hkey1IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreKey2 with
    ⟨key2IR, hkey2IR⟩
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcoreValue with
    ⟨valueIR, hvalueIR⟩
  exact StmtListGenericCore.cons
    (compiledStmtStep_setStructMember2_singleSlot_of_slotSafety
      (hmapping2 := hmapping2)
      (hcoreKey1 := hcoreKey1)
      (hinScopeKey1 := hinScopeKey1)
      (hcoreKey2 := hcoreKey2)
      (hinScopeKey2 := hinScopeKey2)
      (hcoreValue := hcoreValue)
      (hinScopeValue := hinScopeValue)
      (hmembers := hmembers)
      (hmember := hmember)
      (hwriteSlots := hwriteSlots)
      (hslotSafety := hslotSafety)
      (hkey1IR := hkey1IR)
      (hkey2IR := hkey2IR)
      (hvalueIR := hvalueIR))
    StmtListGenericCore.nil

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


private theorem exprBoundNamesInScope_of_scopeNamesIncluded
    {expr : Expr}
    {scope largerScope : List String}
    (hinScope : FunctionBody.exprBoundNamesInScope expr scope)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.exprBoundNamesInScope expr largerScope := by
  intro name hname
  exact hincluded name (hinScope name hname)

private theorem scopeNamesIncluded_cons
    {name : String} {scope largerScope : List String}
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.scopeNamesIncluded (name :: scope) (name :: largerScope) := by
  intro n hn
  simp at hn ⊢
  rcases hn with rfl | hn
  · exact Or.inl rfl
  · exact Or.inr (hincluded n hn)

private theorem stmtListCompileCore_of_scopeNamesIncluded
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.StmtListCompileCore largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil => exact .nil
  | letVar hvalue hinScope hrest ih =>
      exact .letVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | assignVar hvalue hinScope hrest ih =>
      exact .assignVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | require_ hcond hinScope hrest ih =>
      exact .require_ hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | return_ hvalue hinScope hrest ih =>
      exact .return_ hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | stop hrest ih =>
      exact .stop (ih hincluded)

private theorem stmtListTerminalCore_of_scopeNamesIncluded
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    FunctionBody.StmtListTerminalCore largerScope stmts := by
  induction hterminal generalizing largerScope with
  | letVar hvalue hinScope hrest ih =>
      exact .letVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | assignVar hvalue hinScope hrest ih =>
      exact .assignVar hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih <| scopeNamesIncluded_cons hincluded)
  | require_ hcond hinScope hrest ih =>
      exact .require_ hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ih hincluded)
  | return_ hvalue hinScope hrest =>
      exact .return_ hvalue
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)
  | stop hrest =>
      exact .stop (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      exact .ite hcond
        (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
        (ihThen hincluded)
        (ihElse hincluded)
        (stmtListCompileCore_of_scopeNamesIncluded hrest hincluded)

private theorem stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil => exact StmtListGenericCore.nil
  | letVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_letVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
  | assignVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_assignVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
  | require_ hcond hinScope hrest ih =>
      rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
        ⟨failCond, hfailCond⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_require
          (hcore := hcond)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hfailCompile := hfailCond))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
          (stmt := .require _ _) hincluded)
  | return_ hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_return
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .return _) hincluded)
  | stop hrest ih =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .stop) hincluded)

private theorem stmtListGenericCore_of_stmtListTerminalCore_of_scopeNamesIncluded
    {fields : List Field}
    {scope largerScope : List String}
    {stmts : List Stmt}
    (hterminal : FunctionBody.StmtListTerminalCore scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    StmtListGenericCore fields largerScope stmts := by
  induction hterminal generalizing largerScope with
  | letVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_letVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_letVar hincluded)
  | assignVar hvalue hinScope hrest ih =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_assignVar
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_assignVar hincluded)
  | require_ hcond hinScope hrest ih =>
      rcases FunctionBody.compileRequireFailCond_core_ok (fields := fields) hcond with
        ⟨failCond, hfailCond⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_require
          (hcore := hcond)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hfailCompile := hfailCond))
        (ih <| FunctionBody.scopeNamesIncluded_collectStmtNames_tail
          (stmt := .require _ _) hincluded)
  | return_ hvalue hinScope hrest =>
      rcases FunctionBody.compileExpr_core_ok (fields := fields) hvalue with
        ⟨valueIR, hvalueIR⟩
      exact StmtListGenericCore.cons
        (compiledStmtStep_return
          (hcore := hvalue)
          (hinScope := exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (hvalueIR := hvalueIR))
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .return _) hincluded))
  | stop hrest =>
      exact StmtListGenericCore.cons compiledStmtStep_stop
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .stop) hincluded))
  | ite hcond hinScope hthen helse hrest ihThen ihElse =>
      rcases compiledStmtStep_ite (fields := fields) hcond
          (exprBoundNamesInScope_of_scopeNamesIncluded hinScope hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded hthen hincluded)
          (stmtListTerminalCore_of_scopeNamesIncluded helse hincluded) with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .ite _ _ _) hincluded))
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

private theorem stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
    {fields : List Field}
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope [clause.toStmt] := by
  cases clause with
  | mk family n m p q message =>
      cases family with
      | binary op =>
          cases op
          case eq =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case notEq =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case lt =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case gt =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case ge =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
          case le =>
            simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
              (show StmtListGenericCore fields scope
                [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
      | andEqLt =>
          simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
            (show StmtListGenericCore fields scope
              [Stmt.require
                (Expr.logicalAnd (Expr.eq (Expr.literal n) (Expr.literal m))
                  (Expr.lt (Expr.literal p) (Expr.literal q)))
                message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require
                        (Expr.logicalAnd (Expr.eq (Expr.literal n) (Expr.literal m))
                          (Expr.lt (Expr.literal p) (Expr.literal q)))
                        message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)
      | orEqLt =>
          simpa [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt] using
            (show StmtListGenericCore fields scope
              [Stmt.require
                (Expr.logicalOr (Expr.eq (Expr.literal n) (Expr.literal m))
                  (Expr.lt (Expr.literal p) (Expr.literal q)))
                message] from by
                  have hcore : FunctionBody.StmtListCompileCore scope
                      [Stmt.require
                        (Expr.logicalOr (Expr.eq (Expr.literal n) (Expr.literal m))
                          (Expr.lt (Expr.literal p) (Expr.literal q)))
                        message] := by
                    refine FunctionBody.StmtListCompileCore.require_ ?_ ?_ FunctionBody.StmtListCompileCore.nil
                    · repeat constructor
                    · intro name hmem
                      simp [FunctionBody.exprBoundNames] at hmem
                  exact stmtListGenericCore_of_stmtListCompileCore hcore)

theorem stmtListGenericCore_append
    {fields : List Field}
    {scope : List String}
    {«prefix» «suffix» : List Stmt}
    (hprefix : StmtListGenericCore fields scope «prefix»)
    (hsuffix :
      StmtListGenericCore
        fields
        (List.foldl stmtNextScope scope «prefix»)
        «suffix») :
    StmtListGenericCore fields scope («prefix» ++ «suffix») := by
  induction hprefix generalizing «suffix» with
  | nil =>
      simpa using hsuffix
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp
      exact StmtListGenericCore.cons hstep (ih hsuffix)

private theorem stmtNextScope_requireLiteralGuardFamilyClause
    {scope : List String}
    (clause : Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    stmtNextScope scope clause.toStmt = scope := by
  cases clause with
  | mk family n m p q message =>
      cases family with
      | binary guard =>
          cases guard <;>
            simp [stmtNextScope,
              Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
              collectStmtNames, collectExprNames]
      | andEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtNames, collectExprNames]
      | orEqLt =>
          simp [stmtNextScope,
            Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
            collectStmtNames, collectExprNames]

private theorem stmtListGenericCore_of_supportedStmtList_append_of_surface_exceptMappingWrites
    {fields : List Field}
    {scope : List String}
    {«prefix» «suffix» : List Stmt}
    (_hprefix : SupportedStmtList fields scope «prefix»)
    (_hsuffix : SupportedStmtList fields (List.foldl stmtNextScope scope «prefix») «suffix»)
    (ihPrefix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «prefix» = false →
        StmtListGenericCore fields scope «prefix»)
    (ihSuffix :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites «suffix» = false →
        StmtListGenericCore fields (List.foldl stmtNextScope scope «prefix») «suffix»)
    (hsurface :
      stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites («prefix» ++ «suffix») = false) :
    StmtListGenericCore fields scope («prefix» ++ «suffix») := by
  rw [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites_append] at hsurface
  exact stmtListGenericCore_append
    (ihPrefix (Bool.or_eq_false_iff.mp hsurface).1)
    (ihSuffix (Bool.or_eq_false_iff.mp hsurface).2)

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
  simp only [stmtListTouchesUnsupportedContractSurfaceExceptMappingWrites,
    Bool.or_eq_false_iff] at hsurface
  apply stmtListGenericCore_append
    (stmtListGenericCore_singleton_requireLiteralGuardFamilyClause
      (fields := fields) (scope := scope) clause)
  simp only [List.foldl, stmtNextScope_requireLiteralGuardFamilyClause clause]
  exact ihRest hsurface.2

theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported with
  | compileCore hcore =>
      exact stmtListGenericCore_of_stmtListCompileCore hcore
  | terminalCore hterminal =>
      exact stmtListGenericCore_of_stmtListTerminalCore hterminal
  | setStorageSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | setStorageAddrSingleSlot hcore hinScope hfind =>
      exact stmtListGenericCore_of_supportedStmtList_setStorageAddrSingleSlot_of_surface
        (fields := fields) hnoConflict hfind hcore hinScope
  | mstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_mstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | tstoreSingle hcoreOffset hinScopeOffset hcoreValue hinScopeValue =>
      exact stmtListGenericCore_of_supportedStmtList_tstoreSingle_of_surface
        (fields := fields) hcoreOffset hinScopeOffset hcoreValue hinScopeValue
  | letStorageField hfind =>
      exact False.elim (false_of_supportedStmtList_letStorageField_surface hsurface)
  | returnMapping hkey hscope hslot =>
      exact False.elim (false_of_supportedStmtList_returnMapping_surface hsurface)
  | letMapping hkey hscope hslot =>
      exact False.elim (false_of_supportedStmtList_letMapping_surface hsurface)
  | letMapping2 hkey1 hscope1 hkey2 hscope2 hslot =>
      exact False.elim (false_of_supportedStmtList_letMapping2_surface hsurface)
  | letMappingUint hkey hscope hslot =>
      exact False.elim (false_of_supportedStmtList_letMappingUint_surface hsurface)
  | setMappingUintSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingUintSingle_surface hsurface)
  | setMappingChainSingle hkeys hscopeKeys hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingChainSingle_surface hsurface)
  | setMappingSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingSingle_surface hsurface)
  | setMappingWordSingle hkey hscopeKey hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingWordSingle_surface hsurface)
  | setMappingPackedWordSingle hkey hscopeKey hvalue hscopeValue
      hcompatValue hcompatPacked hcompatSlotWord hcompatSlotCleared hpacked hslot =>
      exact False.elim (false_of_supportedStmtList_setMappingPackedWordSingle_surface hsurface)
  | setStructMemberSingle hkey hscopeKey hvalue hscopeValue hslot hmembers hmember =>
      exact False.elim (false_of_supportedStmtList_setStructMemberSingle_surface hsurface)
  | setMapping2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMapping2Single_surface hsurface)
  | setMapping2WordSingle hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot =>
      exact False.elim (false_of_supportedStmtList_setMapping2WordSingle_surface hsurface)
  | setStructMember2Single hkey1 hscope1 hkey2 hscope2 hvalue hscopeValue hslot hmembers hmember =>
      exact False.elim (false_of_supportedStmtList_setStructMember2Single_surface hsurface)
  | rawLogLiterals htopics =>
      exact False.elim (false_of_supportedStmtList_rawLogLiterals_surface hsurface)
  | letCallerLetStorageReqEqReqNeqSetStorageParamStop hOwner hne_sv_p hne_ov_p hne_ov_sv =>
      exact False.elim
        (false_of_supportedStmtList_letCallerLetStorageReqEqReqNeqSetStorageParamStop_surface
          hsurface)
  | letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop
      hOwner hTarget hne_sv_p hne_ov_p hne_ov_sv hne_tv_p hne_tv_sv hne_tv_ov =>
      exact False.elim
        (false_of_supportedStmtList_letCallerLetStorageReqEqLetStorageReqNeqSetStorageParamStop_surface
          hsurface)
  | requireClause clause _ ih =>
      simp [stmtListTouchesUnsupportedContractSurface] at hsurface
      apply stmtListGenericCore_append
        (stmtListGenericCore_singleton_requireLiteralGuardFamilyClause clause)
      simp only [List.foldl, stmtNextScope_requireLiteralGuardFamilyClause clause]
      exact ih hsurface.2
  | ite _ _ _ _ _ _ =>
      exact False.elim (false_of_supportedStmtList_ite_list_surface hsurface)
  | append _ _ ihPrefix ihSuffix =>
      simp only [stmtListTouchesUnsupportedContractSurface_append, Bool.or_eq_false_iff] at hsurface
      exact stmtListGenericCore_append (ihPrefix hsurface.1) (ihSuffix hsurface.2)

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

theorem SupportedBodyInterface.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body := by
  have hsurface :
      stmtListTouchesUnsupportedContractSurface fn.body = false :=
    stmtListTouchesUnsupportedContractSurface_eq_false_of_featureClosed fn.body
      hBody.core.surfaceClosed
      hBody.state.surfaceClosed
      (SupportedBodyCallInterface.surfaceClosed (hBody := hBody))
      hBody.effects.surfaceClosed
  exact stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
    (fields := spec.fields)
    (scope := fn.params.map (·.name))
    (stmts := fn.body)
    hnoConflict
    hBody.stmtList
    hsurface

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


private theorem scopeNamesIncluded_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt} :
    FunctionBody.scopeNamesIncluded scope (List.foldl stmtNextScope scope stmts) := by
  induction stmts generalizing scope with
  | nil =>
      simpa using FunctionBody.scopeNamesIncluded_refl
  | cons stmt rest ih =>
      intro name hname
      exact ih (scope := stmtNextScope scope stmt) name (mem_stmtNextScope_of_mem_scope hname)

private theorem stmtListGenericCore_of_requireClausesOnly
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) :=
  stmtListGenericCore_of_stmtListCompileCore
    (stmtListCompileCore_of_requireLiteralGuardFamilyClauses clauses)

private theorem stmtListGenericCore_of_requireClausesThenReturnLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.return (Expr.literal retVal)]) := by
  have htail :
      FunctionBody.StmtListCompileCore scope [Stmt.return (Expr.literal retVal)] := by
    refine FunctionBody.StmtListCompileCore.return_ (.literal retVal) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

private theorem stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause)
    (tmp : String)
    (retVal : Nat) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt ++
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)]) := by
  have htail :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal retVal) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · refine FunctionBody.StmtListCompileCore.return_ (.localVar tmp) ?_ ?_
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem
        simpa [hmem]
      · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

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
        [Stmt.setStorage fieldName (Expr.literal writeVal)]) :=
  stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_singleton_setStorage_singleSlot
          (fields := fields)
          (scope := scope)
          (hnoConflict := hnoConflict)
          (hfind := hfind)
          (hcore := .literal writeVal)
          (hinScope := by intro name hmem; simp [FunctionBody.exprBoundNames] at hmem)))

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
  have hprefix :
      FunctionBody.StmtListCompileCore scope [Stmt.letVar tmp (Expr.literal n)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope [Stmt.letVar tmp (Expr.literal n)])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

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
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · refine FunctionBody.StmtListCompileCore.assignVar (.literal m) ?_ ?_
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem
      · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n), Stmt.assignVar tmp (Expr.literal m)])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

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
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.add (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

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
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.sub (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

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
  have hprefix :
      FunctionBody.StmtListCompileCore scope
        [Stmt.letVar tmp (Expr.literal n),
         Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))] := by
    refine FunctionBody.StmtListCompileCore.letVar (.literal n) ?_ ?_
    · intro name hmem
      simp [FunctionBody.exprBoundNames] at hmem
    · exact FunctionBody.StmtListCompileCore.assignVar
        (FunctionBody.ExprCompileCore.mul (.localVar tmp) (.literal m))
        (by intro name hmem
            simp [FunctionBody.exprBoundNames] at hmem ⊢
            exact Or.inl hmem)
        FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_append
          (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) hprefix)
          (stmtListGenericCore_singleton_setStorage_singleSlot
            (fields := fields)
            (scope := List.foldl stmtNextScope scope
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              exact Or.inl hmem))))

theorem compileStmtList_ok_of_stmtListGenericCore
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames stmts = Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead htail⟩

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
  induction hgeneric generalizing inScopeNames with
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead htail⟩

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
  induction hgeneric generalizing inScopeNames with
  | nil => exact ⟨[], rfl⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
          (by intro name hmem
              simp [stmtNextScope] at hmem
              rcases hmem with h | h
              · exact List.mem_append_left _ h
              · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead htail⟩

theorem stmtStepMatchesIRExec_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
  rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
  exact ⟨hruntime,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
    hbounded,
    FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩
  · exact hmatch
  · exact hmatch

theorem stmtStepMatchesIRExecWithInternals_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResultWithInternals}
    (hmatch : stmtStepMatchesIRExecWithInternals fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExecWithInternals fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExecWithInternals] at hmatch ⊢
  rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
  exact ⟨hruntime,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
    hbounded,
    FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩
  · exact hmatch
  · exact hmatch

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
    stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;>
    simp [stmtStepMatchesIRExecWithInternals, stmtResultMatchesIRExecWithInternals,
      FunctionBody.stmtResultMatchesIRExec] at hmatch ⊢ <;>
    try exact hmatch
  · exact hmatch.1

private theorem yulStmtList_length_add_sizeOf_le_append
    (head tail : List YulStmt) :
    head.length + sizeOf tail ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil => simp
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega

private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil =>
      cases tail <;> simp <;> omega
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega
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
      execIRStmts (fuel - head.length) next tail := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmts] at hhead
      cases hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmts] using hhead
      | succ fuel =>
          match hstmt : execIRStmt fuel state stmt with
          | .continue next' =>
              simp [execIRStmts, hstmt] at hhead ⊢
              simpa using ih fuel next' hhead
          | .return value state' =>
              simp [execIRStmts, hstmt] at hhead
          | .stop state' =>
              simp [execIRStmts, hstmt] at hhead
          | .revert state' =>
              simp [execIRStmts, hstmt] at hhead

private theorem execIRStmts_append_of_not_continue
    (fuel : Nat)
    (state : IRState)
    (head tail : List YulStmt)
    (irExec : IRExecResult)
    (hhead : execIRStmts fuel state head = irExec)
    (hnot : ∀ next, irExec ≠ .continue next) :
    execIRStmts fuel state (head ++ tail) = irExec := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmts] at hhead
      cases hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmts] using hhead
      | succ fuel =>
          match hstmt : execIRStmt fuel state stmt with
          | .continue next' =>
              simp [execIRStmts, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmts, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmts, hstmt] using hhead

private theorem execIRStmtsWithInternals_append_of_continue
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state next : IRState)
    (head tail : List YulStmt)
    (hhead :
      execIRStmtsWithInternals runtimeContract fuel state head = .continue next) :
    execIRStmtsWithInternals runtimeContract fuel state (head ++ tail) =
      execIRStmtsWithInternals runtimeContract (fuel - head.length) next tail := by
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmtsWithInternals] at hhead
      cases hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmtsWithInternals] using hhead
      | succ fuel =>
          match hstmt : execIRStmtWithInternals runtimeContract fuel state stmt with
          | .continue next' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead ⊢
              simpa using ih fuel next' hhead
          | .return value state' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead
          | .stop state' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead
          | .revert state' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead
          | .leave state' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead

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
  induction head generalizing fuel state with
  | nil =>
      simp [execIRStmtsWithInternals] at hhead
      cases hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simpa [execIRStmtsWithInternals] using hhead
      | succ fuel =>
          match hstmt : execIRStmtWithInternals runtimeContract fuel state stmt with
          | .continue next' =>
              simp [execIRStmtsWithInternals, hstmt] at hhead ⊢
              exact ih fuel next' hhead
          | .return value state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .stop state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .revert state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead
          | .leave state' =>
              simpa [execIRStmtsWithInternals, hstmt] using hhead

theorem exec_compileStmtList_generic_sizeOf_extraFuel_step
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericCore hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false scope (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state headExtraFuel
          hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
          have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
          dsimp [bodyIR]; omega
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec'
          rw [hrw]
          congr 1
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtList fields runtime (stmt :: rest) =
            SourceSemantics.execStmtList fields ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtList, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .stop ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .return ‹Nat› ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .revert ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtList, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExec]

theorem exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExec
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmts, stmtStepMatchesIRExec]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpers hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false scope (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state helperFuel headExtraFuel
          hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
          have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
          dsimp [bodyIR]; omega
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec'
          rw [hrw]
          congr 1
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
            SourceSemantics.execStmtListWithHelpers spec fields helperFuel
              ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .stop ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .return ‹Nat› ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              .revert ‹IRState› := by
          exact execIRStmts_append_of_not_continue
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExec]

-- (Old sorry'd proof body removed - proof now uses scope directly)

theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtStepMatchesIRExecWithInternals
        fields
        (List.foldl stmtNextScope scope stmts)
        sourceResult
        irExec := by
  induction hgeneric generalizing runtime state extraFuel with
  | nil =>
      refine ⟨[], ?_, ?_⟩
      · simp [CompilationModel.compileStmtList, pure, Except.pure]
      · simp [SourceSemantics.execStmtListWithHelpers, execIRStmtsWithInternals,
              stmtStepMatchesIRExecWithInternals]
        exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR hrest
          FunctionBody.scopeNamesIncluded_refl with ⟨tailIR, htailCompile⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false scope (stmt :: rest) =
              Except.ok bodyIR := by
        exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
          hstep.compileOk htailCompile
      let headExtraFuel := sizeOf bodyIR - compiledIR.length + extraFuel
      have hheadSlack :
          sizeOf compiledIR - compiledIR.length ≤ headExtraFuel := by
        have hsize : sizeOf compiledIR ≤ sizeOf bodyIR := by
          simpa [bodyIR] using yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [headExtraFuel]
        omega
      rcases hstep.preserves runtime state helperFuel headExtraFuel
          hfuelPos hexact hscope hbounded hruntime hheadSlack with
        ⟨sourceHead, irHead, hsourceHead, hheadExec, hheadMatch⟩
      refine ⟨bodyIR, hbodyCompile, ?_⟩
      have hlength_le_sizeOf : compiledIR.length ≤ sizeOf compiledIR := by
        have := yulStmtList_length_add_sizeOf_le_append compiledIR []
        simp at this; omega
      have hle : compiledIR.length ≤ sizeOf bodyIR := by
        have := yulStmtList_sizeOf_append_left_le compiledIR tailIR
        dsimp [bodyIR]; omega
      have hfuelEq : compiledIR.length + headExtraFuel + 1 = sizeOf bodyIR + extraFuel + 1 := by
        dsimp [headExtraFuel]; omega
      cases sourceHead <;> cases irHead <;>
        simp [stmtStepMatchesIRExecWithInternals] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (extraFuel := tailExtraFuel')
            hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .continue ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmtsWithInternals runtimeContract
                (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          have hrw := execIRStmtsWithInternals_append_of_continue
              runtimeContract
              (sizeOf bodyIR + extraFuel + 1)
              state
              ‹IRState›
              compiledIR
              tailIR
              hheadExec'
          rw [hrw]
          congr 1
          have hlenTail : compiledIR.length + sizeOf tailIR ≤ sizeOf bodyIR := by
            have := yulStmtList_length_add_sizeOf_le_append compiledIR tailIR
            dsimp [bodyIR]; omega
          dsimp [tailExtraFuel']
          omega
        rw [show SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime (stmt :: rest) =
            SourceSemantics.execStmtListWithHelpers spec fields helperFuel
              ‹SourceSemantics.RuntimeState› rest by
              simp [SourceSemantics.execStmtListWithHelpers, hsourceHead]]
        rw [hfullExec]
        simpa [tailExtraFuel', bodyIR, List.foldl] using htailSem''
      ·
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .stop ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .stop ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.stop ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simpa [List.foldl] using hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime'⟩
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .return ‹Nat› ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .return ‹Nat› ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.return ‹Nat› ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        exact ⟨rfl, hruntime'⟩
      ·
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .revert ‹IRState› := by
          rw [← hfuelEq]; exact hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .revert ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            runtimeContract
            (sizeOf bodyIR + extraFuel + 1)
            state
            compiledIR
            tailIR
            (.revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExecWithInternals]

theorem exec_compileStmtList_generic_sizeOf_extraFuel
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (extraFuel : Nat)
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtList fields runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_sizeOf_extraFuel_step
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (extraFuel := extraFuel)
      hgeneric
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
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR
      FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hgeneric
      hscope
      hexact
      hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, hcompile, ?_⟩
  exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hstep

theorem exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {scope : List String}
    {stmts : List Stmt}
    (helperFuel : Nat)
    (extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope stmts = Except.ok bodyIR ∧
      let sourceResult := SourceSemantics.execStmtListWithHelpers spec fields helperFuel runtime stmts
      let irExec := execIRStmtsWithInternals runtimeContract (sizeOf bodyIR + extraFuel + 1) state bodyIR
      stmtResultMatchesIRExecWithInternals fields sourceResult irExec := by
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hfuelPos
      hgeneric
      hscope
      hexact
      hbounded
      hruntime with
    ⟨bodyIR, hcompile, hstep⟩
  refine ⟨bodyIR, hcompile, ?_⟩
  exact stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep

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
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_sizeOf_extraFuel
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hgeneric
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

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
        (SourceSemantics.effectiveFields model) sourceResult irExec := by
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hgeneric
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

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

/-- Exact helper-aware body theorem for an exact helper-aware generic
statement-induction witness. Unlike the transitional legacy-compiled-body
theorem, this already targets `execIRStmtsWithInternals`, so future helper-call
cases can be proved against the compiled semantics that actually executes
helper-rich Yul. -/
private theorem
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
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
  have hstateRuntime' :
      FunctionBody.runtimeStateMatchesIR
        (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx
          bindings := bindings }
        state := by
    simpa [FunctionBody.runtimeStateMatchesIR] using hstateRuntime
  have hbodyCompile' :
      compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
        (fn.params.map (·.name)) fn.body = Except.ok bodyStmts := by
    simpa [hnormalized, hnoEvents, hnoErrors] using hbodyCompile
  have hscopeExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (fn.params.map (·.name)) bindings state :=
    FunctionBody.bindingsExactlyMatchIRVars_implies_onScope hstateBindings
  let sizeSlack := extraFuel - (sizeOf bodyStmts - bodyStmts.length)
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel
      (runtimeContract := runtimeContract)
      (spec := model)
      (fields := SourceSemantics.effectiveFields model)
      (runtime := { world := SourceSemantics.withTransactionContext initialWorld tx
                    bindings := bindings })
      (state := state)
      (scope := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hfuelPos
      hgeneric
      hscope
      hscopeExact
      hbounded
      hstateRuntime' with
    ⟨bodyIR, hbodyGenericCompile, hgenericSem⟩
  have hbodyEq : bodyIR = bodyStmts := by
    rw [hbodyCompile'] at hbodyGenericCompile
    injection hbodyGenericCompile with hEq
    exact hEq.symm
  subst bodyIR
  have hlength_le : bodyStmts.length ≤ sizeOf bodyStmts := by
    have := yulStmtList_length_add_sizeOf_le_append bodyStmts []
    simp at this
    omega
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  rw [hfuel] at hgenericSem
  exact ⟨_, _, rfl, rfl, hgenericSem⟩

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
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompat :=
    execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
      (bodyStmts.length + extraFuel + 1)
      state
      bodyStmts
      hdisjoint
  cases irExec with
  | «continue» next =>
      refine ⟨sourceResult, .continue next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | «return» value next =>
      refine ⟨sourceResult, .return value next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | stop next =>
      refine ⟨sourceResult, .stop next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch
  | revert next =>
      refine ⟨sourceResult, .revert next, hsource, ?_, ?_⟩
      · rw [hcompat]; simp [hbodyExec]
      · simpa [stmtResultMatchesIRExecWithInternals] using hmatch

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  have hcompat :=
    execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
      (bodyStmts.length + extraFuel + 1)
      state
      bodyStmts
      hdisjoint
  rw [hcompat] at hbodyExec
  -- hbodyExec : (match execIRStmts ... with ...) = irExec
  -- case-split on `execIRStmts` to reduce the match in hbodyExec
  generalize hexec : execIRStmts (bodyStmts.length + extraFuel + 1) state bodyStmts = irPlain at hbodyExec
  cases irPlain with
  | «continue» next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .continue next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | «return» value next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .return value next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | stop next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .stop next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩
  | revert next =>
      simp only [] at hbodyExec; subst hbodyExec
      exact ⟨sourceResult, .revert next, hsource, hexec,
        by simpa [stmtResultMatchesIRExecWithInternals] using hmatch⟩

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir_raw
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hsteps := hsteps)
      (hlegacy := hlegacy)
      hinternal
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := model)
      (hhelperFree := hhelperFree)
      (hdirect := hdirect)
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
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  have hgeneric :
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract
        model
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body :=
    generic_with_helpers_and_helper_ir_of_split_internal_helper_surface_callsDisjoint
      runtimeContract model fn hhelperFree hcall hassign hexpr hstruct hresidual
      hdisjoint
  exact
    supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hgeneric hbodyCompile hscope
      hbounded hstateRuntime hstateBindings

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
    (hhelperSurface :
      stmtListTouchesUnsupportedHelperSurface fn.body = false)
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
    (hhelperSurface :
      stmtListTouchesUnsupportedHelperSurface fn.body = false)
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
      hextraFuel hfuelPos hnormalized hnoEvents hnoErrors hnoPacked hcontractSurface hhelperSurface
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
      compiledIR := by
  refine {
    compileOk := hcompile
    preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCallAssign_shape hcompile
  have hArgEq : argExprs' = argExprs := by
    simp [hargCompile] at hargOk
    exact hargOk.symm
  subst hArgEq
  set singletonIR :=
    [YulStmt.letMany names
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs')]
  have hshape' : compiledIR = singletonIR := by
    simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by simp [singletonIR]
    rw [hshape'] at hslack; rw [hlenOne] at hslack; omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]; omega
  rw [hshape'] at hslack ⊢
  rw [hlenOne] at hslack
  rw [hFuelEq]
  exact ⟨_, _, rfl, rfl, hMatch⟩

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
      compiledIR := by
  refine {
    compileOk := hcompile
    preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape hcompile
  have hArgEq : argExprs' = argExprs := by
    simp [hargCompile] at hargOk
    exact hargOk.symm
  subst hArgEq
  set singletonIR :=
    [YulStmt.expr
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs')]
  have hshape' : compiledIR = singletonIR := by
    simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by
    simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by simp [singletonIR]
    rw [hshape'] at hslack
    rw [hlenOne] at hslack
    omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]; omega
  rw [hshape'] at hslack ⊢
  rw [hlenOne] at hslack
  rw [hFuelEq]
  exact ⟨_, _, rfl, rfl, hMatch⟩

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
    DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn := by
  refine ⟨?_⟩
  intro calleeName hmem
  exfalso
  simpa [hbody.helperCallNames_nil] using hmem

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
