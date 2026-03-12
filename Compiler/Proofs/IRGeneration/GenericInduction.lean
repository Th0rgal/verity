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
  unfold CompilationModel.compileSetStorage at hcompile
  by_cases hmapping : isMapping fields fieldName
  · simp [hmapping] at hcompile
  · simp [hmapping] at hcompile
    rcases hfind : findFieldWithResolvedSlot fields fieldName with _ | ⟨f, slot⟩
    · simp [hfind] at hcompile
    · simp [hfind] at hcompile
      rcases hvalue : CompilationModel.compileExpr fields .calldata value with _ | valueExpr
      · simp [hvalue] at hcompile
      · simp [hvalue] at hcompile
        have hunpacked : f.packedBits = none :=
          hnoPacked f (field_mem_of_findFieldWithResolvedSlot_some hfind)
        rw [hunpacked] at hcompile
        cases halias : f.aliasSlots with
        | nil =>
            simp [halias] at hcompile
            injection hcompile with hbody
            subst hbody
            exact LegacyCompatibleExternalStmtList.expr
              (YulExpr.call "sstore" [YulExpr.lit slot, valueExpr])
              []
              LegacyCompatibleExternalStmtList.nil
        | cons alias rest =>
            simp [halias] at hcompile
            injection hcompile with hbody
            subst hbody
            apply LegacyCompatibleExternalStmtList.block
            · apply LegacyCompatibleExternalStmtList.let_
              exact legacyCompatibleExternalStmtList_of_exprStmtExprs
                (((slot :: alias :: rest).map
                  (fun writeSlot =>
                    YulExpr.call "sstore"
                      [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))
            · exact LegacyCompatibleExternalStmtList.nil

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
    injection hcompile with hbody
    subst hbody
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
    injection hcompile with hbody
    subst hbody
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
  rcases hcond : CompilationModel.compileExpr fields .calldata cond with _ | condIR
  · simp [hcond] at hcompile
  · simp [hcond] at hcompile
    injection hcompile with hbody
    subst hbody
    apply LegacyCompatibleExternalStmtList.if_
    · exact LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "iszero" [condIR])
        []
        LegacyCompatibleExternalStmtList.nil
    · exact legacyCompatibleExternalStmtList_revertMessage message
    · exact LegacyCompatibleExternalStmtList.nil

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
    injection hcompile with hbody
    subst hbody
    exact LegacyCompatibleExternalStmtList.expr
      (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
      []
      (LegacyCompatibleExternalStmtList.expr
        (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
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
    LegacyCompatibleExternalStmtList bodyIR := by
  cases stmt <;> simp [stmtTouchesUnsupportedContractSurface] at hsurface
  case letVar =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_letVar hcompile
  case assignVar =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_assignVar hcompile
  case setStorage =>
    unfold CompilationModel.compileStmt at hcompile
    exact legacyCompatibleExternalStmtList_of_compileSetStorage_ok_of_noPackedFields hnoPacked hcompile
  case require =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_require hcompile
  case return =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_return hcompile
  case stop =>
    exact legacyCompatibleExternalStmtList_of_compileStmt_ok_stop hcompile
  all_goals
    cases hsurface

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
  induction stmts generalizing inScopeNames bodyIR with
  | nil =>
      simpa [CompilationModel.compileStmtList] using hcompile
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2
      rcases FunctionBody.compileStmtList_cons_ok_inv
          (fields := fields)
          (inScopeNames := inScopeNames)
          (stmt := stmt)
          (rest := rest)
          hcompile with
        ⟨headIR, tailIR, hhead, htail, hbody⟩
      subst hbody
      exact legacyCompatibleExternalStmtList_append
        (legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
          hnoPacked hstmtSurface hhead)
        (ih hnoPacked hrestSurface htail)

/-- Derive the compiled-side legacy-compatibility witness needed by the exact
helper-aware induction seam from the existing supported contract-surface scan. -/
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
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro compiledIR hcompile
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked hstmtSurface hcompile

/-- Any list-level compiled witness for full legacy compatibility also suffices
for the weaker exact-seam witness that only constrains helper-free heads. -/
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

/-- The current supported contract surface also derives the weaker exact-seam
compiled witness that only constrains helper-free heads. Future helper-rich
bodies can reuse this witness for the unchanged helper-free cases while proving
exact helper-aware steps only for helper-positive heads. -/
theorem stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoPacked : ∀ field ∈ fields, field.packedBits = none)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListHelperFreeCompiledLegacyCompatible fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro _ compiledIR hcompile
      exact legacyCompatibleExternalStmtList_of_compileStmt_ok_on_supportedContractSurface
        hnoPacked hstmtSurface hcompile

/-- Any full helper-free generic statement-list proof also gives the weaker
source-side reuse witness needed by the future helper-rich exact seam: only the
helper-free heads retain the old generic-step obligation. -/
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
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hstmtInternal : stmtTouchesInternalHelperSurface stmt = false :=
        stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtInternal] at hhelper
      cases hhelper

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hstmtDirect : stmtTouchesDirectInternalHelperCallSurface stmt = false :=
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hstmtDirect : stmtTouchesDirectInternalHelperAssignSurface stmt = false :=
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

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
  induction hcall generalizing hassign with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadCall htailCall ih =>
      cases hassign with
      | cons hheadAssign htailAssign =>
          refine .cons ?_ (ih htailAssign)
          intro hdirect
          have hsplit := stmtTouchesDirectInternalHelperSurface_eq_split stmt
          by_cases hcallStmt : stmtTouchesDirectInternalHelperCallSurface stmt = true
          · exact hheadCall hcallStmt
          · have hassignStmt : stmtTouchesDirectInternalHelperAssignSurface stmt = true := by
              rw [hsplit] at hdirect
              rw [hcallStmt] at hdirect
              simpa using hdirect
            exact hheadAssign hassignStmt

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
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hstmtExpr : stmtTouchesExprInternalHelperSurface stmt = false :=
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtExpr] at hhelper
      cases hhelper

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hstmtStructural : stmtTouchesStructuralInternalHelperSurface stmt = false :=
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtStructural] at hhelper
      cases hhelper

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
  induction hdirect generalizing hexpr hstruct with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadDirect htailDirect ih =>
      cases hexpr with
      | cons hheadExpr htailExpr =>
          cases hstruct with
          | cons hheadStruct htailStruct =>
              refine .cons ?_ (ih htailExpr htailStruct)
              intro hhelper
              have hsplit := stmtTouchesInternalHelperSurface_eq_split stmt
              by_cases hdirectStmt : stmtTouchesDirectInternalHelperSurface stmt = true
              · exact hheadDirect hdirectStmt
              · by_cases hexprStmt : stmtTouchesExprInternalHelperSurface stmt = true
                · exact hheadExpr hexprStmt
                · have hstructStmt : stmtTouchesStructuralInternalHelperSurface stmt = true := by
                    rw [hsplit] at hhelper
                    rw [hdirectStmt, hexprStmt] at hhelper
                    simpa using hhelper
                  exact hheadStruct hstructStmt

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
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := by
        simpa [stmtListTouchesUnsupportedHelperSurface] using (Bool.or_eq_false.mp hsurface).2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper _
      rw [hstmtSurface] at hhelper
      cases hhelper

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
  induction hinternal generalizing hresidual with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadInternal htailInternal ih =>
      cases hresidual with
      | cons hheadResidual htailResidual =>
          refine .cons ?_ (ih htailResidual)
          intro hhelper
          by_cases hactual : stmtTouchesInternalHelperSurface stmt = true
          · exact hheadInternal hactual
          · exact hheadResidual hhelper hactual

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
  induction hgeneric generalizing hsurface with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false] at hsurface
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
        (ih hsurface.2)

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
  induction hhelperFree generalizing hsurface with
  | nil =>
      exact .nil
  | @cons scope stmt rest hhead htail ih =>
      simp [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false] at hsurface
      rcases hhead hsurface.1 with ⟨compiledIR, hstep⟩
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hsurface.1)
        (ih hsurface.2)

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
    intro runtime state helperFuel extraFuel _ hexact hscope hbounded hruntime hslack
    rcases hstep.preserves runtime state helperFuel extraFuel
        hexact hscope hbounded hruntime hslack with
      ⟨sourceResult, irExec, hsource, hir, hmatch⟩
    refine ⟨sourceResult,
      match irExec with
      | .continue next => .continue next
      | .return value next => .return value next
      | .stop next => .stop next
      | .revert next => .revert next,
      hsource, ?_, ?_⟩
    · have hcompat :=
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
      simpa [hir] using hcompat
    · cases irExec <;> simpa [stmtStepMatchesIRExecWithInternals] using hmatch

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
      runtimeContract spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    intro runtime state helperFuel extraFuel _ hexact hscope hbounded hruntime hslack
    rcases hstep.preserves runtime state helperFuel extraFuel
        hexact hscope hbounded hruntime hslack with
      ⟨sourceResult, irExec, hsource, hir, hmatch⟩
    refine ⟨sourceResult,
      match irExec with
      | .continue next => .continue next
      | .return value next => .return value next
      | .stop next => .stop next
      | .revert next => .revert next,
      hsource, ?_, ?_⟩
    · have hcompat :=
        execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
          (compiledIR.length + extraFuel + 1)
          state
          compiledIR
          hdisjoint
      simpa [hir] using hcompat
    · cases irExec <;> simpa [stmtStepMatchesIRExecWithInternals] using hmatch

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
  induction hgeneric generalizing hlegacy with
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
  induction hsteps generalizing hhelperFree hlegacy with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hlegacy with
          | cons hheadLegacy htailLegacy =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
                exact .cons
                  ((hcore.withHelpers_of_helperSurfaceClosed hsurface)
                    .withHelperIR_of_legacyCompatible
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
  induction hsteps generalizing hhelperFree hdisjoint with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hdisjoint with
          | cons hheadDisjoint htailDisjoint =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
                exact .cons
                  ((hcore.withHelpers_of_helperSurfaceClosed hsurface)
                    .withHelperIR_of_callsDisjoint
                      (hheadDisjoint hsurface compiledIR hcore.compileOk))
                  (ih htailFree htailDisjoint)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                exact .cons hcompiled (ih htailFree htailDisjoint)

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
          hinternal
          hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hdirect :=
        stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
          hcall
          hassign)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      hnoInternalFunctions

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hsteps := hsteps)
      (hlegacy := hlegacy)
      hinternal

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
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hsteps := hsteps)
      (hdisjoint := hdisjoint)

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
  induction expr with
  | literal value =>
      exact .literal value
  | param name =>
      exact .param name
  | storage field =>
      cases hsurface
  | storageAddr field =>
      cases hsurface
  | localVar name =>
      exact .localVar name
  | caller =>
      exact .caller
  | contractAddress =>
      exact .contractAddress
  | chainid =>
      exact .chainid
  | msgValue =>
      exact .msgValue
  | blockTimestamp =>
      exact .blockTimestamp
  | blockNumber =>
      exact .blockNumber
  | constructorArg idx =>
      cases hsurface
  | blobbasefee =>
      cases hsurface
  | calldatasize =>
      cases hsurface
  | returndataSize =>
      cases hsurface
  | arrayLength name =>
      cases hsurface
  | storageArrayLength field =>
      cases hsurface
  | returnDataOptionalBoolAt outOffset =>
      cases hsurface
  | mload offset =>
      cases hsurface
  | tload offset =>
      cases hsurface
  | calldataload offset =>
      cases hsurface
  | extcodesize addr =>
      cases hsurface
  | dynamicBytesEq lhs rhs =>
      cases hsurface
  | bitNot expr ih =>
      cases hsurface
  | logicalNot expr ih =>
      exact .logicalNot <| ih (by simpa [exprTouchesUnsupportedContractSurface] using hsurface)
  | add lhs rhs ihL ihR =>
      exact .add
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | sub lhs rhs ihL ihR =>
      exact .sub
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | mul lhs rhs ihL ihR =>
      exact .mul
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | div lhs rhs ihL ihR =>
      exact .div
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | sdiv lhs rhs ihL ihR =>
      cases hsurface
  | mod lhs rhs ihL ihR =>
      exact .mod
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | smod lhs rhs ihL ihR =>
      cases hsurface
  | bitAnd lhs rhs ihL ihR =>
      cases hsurface
  | bitOr lhs rhs ihL ihR =>
      cases hsurface
  | bitXor lhs rhs ihL ihR =>
      cases hsurface
  | shl lhs rhs ihL ihR =>
      cases hsurface
  | shr lhs rhs ihL ihR =>
      cases hsurface
  | sar lhs rhs ihL ihR =>
      cases hsurface
  | signextend lhs rhs ihL ihR =>
      cases hsurface
  | eq lhs rhs ihL ihR =>
      exact .eq
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | ge lhs rhs ihL ihR =>
      exact .ge
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | gt lhs rhs ihL ihR =>
      exact .gt
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | sgt lhs rhs ihL ihR =>
      cases hsurface
  | lt lhs rhs ihL ihR =>
      exact .lt
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | slt lhs rhs ihL ihR =>
      cases hsurface
  | le lhs rhs ihL ihR =>
      exact .le
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | logicalAnd lhs rhs ihL ihR =>
      exact .logicalAnd
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | logicalOr lhs rhs ihL ihR =>
      exact .logicalOr
        (ihL <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).1)
        (ihR <| by simpa [exprTouchesUnsupportedContractSurface] using (Bool.or_eq_false.mp hsurface).2)
  | ite cond thenVal elseVal ihCond ihThen ihElse =>
      cases hsurface
  | min lhs rhs ihL ihR =>
      cases hsurface
  | max lhs rhs ihL ihR =>
      cases hsurface
  | wMulDown lhs rhs ihL ihR =>
      cases hsurface
  | wDivUp lhs rhs ihL ihR =>
      cases hsurface
  | mulDivDown a b c ihA ihB ihC =>
      cases hsurface
  | mulDivUp a b c ihA ihB ihC =>
      cases hsurface
  | mapping field key ih =>
      cases hsurface
  | mappingWord field key offset ih =>
      cases hsurface
  | mappingPackedWord field key offset packed ih =>
      cases hsurface
  | mapping2 field key1 key2 ih1 ih2 =>
      cases hsurface
  | mapping2Word field key1 key2 offset ih1 ih2 =>
      cases hsurface
  | mappingUint field key ih =>
      cases hsurface
  | mappingChain field keys ih =>
      cases hsurface
  | structMember field key memberName ih =>
      cases hsurface
  | structMember2 field key1 key2 memberName ih1 ih2 =>
      cases hsurface
  | arrayElement name index ih =>
      cases hsurface
  | storageArrayElement field index ih =>
      cases hsurface
  | call gas target value inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 ih7 =>
      cases hsurface
  | staticcall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 =>
      cases hsurface
  | delegatecall gas target inOffset inSize outOffset outSize ih1 ih2 ih3 ih4 ih5 ih6 =>
      cases hsurface
  | externalCall name args ih =>
      cases hsurface
  | internalCall name args ih =>
      cases hsurface

private theorem fieldName_mem_fields_of_findFieldWithResolvedSlot_some
    {fields : List Field}
    {fieldName : String}
    {f : Field}
    {slot : Nat}
    (hfind : findFieldWithResolvedSlot fields fieldName = some (f, slot)) :
    fieldName ∈ fields.map (·.name) := by
  induction fields with
  | nil =>
      simp [findFieldWithResolvedSlot] at hfind
  | cons field rest ih =>
      simp [findFieldWithResolvedSlot] at hfind ⊢
      by_cases hname : field.name == fieldName
      · simp [hname]
      · simp [hname] at hfind
        exact Or.inr (ih hfind)

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
  | ok condIR =>
      cases hthen :
          CompilationModel.compileStmtList fields [] [] .calldata [] false scope thenBranch with
      | error err =>
          simp [hcond, hthen] at hcompile
      | ok thenIR =>
          cases helse :
              CompilationModel.compileStmtList fields [] [] .calldata [] false scope elseBranch with
          | error err =>
              simp [hcond, hthen, helse] at hcompile
          | ok elseIR =>
              by_cases helseEmpty : elseBranch.isEmpty
              · simp [hcond, hthen, helse, helseEmpty] at hcompile
                exact ⟨condIR, thenIR, elseIR, hcond, hthen, helse⟩
              · simp [hcond, hthen, helse, helseEmpty] at hcompile
                exact ⟨condIR, thenIR, elseIR, hcond, hthen, helse⟩

theorem stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
    {fields : List Field}
    {scope : List String}
    {prefix suffix : List Stmt}
    {bodyIR : List YulStmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (prefix ++ suffix) = false)
    (hcompile :
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false scope (prefix ++ suffix) =
          Except.ok bodyIR) :
    StmtListScopeCore (fields.map (·.name)) prefix := by
  induction prefix generalizing scope suffix bodyIR with
  | nil =>
      exact StmtListScopeCore.nil
  | cons stmt rest ih =>
      rcases compileStmtList_cons_ok_inv hcompile with
        ⟨headIR, tailIR, hhead, htail, rfl⟩
      have hstmtSurface :
          stmtTouchesUnsupportedContractSurface stmt = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false.mp hsurface).1
      have hrestSurface :
          stmtListTouchesUnsupportedContractSurface (rest ++ suffix) = false := by
        simpa [stmtListTouchesUnsupportedContractSurface] using
          (Bool.or_eq_false.mp hsurface).2
      cases stmt with
      | letVar name value =>
          exact StmtListScopeCore.letVar
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | assignVar name value =>
          exact StmtListScopeCore.assignVar
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setStorage fieldName value =>
          have hfield :
              fieldName ∈ fields.map (·.name) := by
            simp [CompilationModel.compileStmt] at hhead
            exact fieldName_mem_fields_of_compileSetStorage_ok hhead
          exact StmtListScopeCore.setStorage
            hfield
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | setStorageAddr fieldName value =>
          cases hstmtSurface
      | require cond message =>
          exact StmtListScopeCore.require
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | return value =>
          exact StmtListScopeCore.return_
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
              (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface))
            (ih hrestSurface htail)
      | stop =>
          exact StmtListScopeCore.stop (ih hrestSurface htail)
      | ite cond thenBranch elseBranch =>
          have hcondSurface :
              exprTouchesUnsupportedContractSurface cond = false := by
            have hfalse1 := (Bool.or_eq_false.mp hstmtSurface).1
            simpa [stmtTouchesUnsupportedContractSurface] using hfalse1
          have hbranchesSurface :
              stmtListTouchesUnsupportedContractSurface thenBranch ||
                stmtListTouchesUnsupportedContractSurface elseBranch = false := by
            have hfalse2 := (Bool.or_eq_false.mp hstmtSurface).2
            simpa [stmtTouchesUnsupportedContractSurface] using hfalse2
          have hthenSurface :
              stmtListTouchesUnsupportedContractSurface thenBranch = false :=
            (Bool.or_eq_false.mp hbranchesSurface).1
          have helseSurface :
              stmtListTouchesUnsupportedContractSurface elseBranch = false :=
            (Bool.or_eq_false.mp hbranchesSurface).2
          rcases compileStmt_ite_ok_inv hhead with ⟨condIR, thenIR, elseIR, _, hthen, helse⟩
          exact StmtListScopeCore.ite
            (exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false hcondSurface)
            (stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
              (scope := scope) (prefix := thenBranch) (suffix := [])
              (bodyIR := thenIR) (by simpa using hthenSurface) hthen)
            (stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
              (scope := scope) (prefix := elseBranch) (suffix := [])
              (bodyIR := elseIR) (by simpa using helseSurface) helse)
            (ih hrestSurface htail)
      | mstore offset value =>
          cases hstmtSurface
      | tstore offset value =>
          cases hstmtSurface
      | storageArrayPush field value =>
          cases hstmtSurface
      | storageArrayPop field =>
          cases hstmtSurface
      | setStorageArrayElement field index value =>
          cases hstmtSurface
      | setMapping field key value =>
          cases hstmtSurface
      | setMappingWord field key wordOffset value =>
          cases hstmtSurface
      | setMappingPackedWord field key wordOffset packed value =>
          cases hstmtSurface
      | setMapping2 field key1 key2 value =>
          cases hstmtSurface
      | setMapping2Word field key1 key2 wordOffset value =>
          cases hstmtSurface
      | setMappingUint field key value =>
          cases hstmtSurface
      | setMappingChain field keys value =>
          cases hstmtSurface
      | setStructMember field key memberName value =>
          cases hstmtSurface
      | setStructMember2 field key1 key2 memberName value =>
          cases hstmtSurface
      | requireError cond errorName args =>
          cases hstmtSurface
      | revertError errorName args =>
          cases hstmtSurface
      | returnValues values =>
          cases hstmtSurface
      | returnArray name =>
          cases hstmtSurface
      | returnBytes name =>
          cases hstmtSurface
      | returnStorageWords name =>
          cases hstmtSurface
      | calldatacopy destOffset sourceOffset size =>
          cases hstmtSurface
      | returndataCopy destOffset sourceOffset size =>
          cases hstmtSurface
      | revertReturndata =>
          cases hstmtSurface
      | forEach varName count body =>
          cases hstmtSurface
      | emit eventName args =>
          cases hstmtSurface
      | internalCall functionName args =>
          cases hstmtSurface
      | internalCallAssign names functionName args =>
          cases hstmtSurface
      | rawLog topics dataOffset dataSize =>
          cases hstmtSurface
      | externalCallBind resultVars externalName args =>
          cases hstmtSurface
      | ecm mod args =>
          cases hstmtSurface

private theorem stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
    {prefix suffix : List Stmt}
    {stmt : Stmt}
    (hsurface :
      stmtListTouchesUnsupportedContractSurface (prefix ++ stmt :: suffix) = false) :
    stmtTouchesUnsupportedContractSurface stmt = false := by
  induction prefix with
  | nil =>
      simpa [stmtListTouchesUnsupportedContractSurface] using
        (Bool.or_eq_false.mp hsurface).1
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
      simp [validateScopedExprIdentifiers] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hparamsInScope name0 hvalidate
  | localVar name0 =>
      intro name hmem
      simp [validateScopedExprIdentifiers] at hvalidate
      simp [FunctionBody.exprBoundNames] at hmem
      subst name
      exact hlocalsInScope name0 hvalidate
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
  | le hL hR ihL ihR =>
      simp [validateScopedExprIdentifiers] at hvalidate
      intro name hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihL hvalidate.1 hparamsInScope hlocalsInScope _ hmem
      · exact ihR hvalidate.2 hparamsInScope hlocalsInScope _ hmem
  | logicalNot h ih =>
      intro name hmem
      simpa [FunctionBody.exprBoundNames] using
        ih (by simpa [validateScopedExprIdentifiers] using hvalidate)
          hparamsInScope hlocalsInScope name hmem
  | logicalAnd hL hR ihL ihR
  | logicalOr hL hR ihL ihR =>
      simp [validateScopedExprIdentifiers] at hvalidate
      intro name hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact ihL hvalidate.2.1 hparamsInScope hlocalsInScope _ hmem
      · exact ihR hvalidate.2.2 hparamsInScope hlocalsInScope _ hmem

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
      cases hvalidate
      exact StmtListScopeDiscipline.nil
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, _, _, rfl⟩
      exact StmtListScopeDiscipline.letVar
        hvalueCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨_, hvalueValidate, rfl⟩
      exact StmtListScopeDiscipline.assignVar
        hvalueCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hcondValidate, rfl⟩
      exact StmtListScopeDiscipline.require
        hcondCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hcondCore hcondValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
      exact StmtListScopeDiscipline.return_
        hvalueCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with rfl
      refine StmtListScopeDiscipline.stop ?_
      exact ih hrestValidate hparamsInScope hlocalsInScope
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
      exact StmtListScopeDiscipline.setStorage
        hfield
        hvalueCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
      exact StmtListScopeDiscipline.setStorageAddr
        hfield
        hvalueCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hvalueCore hvalueValidate hparamsInScope hlocalsInScope)
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hcondValidate, hthenValidate, helseValidate, rfl⟩
      exact StmtListScopeDiscipline.ite
        hcondCore
        (exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
          hcondCore hcondValidate hparamsInScope hlocalsInScope)
        (ihThen hthenValidate hparamsInScope hlocalsInScope)
        (ihElse helseValidate hparamsInScope hlocalsInScope)
        (ihRest hrestValidate
          (by
            intro other hmem
            exact mem_stmtNextScope_of_mem_scope (hparamsInScope other hmem))
          (by
            intro other hmem
            exact mem_stmtNextScope_of_mem_scope (hlocalsInScope other hmem)))

theorem stmtListScopeDiscipline_of_validateFunctionIdentifierReferences_prefix
    {spec : FunctionSpec}
    {fieldNames : List String}
    {prefix suffix : List Stmt}
    (hcore : StmtListScopeCore fieldNames prefix)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = prefix ++ suffix) :
    StmtListScopeDiscipline fieldNames (spec.params.map (·.name)) prefix := by
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
      cases hvalidate
      intro name hmem
      simpa using hmem
  | letVar hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, _, _, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨_, hvalueValidate, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hcondValidate, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with rfl
      intro other hmem
      exact ih hrestValidate hparamsInScope hlocalsInScope other hmem
  | setStorage hfield hvalueCore hrest ih =>
      rcases validateScopedStmtListIdentifiers_cons_ok_inv hvalidate with
        ⟨nextLocalScope, hstmt, hrestValidate⟩
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hvalueValidate, rfl⟩
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
      simp [validateScopedStmtIdentifiers] at hstmt
      rcases hstmt with ⟨hcondValidate, hthenValidate, helseValidate, rfl⟩
      intro other hmem
      exact ihRest hrestValidate
        (by
          intro name hname
          exact mem_stmtNextScope_of_mem_scope (hparamsInScope name hname))
        (by
          intro name hname
          exact mem_stmtNextScope_of_mem_scope (hlocalsInScope name hname))
        other hmem

private theorem exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
    {spec : FunctionSpec}
    {fieldNames : List String}
    {prefix suffix : List Stmt}
    {fieldName : String}
    {value : Expr}
    (hprefixCore : StmtListScopeCore fieldNames prefix)
    (hvalueCore : FunctionBody.ExprCompileCore value)
    (hvalidate : validateFunctionIdentifierReferences spec = Except.ok ())
    (hparamScope : paramScopeNames spec.params = spec.params.map (·.name))
    (hbody : spec.body = prefix ++ .setStorage fieldName value :: suffix) :
    FunctionBody.exprBoundNamesInScope
      value
      (List.foldl stmtNextScope (spec.params.map (·.name)) prefix) := by
  rcases validateFunctionIdentifierReferences_prefix_stmt_ok hvalidate hbody with
    ⟨localScope, nextScope, hprefixValidate, hstmtValidate⟩
  simp [validateScopedStmtIdentifiers] at hstmtValidate
  rcases hstmtValidate with ⟨hvalueValidate, rfl⟩
  apply exprBoundNamesInScope_of_validateScopedExprIdentifiers_core
    (paramScope := paramScopeNames spec.params)
    (dynamicParams := dynamicParamBases spec.params)
    (localScope := localScope)
    (scope := List.foldl stmtNextScope (spec.params.map (·.name)) prefix)
    hvalueCore
    hvalueValidate
  · intro name hname
    rw [hparamScope] at hname
    exact mem_stmtNextScopeList_of_mem_scope hname
  · intro name hname
    exact scopeNamesPresent_foldl_stmtNextScope_of_validateScopedStmtListIdentifiers
      hprefixCore
      hprefixValidate
      (by
        intro other hmem
        rw [hparamScope] at hmem
        simpa using hmem)
      (by
        intro other hmem
        simp at hmem)
      name
      hname

private theorem collectExprNames_mem_exprBoundNames_of_core
    {expr : Expr}
    (hcore : FunctionBody.ExprCompileCore expr) :
    ∀ name, name ∈ collectExprNames expr → name ∈ FunctionBody.exprBoundNames expr := by
  induction hcore with
  | literal value =>
      intro name hmem
      simp at hmem
  | param name0 =>
      intro name hmem
      simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
  | localVar name0 =>
      intro name hmem
      simpa [collectExprNames, FunctionBody.exprBoundNames] using hmem
  | caller | contractAddress | msgValue | blockTimestamp | blockNumber | chainid =>
      intro name hmem
      simp at hmem
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
  | logicalAnd hL hR ihL ihR
  | logicalOr hL hR ihL ihR =>
      intro name hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact List.mem_append.mpr <| Or.inl <| ihL _ hmem
      · exact List.mem_append.mpr <| Or.inr <| ihR _ hmem
  | logicalNot h ih =>
      intro name hmem
      simpa [collectExprNames, FunctionBody.exprBoundNames] using ih _ hmem

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
      simpa using hmem
  | letVar hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hname | htail
      · exact Or.inr <| Or.inl hname
      rcases htail with hvalue | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · exact Or.inr <| Or.inr htail
  | assignVar hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hname | htail
      · exact Or.inr <| Or.inr <| Or.inl hname
      rcases htail with hvalue | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · exact Or.inr <| Or.inr <| Or.inr htail
  | require hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hcond | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      · exact Or.inr htail
  | return_ hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hvalue | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · exact Or.inr htail
  | stop hrest ih =>
      intro other hmem
      simpa [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] using ih other hmem
  | setStorage hfield hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hfieldMem | htail
      · exact Or.inr <| Or.inr <| Or.inr <| by simpa using hfieldMem
      rcases htail with hvalue | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · exact Or.inr htail
  | setStorageAddr hfield hcore hinScope hrest ih =>
      intro other hmem
      have htail := ih other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hfieldMem | htail
      · exact Or.inr <| Or.inr <| Or.inr <| by simpa using hfieldMem
      rcases htail with hvalue | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hvalue)
      · exact Or.inr htail
  | ite hcore hinScope hthen helse hrest ihThen ihElse ihRest =>
      intro other hmem
      have htail := ihRest other hmem
      simp [stmtNextScope, collectStmtNames, collectStmtListBindNames,
        collectStmtListAssignedNames] at htail ⊢
      rcases htail with hcond | htail
      · exact Or.inl <| hinScope _ (collectExprNames_mem_exprBoundNames_of_core hcore _ hcond)
      rcases htail with hthenMem | htail
      · have hthenNames :=
          ihThen other (by
            simpa using (List.mem_append.mpr (Or.inl hthenMem)))
        simpa [collectStmtListBindNames, collectStmtListAssignedNames] using hthenNames
      rcases htail with helseMem | htail
      · have helseNames :=
          ihElse other (by
            simpa using (List.mem_append.mpr (Or.inl helseMem)))
        simpa [collectStmtListBindNames, collectStmtListAssignedNames] using helseNames
      · exact Or.inr htail

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
    let slack := sizeOf [YulStmt.let_ name valueIR] - [YulStmt.let_ name valueIR].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.let_ name valueIR] + wholeExtraFuel + 1 =
          [YulStmt.let_ name valueIR].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_let_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (name := name)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hscope hbounded hruntime with
      ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel] using hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
        And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

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
    let slack := sizeOf [YulStmt.assign name valueIR] - [YulStmt.assign name valueIR].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.assign name valueIR] + wholeExtraFuel + 1 =
          [YulStmt.assign name valueIR].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_assign_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (name := name)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hscope hbounded hruntime with
      ⟨valueIR', hvalueIR', hwhole, hruntime', hexact', hbounded', hscope'⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel] using hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
        And.intro hruntime' <| And.intro hexact' <| And.intro hbounded' hscope'

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
    let slack :=
      sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] -
        [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] + wholeExtraFuel + 1 =
          [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack]
      have : slack ≤ extraFuel := by
        simpa [slack] using hslack
      omega
    by_cases hcondZero : SourceSemantics.evalExpr fields runtime cond = 0
    · rcases FunctionBody.execIRStmts_compiled_require_core_fail_append_wholeFuel_of_scope
          (fields := fields)
          (runtime := runtime)
          (state := state)
          (scope := scope)
          (cond := cond)
          (message := message)
          (tailIR := [])
          (extraFuel := wholeExtraFuel)
          hcore hexact hinScope hscope hbounded hruntime hcondZero with
        ⟨failCond', revState, hfailCompile', hwhole⟩
      rw [hfailCompile] at hfailCompile'
      injection hfailCompile' with hEq
      subst hEq
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, hcondZero]
      · simpa [hwholeFuel] using hwhole
      · simp [stmtStepMatchesIRExec]
    · have hcondNeZero : SourceSemantics.evalExpr fields runtime cond ≠ 0 := hcondZero
      have hwhole :=
        FunctionBody.execIRStmts_compiled_require_core_pass_append_wholeFuel_of_scope
          (fields := fields)
          (runtime := runtime)
          (state := state)
          (scope := scope)
          (cond := cond)
          (message := message)
          (tailIR := [])
          (extraFuel := wholeExtraFuel)
          hcore hexact hinScope hscope hbounded hruntime hcondNeZero
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, hcondNeZero]
      · simpa [hwholeFuel] using hwhole
      · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
          And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope

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
    simp [CompilationModel.compileStmt, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR :=
      [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    rcases FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope
        (fields := fields)
        (runtime := runtime)
        (state := state)
        (scope := scope)
        (value := value)
        (tailIR := [])
        (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime with
      ⟨valueIR', hvalueIR', hwhole⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    let retVal := SourceSemantics.evalExpr fields runtime value
    let retState := { state with memory := fun o => if o = 0 then retVal else state.memory o }
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [hwholeFuel, compiledIR, retVal, retState] using hwhole
    · refine ⟨rfl, ?_⟩
      exact FunctionBody.runtimeStateMatchesIR_setMemory hruntime 0 retVal

theorem compiledStmtStep_stop
    {fields : List Field}
    {scope : List String} :
    CompiledStmtStep fields scope .stop [YulStmt.expr (YulExpr.call "stop" [])] where
  compileOk := by
    simp [CompilationModel.compileStmt]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "stop" [])]
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt]
    · simpa [compiledIR, hwholeFuel] using
        (FunctionBody.execIRStmts_compiled_stop_core_append_wholeFuel
          (state := state) (tailIR := []) (extraFuel := wholeExtraFuel))
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
  simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots, hneq]

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
  simp [SourceSemantics.encodeStorageAt, SourceSemantics.writeUintSlots,
    List.contains_eq_false.mpr hnotMem]

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
  induction seen with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      simp at hmem ⊢
      by_cases hEq : entry.1 = slot
      · subst hEq
        simp [packedSlotsConflict]
      · simp [hEq, ih hmem]

private theorem firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
    {seen current : List (Nat × String × Option PackedBits)}
    {slot : Nat}
    (hseen : slot ∈ seen.map (fun entry => entry.1))
    (hcurrent : slot ∈ current.map (fun entry => entry.1))
    (hunpacked : ∀ packed ∈ current.map (fun entry => entry.2.2), packed = none) :
    firstInFieldConflictCopy seen current ≠ none := by
  induction current generalizing seen with
  | nil =>
      cases hcurrent
  | cons entry rest ih =>
      simp at hcurrent
      have hpnone : entry.2.2 = none := hunpacked entry.2.2 (by simp)
      rcases hcurrent with hEq | hrest
      · subst hEq
        have hfindSeen :
            (seen.find? (fun seenEntry => seenEntry.1 == entry.1 &&
              packedSlotsConflict seenEntry.2.2 entry.2.2)) ≠ none := by
          simpa [hpnone] using list_findSlotPackedNone_ne_none hseen
        intro hnone
        simp [firstInFieldConflictCopy, hpnone, hfindSeen] at hnone
      · have hunpackedRest :
            ∀ packed ∈ rest.map (fun restEntry => restEntry.2.2), packed = none := by
          intro packed hmem
          exact hunpacked packed (by simp [hmem])
        intro hnone
        cases hfind : seen.find? (fun seenEntry => seenEntry.1 == entry.1 &&
            packedSlotsConflict seenEntry.2.2 entry.2.2)
        · have htailNone :
              firstInFieldConflictCopy ((entry.1, entry.2.1, entry.2.2) :: seen) rest = none := by
            simpa [firstInFieldConflictCopy, hfind] using hnone
          have hseen' :
              slot ∈ (((entry.1, entry.2.1, entry.2.2) :: seen).map (fun seenEntry => seenEntry.1)) := by
            simp [hseen]
          exact (ih hseen' hrest hunpackedRest) htailNone
        · simp [firstInFieldConflictCopy, hfind] at hnone

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
  | nil =>
      cases hfind
  | cons field rest ih =>
      by_cases hname : field.name == fieldName
      · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
        injection hfind with hf hslotEq
        subst hf
        subst hslotEq
        injection hwrite with hwriteEq
        subst hwriteEq
        have hcurrent :
            targetSlot ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.1) := by
          simpa [fieldWriteEntriesAt] using hslot
        have hunpackedCurrent :
            ∀ packed ∈ (fieldWriteEntriesAt idx field).map (fun entry => entry.2.2), packed = none := by
          intro packed hmem
          simpa [fieldWriteEntriesAt, hunpacked] using hmem
        exact firstInFieldConflictCopy_ne_none_of_seen_slot_unpacked
          hseen hcurrent hunpackedCurrent
      · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at hfind hwrite
        intro hnone
        cases hfirst : firstInFieldConflictCopy seen (fieldWriteEntriesAt idx field)
        · have htailNone :
              firstFieldWriteSlotConflictCopyFrom
                ((fieldWriteEntriesAt idx field).reverse ++ seen)
                (idx + 1)
                rest = none := by
            simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnone
          have hseen' :
              targetSlot ∈
                (((fieldWriteEntriesAt idx field).reverse ++ seen).map
                  (fun entry => entry.1)) := by
            simp [hseen]
          exact (ih hseen' hfind hwrite hslot hunpacked) htailNone
        · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnone

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
    findResolvedFieldAtSlotCopy fields targetSlot = some f := by
  have hnoConflictCopy :
      firstFieldWriteSlotConflictCopyFrom [] 0 fields = none := by
    simpa [firstFieldWriteSlotConflict, firstFieldWriteSlotConflictCopyFrom,
      fieldWriteEntriesAt, firstInFieldConflictCopy] using hnoConflict
  have hfindCopy :
      findFieldWithResolvedSlotCopyFrom fields 0 fieldName = some (f, slot) := by
    simpa [findFieldWithResolvedSlot, findFieldWithResolvedSlotCopyFrom] using hfind
  have hwriteCopy :
      findFieldWriteSlotsCopyFrom fields 0 fieldName = some writeSlots := by
    simpa [findFieldWriteSlots, findFieldWriteSlotsCopyFrom] using hwrite
  have hresolved :
      findResolvedFieldAtSlotCopyFrom fields 0 targetSlot = some f := by
    induction fields generalizing targetSlot with
    | nil =>
        cases hfindCopy
    | cons field rest ih =>
        by_cases hname : field.name == fieldName
        · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
            hfindCopy hwriteCopy
          injection hfindCopy with hf hslotEq
          subst hf
          subst hslotEq
          injection hwriteCopy with hwriteEq
          subst hwriteEq
          rcases List.mem_cons.mp hslot with htargetEq | htargetAlias
          · simp [findResolvedFieldAtSlotCopyFrom, htargetEq]
          · have hcontains : field.aliasSlots.contains targetSlot = true :=
              List.contains_eq_true.mpr htargetAlias
            simp [findResolvedFieldAtSlotCopyFrom, hcontains]
        · simp [findFieldWithResolvedSlotCopyFrom, findFieldWriteSlotsCopyFrom, hname] at
            hfindCopy hwriteCopy
          cases hfirst : firstInFieldConflictCopy [] (fieldWriteEntriesAt 0 field)
          · have htailNoConflict :
                firstFieldWriteSlotConflictCopyFrom
                  (fieldWriteEntriesAt 0 field).reverse
                  1
                  rest = none := by
              simpa [firstFieldWriteSlotConflictCopyFrom, hfirst] using hnoConflictCopy
            have hheadNotOwn :
                targetSlot ∉ (fieldWriteEntriesAt 0 field).map (fun entry => entry.1) := by
              intro hmem
              have hmemRev :
                  targetSlot ∈ ((fieldWriteEntriesAt 0 field).reverse.map (fun entry => entry.1)) := by
                simpa [List.map_reverse] using (List.mem_reverse.mpr hmem)
              exact
                (firstFieldWriteSlotConflictCopyFrom_some_of_seen_slot_member
                  hmemRev hfindCopy hwriteCopy hslot hunpacked) htailNoConflict
            have hresolvedNe : field.slot.getD 0 ≠ targetSlot := by
              have hheadNotOwn' := hheadNotOwn
              simp [fieldWriteEntriesAt] at hheadNotOwn'
              exact hheadNotOwn'.1
            have haliasNotMem : targetSlot ∉ field.aliasSlots := by
              have hheadNotOwn' := hheadNotOwn
              simp [fieldWriteEntriesAt] at hheadNotOwn'
              exact hheadNotOwn'.2
            have haliasNe : field.aliasSlots.contains targetSlot = false :=
              List.contains_eq_false.mpr haliasNotMem
            simpa [findResolvedFieldAtSlotCopyFrom, hresolvedNe, haliasNe] using
              ih (targetSlot := targetSlot) htailNoConflict hfindCopy hwriteCopy hslot hunpacked
          · simp [firstFieldWriteSlotConflictCopyFrom, hfirst] at hnoConflictCopy
  simpa [findResolvedFieldAtSlotCopy, findResolvedFieldAtSlotCopyFrom] using hresolved

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
      encodeStorageAtCopy fields world slot := by
  simp [SourceSemantics.encodeStorageAt, encodeStorageAtCopy,
    findResolvedFieldAtSlotCopy, findDynamicArrayElementAtSlotCopy]

private theorem encodeStorageAt_eq_storage_of_resolvedSlot
    {fields : List Field}
    {world : Verity.ContractState}
    {slot : Nat}
    {f : Field}
    (hresolved : findResolvedFieldAtSlotCopy fields slot = some f)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false) :
    SourceSemantics.encodeStorageAt fields world slot = (world.storage slot).val := by
  rw [encodeStorageAt_eq_copy, encodeStorageAtCopy, hresolved, hnotAddr, hnotDyn]

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
        simp [abstractStoreStorageOrMappingMany, Compiler.Proofs.abstractStoreStorageOrMapping_eq]
      · simp [abstractStoreStorageOrMappingMany, ih,
          Compiler.Proofs.abstractStoreStorageOrMapping_eq, hEq]

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
  rcases hruntime with
    ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hEq : query = slot
  · subst hEq
    rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage,
      encodeStorageAt_eq_storage_of_resolvedSlot hresolved hnotAddr hnotDyn]
    simp [SourceSemantics.writeUintSlots]
  · rw [Compiler.Proofs.abstractStoreStorageOrMapping_eq, hstorage]
    simp [hEq, encodeStorageAt_writeUintSlots_singleton_other]

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
  rcases hruntime with
    ⟨hstorage, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  refine ⟨?_, hsender, hmsgValue, hthis, htimestamp, hblock, hchain, hret, hevents⟩
  funext query
  by_cases hmem : query ∈ slots
  · rw [abstractStoreStorageOrMappingMany_eq, hstorage,
      encodeStorageAt_eq_storage_of_resolvedSlot (hresolved query hmem) hnotAddr hnotDyn]
    simp [SourceSemantics.writeUintSlots, List.contains_eq_true.mpr hmem]
  · rw [abstractStoreStorageOrMappingMany_eq, hstorage]
    simp [List.contains_eq_false.mpr hmem, encodeStorageAt_writeUintSlots_other hmem]

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
        simpa [evalIRExpr, IRState.getVar, hvalue]
      have hvalueNext : IRState.getVar nextState name = value := by
        simpa [nextState, IRState.getVar] using hvalue
      have htail :=
        ih (fuel := fuel) (state := nextState) (name := name) (value := value) hvalueNext
      simpa [execIRStmts, abstractStoreStorageOrMappingMany, nextState] using htail

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
      (by simp [IRState.getVar])
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

private theorem compatValue_not_mem_scope_of_reservedPrefix
    {scope : List String}
    (hscopeReserved : scopeAvoidsReservedCompilerPrefix scope) :
    "__compat_value" ∉ scope := by
  intro hmem
  have hreserved : ¬ "__compat_value".startsWith "__" :=
    hscopeReserved "__compat_value" hmem
  exact hreserved (by decide)

private theorem validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix
    {spec : CompilationModel}
    {name : String}
    (hvalidate : validateIdentifierShapes spec = Except.ok ())
    (hmem : name ∈ spec.fields.map (·.name)) :
    ¬ name.startsWith "__" := by
  have hfield :
      ∃ field, field ∈ spec.fields ∧ field.name = name := by
    induction spec.fields with
    | nil =>
        cases hmem
    | cons field rest ih =>
        simp at hmem
        rcases hmem with rfl | hmem
        · exact ⟨field, by simp, rfl⟩
        · rcases ih hmem with ⟨found, hfoundMem, hfoundName⟩
          exact ⟨found, by simp [hfoundMem], hfoundName⟩
  rcases hfield with ⟨field, hfieldMem, hfieldName⟩
  subst hfieldName
  exact CompilationModel.validateIdentifierShapes_field_avoidReservedCompilerPrefix
    hvalidate hfieldMem

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
  repeat
    rw [List.mem_append] at hname
  rcases hname with hparam | hrest
  · exact CompilationModel.validateIdentifierShapes_functionParams_avoidReservedCompilerPrefix
      hvalidate hfn hparam
  rcases hrest with hlocal | hrest
  · exact CompilationModel.validateIdentifierShapes_functionLocals_avoidReservedCompilerPrefix
      hvalidate hfn hlocal
  rcases hrest with hassign | hfield
  · exact CompilationModel.validateIdentifierShapes_functionAssignTargets_avoidReservedCompilerPrefix
      hvalidate hfn hassign
  · exact validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix hvalidate hfield

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
      [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hfind, halias, hunpacked, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let compiledIR := [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])]
    let valueNat := SourceSemantics.evalExpr fields runtime value
    have hresolvedSlot :
        findResolvedFieldAtSlotCopy fields slot = some f :=
      findResolvedFieldAtSlotCopy_of_findFieldWithResolvedSlot_singleton
        hnoConflict hfind hwriteSlots hunpacked
    have heval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at heval
    have hvalueEval : evalIRExpr state valueIR = some valueNat := by
      simpa [valueNat] using heval
    have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
      simpa [compiledIR] using hslack
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt, hwriteSlots, valueNat]
    · have hExecStmt :
          execIRStmt (extraFuel + 1) state
            (YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueIR])) =
              .continue
                { state with
                    storage :=
                      Compiler.Proofs.abstractStoreStorageOrMapping
                        state.storage slot valueNat } :=
        execIRStmt_sstore_lit_expr_succ_of_eval
          extraFuel state slot valueIR valueNat hvalueEval
      simpa [compiledIR, execIRStmts, hExecStmt]
    · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
      · exact runtimeStateMatchesIR_writeUintSlot hruntime hresolvedSlot hnotAddr hnotDyn
      · exact bindingsExactlyMatchIRVarsOnScope_writeUintSlot hexact

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
              (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"])))] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileSetStorage,
      hfind, hwriteSlots, halias, hunpacked, hvalueIR]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    let slots := slot :: f.aliasSlots
    let blockBody :=
      [YulStmt.let_ "__compat_value" valueIR] ++
        slots.map (fun writeSlot =>
          YulStmt.expr
            (YulExpr.call "sstore" [YulExpr.lit writeSlot, YulExpr.ident "__compat_value"]))
    let compiledIR := [YulStmt.block blockBody]
    let valueNat := SourceSemantics.evalExpr fields runtime value
    have heval :=
      FunctionBody.eval_compileExpr_core_of_scope
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope)
        hruntime
    rw [hvalueIR] at heval
    have hvalueEval : evalIRExpr state valueIR = some valueNat := by
      simpa [valueNat] using heval
    have hbodyFuelLe : slots.length + 2 ≤ extraFuel := by
      have hslack' : sizeOf compiledIR - compiledIR.length ≤ extraFuel := by
        simpa [compiledIR] using hslack
      simp [compiledIR, blockBody, slots] at hslack'
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
    refine ⟨_, _, ?_⟩
    · simp [SourceSemantics.execStmt, hwriteSlots, valueNat, slots]
    · have hbody :
          execIRStmts extraFuel state blockBody =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                      (state.setVar "__compat_value" valueNat).storage
                      slots
                      valueNat } := by
        simpa [hbodyFuelEq, blockBody, slots, bodyExtraFuel] using
          execIRStmts_let_then_sstore_lit_ident_slots_continue
            bodyExtraFuel state slots "__compat_value" valueIR valueNat hvalueEval
      have hwhole :
          execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR =
            .continue
              { state.setVar "__compat_value" valueNat with
                  storage :=
                    abstractStoreStorageOrMappingMany
                    (state.setVar "__compat_value" valueNat).storage
                    slots
                    valueNat } := by
        simpa [compiledIR] using
          execIRStmts_single_block_of_continue
            extraFuel state
            { state.setVar "__compat_value" valueNat with
                storage :=
                  abstractStoreStorageOrMappingMany
                    (state.setVar "__compat_value" valueNat).storage
                    slots
                    valueNat }
            blockBody
            hbody
      simpa using hwhole
    · refine And.intro ?_ <| And.intro ?_ <| And.intro hbounded hscope
      · have hruntimeSet :
            FunctionBody.runtimeStateMatchesIR fields runtime (state.setVar "__compat_value" valueNat) :=
          FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime
        simpa [slots, IRState.setVar] using
          runtimeStateMatchesIR_writeUintSlots hruntimeSet hresolvedSlots hnotAddr hnotDyn
      · have hexactSet :
            FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings
              (state.setVar "__compat_value" valueNat) :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_irrelevant
            hexact (compatValue_not_mem_scope_of_reservedPrefix hscopeReserved)
        simpa [slots, IRState.setVar] using
          bindingsExactlyMatchIRVarsOnScope_writeUintSlots hexactSet

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
      (hvalueIR := hvalueIR)

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_scopeDiscipline
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {prefix suffix : List Stmt}
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
        prefix)
    (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes
    (scope := List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
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
    (hvalueIR := hvalueIR)
  intro name hmem
  have hscopeNames := stmtListScopeDiscipline_scope_names hprefix name hmem
  rw [hbody] at hscopeNames
  simpa [collectStmtListBindNames, collectStmtListAssignedNames, hbody] using hscopeNames

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {prefix suffix : List Stmt}
    {fieldName : String}
    {value : Expr}
    {valueIR : YulExpr}
    {f : Field}
    {slot : Nat}
    (hvalidateShapes : validateIdentifierShapes spec = Except.ok ())
    (hvalidateRefs : validateFunctionIdentifierReferences fn = Except.ok ())
    (hfn : fn ∈ spec.functions)
    (hparamScope : paramScopeNames fn.params = fn.params.map (·.name))
    (hprefixCore : StmtListScopeCore (spec.fields.map (·.name)) prefix)
    (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
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
    (hvalueIR := hvalueIR)

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {prefix suffix : List Stmt}
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
    (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix))
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
        (.setStorage fieldName value)
        compiledIR := by
  apply compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences
    (hvalidateShapes := hvalidateShapes)
    (hvalidateRefs := hvalidateRefs)
    (hfn := hfn)
    (hparamScope := hparamScope)
    (hprefixCore := stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
      (fields := spec.fields)
      (scope := fn.params.map (·.name))
      (prefix := prefix)
      (suffix := .setStorage fieldName value :: suffix)
      (bodyIR := bodyIR)
      (by simpa [hbody] using hbodySurface)
      (by simpa [hbody] using hbodyCompile))
    (hbody := hbody)
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hvalueIR := hvalueIR)

theorem compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList_of_bodySurface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {prefix suffix : List Stmt}
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
    (hbody : fn.body = prefix ++ .setStorage fieldName value :: suffix)
    (hfind : findFieldWithResolvedSlot spec.fields fieldName = some (f, slot))
    (hwriteSlots : findFieldWriteSlots spec.fields fieldName = some (slot :: f.aliasSlots))
    (hunpacked : f.packedBits = none)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none)
    (hnotAddr : SourceSemantics.fieldUsesAddressStorage f = false)
    (hnotDyn : SourceSemantics.fieldUsesDynamicArrayStorage f = false)
    (hvalueIR : CompilationModel.compileExpr spec.fields .calldata value = Except.ok valueIR) :
    ∃ compiledIR,
      CompiledStmtStep spec.fields
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix)
        (.setStorage fieldName value)
        compiledIR := by
  have hprefixCore :
      StmtListScopeCore (spec.fields.map (·.name)) prefix :=
    stmtListScopeCore_prefix_of_compileStmtList_ok_of_stmtListTouchesUnsupportedContractSurface
      (fields := spec.fields)
      (scope := fn.params.map (·.name))
      (prefix := prefix)
      (suffix := .setStorage fieldName value :: suffix)
      (bodyIR := bodyIR)
      (by simpa [hbody] using hbodySurface)
      (by simpa [hbody] using hbodyCompile)
  have hstmtSurface :
      stmtTouchesUnsupportedContractSurface (.setStorage fieldName value) = false := by
    exact
      stmtTouchesUnsupportedContractSurface_of_stmtListTouchesUnsupportedContractSurface_append_cons
        (by simpa [hbody] using hbodySurface)
  have hvalueCore : FunctionBody.ExprCompileCore value :=
    exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false
      (by simpa [stmtTouchesUnsupportedContractSurface] using hstmtSurface)
  have hinScope :
      FunctionBody.exprBoundNamesInScope
        value
        (List.foldl stmtNextScope (fn.params.map (·.name)) prefix) :=
    exprBoundNamesInScope_setStorage_of_validateFunctionIdentifierReferences
      hprefixCore hvalueCore hvalidateRefs hparamScope hbody
  exact compiledStmtStep_setStorage_of_validateIdentifierShapes_of_validateFunctionIdentifierReferences_of_compileStmtList
    (hvalidateShapes := hvalidateShapes)
    (hvalidateRefs := hvalidateRefs)
    (hfn := hfn)
    (hparamScope := hparamScope)
    (hbodySurface := hbodySurface)
    (hbodyCompile := hbodyCompile)
    (hbody := hbody)
    (hcore := hvalueCore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := hwriteSlots)
    (hunpacked := hunpacked)
    (hnoConflict := hnoConflict)
    (hnotAddr := hnotAddr)
    (hnotDyn := hnotDyn)
    (hvalueIR := hvalueIR)

private theorem terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec)
    (hnotContinue : ∀ next, sourceResult ≠ .continue next) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
  case continue runtime =>
    exact False.elim (hnotContinue runtime rfl)

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
      (fields := fields)
      (scope := scope)
      (inScopeNames := scope)
      (stmts := thenBranch)
      hthen with
    ⟨thenIR, hthenIR⟩
  rcases FunctionBody.compileStmtList_terminal_core_ok
      (fields := fields)
      (scope := scope)
      (inScopeNames := scope)
      (stmts := elseBranch)
      helse with
    ⟨elseIR, helseIR⟩
  have helseNonempty : elseBranch.isEmpty = false := by
    cases elseBranch with
    | nil =>
        exfalso
        exact FunctionBody.stmtListTerminalCore_ne_nil helse rfl
    | cons =>
        simp
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
  · unfold compiledIR tempName
    unfold CompilationModel.compileStmt
    rw [hcondIR, hthenIR, helseIR]
    simp [helseNonempty]
  · intro runtime state extraFuel hexact hscope hbounded hruntime hslack
    let slack := sizeOf compiledIR - compiledIR.length
    let wholeExtraFuel := extraFuel - slack
    have hwholeFuel :
        sizeOf compiledIR + wholeExtraFuel + 1 =
          compiledIR.length + extraFuel + 1 := by
      dsimp [wholeExtraFuel, slack, compiledIR]
      have : slack ≤ extraFuel := by
        simpa [slack, compiledIR] using hslack
      omega
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    let condValue := SourceSemantics.evalExpr fields runtime cond
    have hcondEval :
        evalIRExpr state condIR = some condValue := by
      have heval :=
        FunctionBody.eval_compileExpr_core_of_scope
          hcond hexact hinScope hbounded hpresent hruntime
      rw [hcondIR] at heval
      simpa [condValue] using heval
    by_cases hcondZero : condValue = 0
    · let branchExtraFuel :=
        sizeOf compiledIR - (sizeOf elseIR + 5) + wholeExtraFuel
      rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
          (fields := fields)
          (runtime := runtime)
          (state := state.setVar tempName condValue)
          (scope := scope)
          (inScopeNames := scope)
          (stmts := elseBranch)
          (extraFuel := branchExtraFuel)
          helse
          FunctionBody.scopeNamesIncluded_refl
          hscope
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope)
            (inScopeNames := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (value := condValue)
            hexact
            FunctionBody.scopeNamesIncluded_refl)
          hbounded
          (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
        ⟨elseIR', helseIR', helseSem⟩
      rw [helseIR] at helseIR'
      injection helseIR' with helseEq
      subst helseEq
      have hsourceEq :
          SourceSemantics.execStmtList fields runtime
            (.ite cond thenBranch elseBranch :: []) =
            SourceSemantics.execStmtList fields runtime elseBranch :=
        FunctionBody.execStmtList_terminal_core_ite_else_eq
          (fields := fields)
          (runtime := runtime)
          (scope := scope)
          (cond := cond)
          (thenBranch := thenBranch)
          (elseBranch := elseBranch)
          (rest := [])
          helse
          (by simp [condValue, hcondZero])
      have hbodyMatch :
          FunctionBody.stmtResultMatchesIRExec
            fields
            (SourceSemantics.execStmtList fields runtime elseBranch)
            (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
        have hmatch :=
          FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_else
            (fields := fields)
            (runtime := runtime)
            (state := state)
            (scope := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (rest := [])
            (extraFuel := wholeExtraFuel)
            (tempName := tempName)
            (condIR := condIR)
            (thenIR := thenIR)
            (elseIR := elseIR)
            (tailIR := [])
            (condValue := condValue)
            (irExec := execIRStmts
              (sizeOf elseIR + branchExtraFuel)
              (state.setVar tempName condValue)
              elseIR)
            helse
            helseSem
            (by simp [condValue, hcondZero])
            hcondEval
            hcondZero
            (by
              simpa [compiledIR, branchExtraFuel, tempName, condValue] using rfl)
        rw [hsourceEq] at hmatch
        simpa [hwholeFuel, compiledIR] using hmatch
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, condValue, hcondZero]
      · rfl
      · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
          hbodyMatch
          (FunctionBody.execStmtList_terminal_core_not_continue
            (fields := fields)
            (runtime := runtime)
            (scope := scope)
            (stmts := elseBranch)
            helse)
    · let branchExtraFuel :=
        sizeOf compiledIR - (sizeOf thenIR + 5) + wholeExtraFuel
      rcases FunctionBody.exec_compileStmtList_terminal_core_sizeOf_extraFuel
          (fields := fields)
          (runtime := runtime)
          (state := state.setVar tempName condValue)
          (scope := scope)
          (inScopeNames := scope)
          (stmts := thenBranch)
          (extraFuel := branchExtraFuel)
          hthen
          FunctionBody.scopeNamesIncluded_refl
          hscope
          (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setCompiledTerminalIteTemp_irrelevant
            (scope := scope)
            (inScopeNames := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (value := condValue)
            hexact
            FunctionBody.scopeNamesIncluded_refl)
          hbounded
          (FunctionBody.runtimeStateMatchesIR_setVar_irrelevant hruntime) with
        ⟨thenIR', hthenIR', hthenSem⟩
      rw [hthenIR] at hthenIR'
      injection hthenIR' with hthenEq
      subst hthenEq
      have hsourceEq :
          SourceSemantics.execStmtList fields runtime
            (.ite cond thenBranch elseBranch :: []) =
            SourceSemantics.execStmtList fields runtime thenBranch :=
        FunctionBody.execStmtList_terminal_core_ite_then_eq
          (fields := fields)
          (runtime := runtime)
          (scope := scope)
          (cond := cond)
          (thenBranch := thenBranch)
          (elseBranch := elseBranch)
          (rest := [])
          hthen
          (by simp [condValue, hcondZero])
      have hbodyMatch :
          FunctionBody.stmtResultMatchesIRExec
            fields
            (SourceSemantics.execStmtList fields runtime thenBranch)
            (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR) := by
        have hmatch :=
          FunctionBody.stmtResultMatchesIRExec_compiled_terminal_ite_then
            (fields := fields)
            (runtime := runtime)
            (state := state)
            (scope := scope)
            (cond := cond)
            (thenBranch := thenBranch)
            (elseBranch := elseBranch)
            (rest := [])
            (extraFuel := wholeExtraFuel)
            (tempName := tempName)
            (condIR := condIR)
            (thenIR := thenIR)
            (elseIR := elseIR)
            (tailIR := [])
            (condValue := condValue)
            (irExec := execIRStmts
              (sizeOf thenIR + branchExtraFuel + 1)
              (state.setVar tempName condValue)
              thenIR)
            hthen
            hthenSem
            (by simp [condValue, hcondZero])
            hcondEval
            (by
              intro hzero
              exact hcondZero hzero)
            (by
              simpa [compiledIR, branchExtraFuel, tempName, condValue, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm] using rfl)
        rw [hsourceEq] at hmatch
        simpa [hwholeFuel, compiledIR] using hmatch
      refine ⟨_, _, ?_⟩
      · simp [SourceSemantics.execStmt, condValue, hcondZero]
      · rfl
      · exact terminal_stmtResultMatchesIRExec_implies_stmtStepMatchesIRExec
          hbodyMatch
          (FunctionBody.execStmtList_terminal_core_not_continue
            (fields := fields)
            (runtime := runtime)
            (scope := scope)
            (stmts := thenBranch)
            hthen)

private theorem stmtListTouchesUnsupportedContractSurface_append
    {prefix suffix : List Stmt} :
    stmtListTouchesUnsupportedContractSurface (prefix ++ suffix) =
      (stmtListTouchesUnsupportedContractSurface prefix ||
        stmtListTouchesUnsupportedContractSurface suffix) := by
  induction prefix with
  | nil =>
      simp [stmtListTouchesUnsupportedContractSurface]
  | cons stmt rest ih =>
      simp [stmtListTouchesUnsupportedContractSurface, ih, Bool.or_assoc]

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
            cases family <;> repeat constructor
      · intro name hmem
        cases clause with
        | mk family n m p q message =>
            cases family <;> simp [Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
              FunctionBody.exprBoundNames] at hmem

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
          cases family <;>
            simp [stmtNextScope, Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt,
              collectStmtNames, ih]

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
  refine StmtListGenericCore.cons ?_ StmtListGenericCore.nil
  exact compiledStmtStep_setStorage_singleSlot
    (hcore := hcore)
    (hinScope := hinScope)
    (hfind := hfind)
    (hwriteSlots := by simpa [findFieldWriteSlots, hfind])
    (halias := by rfl)
    (hunpacked := by rfl)
    (hnoConflict := hnoConflict)
    (hnotAddr := by rfl)
    (hnotDyn := by rfl)
    (hvalueIR := hvalueIR)

private theorem stmtListGenericCore_of_requireClausesOnly
    {fields : List Field}
    {scope : List String}
    (clauses : List Verity.Core.Free.RequireLiteralGuardFamilyClause) :
    StmtListGenericCore fields scope
      (clauses.map Verity.Core.Free.RequireLiteralGuardFamilyClause.toStmt) :=
  stmtListGenericCore_of_stmtListCompileCore
    (fields := fields)
    (scope := scope)
    (stmtListCompileCore_of_requireLiteralGuardFamilyClauses (scope := scope) clauses)

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
  exact stmtListGenericCore_append
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
      · exact .localVar tmp
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem
        simpa [hmem]
      · exact FunctionBody.StmtListCompileCore.nil
  exact stmtListGenericCore_append
    (stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses)
    (by
      simpa [foldl_stmtNextScope_requireLiteralGuardFamilyClauses (scope := scope) clauses] using
        (stmtListGenericCore_of_stmtListCompileCore (fields := fields) (scope := scope) htail))

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
              simpa using hmem))))

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
              simpa using hmem))))

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
    · refine FunctionBody.StmtListCompileCore.assignVar (.add (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
      · exact .add (.localVar tmp) (.literal m)
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem ⊢
        simpa using hmem
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
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              simpa using hmem))))

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
    · refine FunctionBody.StmtListCompileCore.assignVar (.sub (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
      · exact .sub (.localVar tmp) (.literal m)
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem ⊢
        simpa using hmem
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
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              simpa using hmem))))

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
    · refine FunctionBody.StmtListCompileCore.assignVar (.mul (Expr.localVar tmp) (Expr.literal m)) ?_ ?_
      · exact .mul (.localVar tmp) (.literal m)
      · intro name hmem
        simp [FunctionBody.exprBoundNames] at hmem ⊢
        simpa using hmem
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
              [Stmt.letVar tmp (Expr.literal n),
               Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))])
            (hnoConflict := hnoConflict)
            (hfind := hfind)
            (hcore := .localVar tmp)
            (hinScope := by
              intro name hmem
              simp [stmtNextScope, collectStmtNames, FunctionBody.exprBoundNames] at hmem ⊢
              simpa using hmem))))

private theorem stmtListGenericCore_of_supportedStmtFragment_of_surface
    {fields : List Field}
    {scope : List String}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (fragment : Verity.Core.Free.SupportedStmtFragment fields)
    (hsurface :
      stmtListTouchesUnsupportedContractSurface
        (Verity.Core.Free.SupportedStmtFragment.toStmts fragment) = false) :
    StmtListGenericCore fields scope
      (Verity.Core.Free.SupportedStmtFragment.toStmts fragment) := by
  cases fragment <;>
    simp [Verity.Core.Free.SupportedStmtFragment.toStmts,
      Verity.Core.Free.RequireFamilyClausesTailProgram.toStmts,
      Verity.Core.Free.RequireFamilyClausesTail.toStmts] at hsurface ⊢
  · exact stmtListGenericCore_of_requireClausesOnly (fields := fields) (scope := scope) clauses
  · exact stmtListGenericCore_of_requireClausesThenSetStorageLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName slot writeVal hfind
  · exact stmtListGenericCore_of_requireClausesThenReturnLiteral
      (fields := fields) (scope := scope) clauses retVal
  · exact stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral
      (fields := fields) (scope := scope) clauses tmp retVal
  · exact stmtListGenericCore_of_requireClausesThenLetSetStorageLocalLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName tmp slot n hfind
  · exact stmtListGenericCore_of_requireClausesThenLetAssignSetStorageLocalLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName tmp slot n m hfind
  · exact stmtListGenericCore_of_requireClausesThenLetAssignAddSetStorageLocalLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName tmp slot n m hfind
  · exact stmtListGenericCore_of_requireClausesThenLetAssignSubSetStorageLocalLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName tmp slot n m hfind
  · exact stmtListGenericCore_of_requireClausesThenLetAssignMulSetStorageLocalLiteral
      (fields := fields) (scope := scope) hnoConflict clauses fieldName tmp slot n m hfind
  all_goals
    cases hsurface

theorem stmtListGenericCore_of_supportedStmtList_of_surface
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hnoConflict : firstFieldWriteSlotConflict fields = none)
    (hSupported : SupportedStmtList fields stmts)
    (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false) :
    StmtListGenericCore fields scope stmts := by
  induction hSupported generalizing scope with
  | nil =>
      simpa using (StmtListGenericCore.nil (fields := fields) (scope := scope))
  | @cons fragment rest htail ih =>
      have hsplit :
          stmtListTouchesUnsupportedContractSurface
              (Verity.Core.Free.SupportedStmtFragment.toStmts fragment) ||
            stmtListTouchesUnsupportedContractSurface rest = false := by
        simpa [stmtListTouchesUnsupportedContractSurface_append] using hsurface
      have hheadSurface :
          stmtListTouchesUnsupportedContractSurface
            (Verity.Core.Free.SupportedStmtFragment.toStmts fragment) = false :=
        (Bool.or_eq_false.mp hsplit).1
      have htailSurface :
          stmtListTouchesUnsupportedContractSurface rest = false :=
        (Bool.or_eq_false.mp hsplit).2
      exact stmtListGenericCore_append
        (stmtListGenericCore_of_supportedStmtFragment_of_surface
          (fields := fields)
          (scope := scope)
          hnoConflict
          fragment
          hheadSurface)
        (ih
          (scope := List.foldl stmtNextScope scope
            (Verity.Core.Free.SupportedStmtFragment.toStmts fragment))
          htailSurface)

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
    (hSupported : SupportedStmtList fields stmts)
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

/-- The supported-body interface also derives the weaker source-side reuse
witness needed by the exact helper-aware seam: helper-free heads retain the
legacy generic-step obligation, while helper-positive heads can be discharged
separately. -/
theorem SupportedBodyInterface.helperFreeStepInterface
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hBody : SupportedBodyInterface spec fn)
    (hnoConflict : firstFieldWriteSlotConflict spec.fields = none) :
    StmtListHelperFreeStepInterface spec.fields (fn.params.map (·.name)) fn.body :=
  stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface
    (fields := spec.fields)
    (scope := fn.params.map (·.name))
    (stmts := fn.body)
    hnoConflict
    hBody.stmtList
    hBody.surfaceClosed

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
    StmtListGenericCore fields largerScope stmts := by
  induction hcore generalizing largerScope with
  | nil =>
      exact StmtListGenericCore.nil
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
          hthen helse with
        ⟨compiledIR, hstep⟩
      exact StmtListGenericCore.cons hstep
        (stmtListGenericCore_of_stmtListCompileCore_of_scopeNamesIncluded
          hrest
          (FunctionBody.scopeNamesIncluded_collectStmtNames_tail
            (stmt := .ite _ _ _) hincluded))

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
    {prefix suffix : List Stmt}
    (hprefix : StmtListGenericCore fields scope prefix)
    (hsuffix :
      StmtListGenericCore
        fields
        (List.foldl stmtNextScope scope prefix)
        suffix) :
    StmtListGenericCore fields scope (prefix ++ suffix) := by
  induction hprefix generalizing suffix with
  | nil =>
      simpa using hsuffix
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp
      exact StmtListGenericCore.cons hstep (ih hsuffix)

private theorem scopeNamesIncluded_foldl_stmtNextScope
    {scope : List String}
    {stmts : List Stmt} :
    FunctionBody.scopeNamesIncluded scope (List.foldl stmtNextScope scope stmts) := by
  induction stmts generalizing scope with
  | nil =>
      simpa using FunctionBody.scopeNamesIncluded_refl
  | cons stmt rest ih =>
      exact
        FunctionBody.scopeNamesIncluded_collectStmtNames_tail
          (ih (scope := stmtNextScope scope stmt))

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
  | nil =>
      exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases ih
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (scopeNamesIncluded_stmtNextScope hincluded) with
        ⟨tailIR, htail⟩
      refine ⟨compiledIR ++ tailIR, ?_⟩
      exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
        hstep.compileOk htail

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
  | nil =>
      exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases ih
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (scopeNamesIncluded_stmtNextScope hincluded) with
        ⟨tailIR, htail⟩
      refine ⟨compiledIR ++ tailIR, ?_⟩
      exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
        hstep.compileOk htail

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
  | nil =>
      exact ⟨[], by simp [CompilationModel.compileStmtList]⟩
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      rcases ih
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (scopeNamesIncluded_stmtNextScope hincluded) with
        ⟨tailIR, htail⟩
      refine ⟨compiledIR ++ tailIR, ?_⟩
      exact FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok
        hstep.compileOk htail

theorem stmtStepMatchesIRExec_of_included
    {fields : List Field}
    {scope largerScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields largerScope sourceResult irExec)
    (hincluded : FunctionBody.scopeNamesIncluded scope largerScope) :
    stmtStepMatchesIRExec fields scope sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch ⊢
  case continue runtime state =>
    rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
    exact ⟨hruntime,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
      hbounded,
      FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩

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
  case continue runtime state =>
    rcases hmatch with ⟨hruntime, hexact, hbounded, hscope⟩
    exact ⟨hruntime,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hincluded,
      hbounded,
      FunctionBody.scopeNamesPresent_of_included hscope hincluded⟩

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
    simp [stmtStepMatchesIRExecWithInternals, stmtResultMatchesIRExecWithInternals] at hmatch ⊢ <;>
    simp [stmtResultMatchesIRExecWithInternals, hmatch]

private theorem yulStmtList_sizeOf_append_left_le
    (head tail : List YulStmt) :
    sizeOf head ≤ sizeOf (head ++ tail) := by
  induction head with
  | nil =>
      simp
  | cons stmt rest ih =>
      simp [List.cons_append]
      omega

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
      simp at hhead
      subst hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmts] at hhead
      | succ fuel =>
          simp [execIRStmts] at hhead ⊢
          cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead
          case continue next' =>
            simpa using ih fuel next' hhead

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
      simp at hhead
      subst hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmts] at hhead ⊢
      | succ fuel =>
          simp [execIRStmts] at hhead ⊢
          cases hstmt : execIRStmt fuel state stmt <;> simp [hstmt] at hhead ⊢
          case continue next' =>
            exact ih fuel next' hhead hnot
          case return value state' =>
            cases hhead
            simp [execIRStmts, hstmt]

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
      simp at hhead
      subst hhead
      simp
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals] at hhead
      | succ fuel =>
          simp [execIRStmtsWithInternals] at hhead ⊢
          cases hstmt : execIRStmtWithInternals runtimeContract fuel state stmt <;>
            simp [hstmt] at hhead
          case continue next' =>
            simpa using ih fuel next' hhead

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
      simp at hhead
      subst hhead
      exact False.elim (hnot state rfl)
  | cons stmt rest ih =>
      cases fuel with
      | zero =>
          simp [execIRStmtsWithInternals] at hhead ⊢
      | succ fuel =>
          simp [execIRStmtsWithInternals] at hhead ⊢
          cases hstmt : execIRStmtWithInternals runtimeContract fuel state stmt <;>
            simp [hstmt] at hhead ⊢
          case continue next' =>
            exact ih fuel next' hhead hnot
          case return value state' =>
            cases hhead
            simp [execIRStmtsWithInternals, hstmt]
          case stop state' =>
            cases hhead
            simp [execIRStmtsWithInternals, hstmt]
          case revert state' =>
            cases hhead
            simp [execIRStmtsWithInternals, hstmt]
          case leave state' =>
            cases hhead
            simp [execIRStmtsWithInternals, hstmt]
          case stop state' =>
            cases hhead
            simp [execIRStmts, hstmt]
          case revert state' =>
            cases hhead
            simp [execIRStmts, hstmt]

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
  induction hgeneric generalizing runtime state inScopeNames extraFuel with
  | nil =>
      refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
      exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      have hnextIncluded :
          FunctionBody.scopeNamesIncluded
            (stmtNextScope scope stmt)
            (collectStmtNames stmt ++ inScopeNames) :=
        scopeNamesIncluded_stmtNextScope hincluded
      rcases ih
          (runtime := runtime)
          (state := state)
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (extraFuel := 0)
          hnextIncluded hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
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
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (inScopeNames := collectStmtNames stmt ++ inScopeNames)
            (extraFuel := tailExtraFuel')
            hnextIncluded hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          rw [execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec']
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
  induction hgeneric generalizing runtime state inScopeNames extraFuel with
  | nil =>
      refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
      exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      have hnextIncluded :
          FunctionBody.scopeNamesIncluded
            (stmtNextScope scope stmt)
            (collectStmtNames stmt ++ inScopeNames) :=
        scopeNamesIncluded_stmtNextScope hincluded
      rcases ih
          (runtime := runtime)
          (state := state)
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (extraFuel := 0)
          hnextIncluded hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
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
      cases sourceHead <;> cases irHead <;> simp [stmtStepMatchesIRExec] at hheadMatch
      ·
        rcases hheadMatch with ⟨hruntime', hexact', hbounded', hscope'⟩
        let tailExtraFuel' :=
          sizeOf bodyIR - compiledIR.length - sizeOf tailIR + extraFuel
        have htailSem' :=
          ih
            (runtime := _)
            (state := _)
            (inScopeNames := collectStmtNames stmt ++ inScopeNames)
            (extraFuel := tailExtraFuel')
            hnextIncluded hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state compiledIR =
              .continue ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmts (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmts (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          rw [execIRStmts_append_of_continue
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec']
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
          simpa [headExtraFuel, bodyIR] using hheadExec
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
  induction hgeneric generalizing runtime state inScopeNames extraFuel with
  | nil =>
      refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
      exact And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      have hnextIncluded :
          FunctionBody.scopeNamesIncluded
            (stmtNextScope scope stmt)
            (collectStmtNames stmt ++ inScopeNames) :=
        scopeNamesIncluded_stmtNextScope hincluded
      rcases ih
          (runtime := runtime)
          (state := state)
          (inScopeNames := collectStmtNames stmt ++ inScopeNames)
          (extraFuel := 0)
          hnextIncluded hscope hexact hbounded hruntime with
        ⟨tailIR, htailCompile, htailSem⟩
      let bodyIR := compiledIR ++ tailIR
      have hbodyCompile :
          CompilationModel.compileStmtList
            fields [] [] .calldata [] false inScopeNames (stmt :: rest) =
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
            (inScopeNames := collectStmtNames stmt ++ inScopeNames)
            (extraFuel := tailExtraFuel')
            hfuelPos hnextIncluded hscope' hexact' hbounded' hruntime'
        rcases htailSem' with ⟨tailIR', htailCompile', htailSem''⟩
        rw [htailCompile] at htailCompile'
        injection htailCompile' with htailEq
        subst htailEq
        have hheadExec' :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .continue ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
              execIRStmtsWithInternals runtimeContract
                (sizeOf tailIR + tailExtraFuel' + 1) ‹IRState› tailIR := by
          rw [execIRStmtsWithInternals_append_of_continue
              (runtimeContract := runtimeContract)
              (fuel := sizeOf bodyIR + extraFuel + 1)
              (state := state)
              (next := ‹IRState›)
              (head := compiledIR)
              (tail := tailIR)
              hheadExec']
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
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .stop ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            (runtimeContract := runtimeContract)
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
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .return ‹Nat› ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .return ‹Nat› ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            (runtimeContract := runtimeContract)
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
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state compiledIR =
                .revert ‹IRState› := by
          simpa [headExtraFuel, bodyIR] using hheadExec
        have hfullExec :
            execIRStmtsWithInternals runtimeContract
              (sizeOf bodyIR + extraFuel + 1) state bodyIR =
                .revert ‹IRState› := by
          exact execIRStmtsWithInternals_append_of_not_continue
            (runtimeContract := runtimeContract)
            (fuel := sizeOf bodyIR + extraFuel + 1)
            (state := state)
            (head := compiledIR)
            (tail := tailIR)
            (irExec := .revert ‹IRState›)
            hheadExec'
            (by intro next hcontra; simp at hcontra)
        rw [SourceSemantics.execStmtListWithHelpers, hsourceHead]
        rw [hfullExec]
        simp [stmtStepMatchesIRExecWithInternals]

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
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_sizeOf_extraFuel_step
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (runtime := runtime)
      (state := state)
      (scope := scope)
      (inScopeNames := inScopeNames)
      (stmts := stmts)
      (helperFuel := helperFuel)
      (extraFuel := extraFuel)
      hfuelPos
      hgeneric
      hincluded
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
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (extraFuel := sizeSlack)
      hgeneric
      FunctionBody.scopeNamesIncluded_refl
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
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simpa [hfuel] using rfl
  · simpa [hfuel, sizeSlack] using hgenericSem

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
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hgeneric
      FunctionBody.scopeNamesIncluded_refl
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
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simpa [hfuel] using rfl
  · simpa [hfuel, sizeSlack] using hgenericSem

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
      (inScopeNames := fn.params.map (·.name))
      (stmts := fn.body)
      (helperFuel := helperFuel)
      (extraFuel := sizeSlack)
      hfuelPos
      hgeneric
      FunctionBody.scopeNamesIncluded_refl
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
  have hfuel :
      sizeOf bodyStmts + sizeSlack + 1 =
        bodyStmts.length + extraFuel + 1 := by
    dsimp [sizeSlack]
    omega
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simpa [hfuel] using rfl
  · simpa [hfuel, sizeSlack] using hgenericSem

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

/-- The current helper-free compiled-body goal is a conservative special case of
the exact helper-aware compiled-body target whenever the runtime contract has no
internal helper table and the compiled body stays inside the already-closed
legacy-compatible external Yul subset. -/
theorem supported_function_body_with_helpers_and_helper_ir_goal_of_legacy_ir_goal
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
    (hlegacyBody : LegacyCompatibleExternalStmtList bodyStmts)
    (hinternal : runtimeContract.internalFunctions = []) :
    SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
      runtimeContract
      model fn bodyStmts helperFuel tx initialWorld state bindings extraFuel := by
  rcases hbody with ⟨sourceResult, irExec, hsource, hbodyExec, hmatch⟩
  refine ⟨sourceResult, match irExec with
      | .continue next => .continue next
      | .return value next => .return value next
      | .stop next => .stop next
      | .revert next => .revert next, hsource, ?_, ?_⟩
  · have hcompat :=
      execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility runtimeContract
        (execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals
          runtimeContract
          (interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed
            runtimeContract))
        hinternal
        (bodyStmts.length + extraFuel + 1)
        state
        bodyStmts
        hlegacyBody
    simpa [hbodyExec] using hcompat
  · cases irExec <;> simpa [stmtResultMatchesIRExecWithInternals] using hmatch

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
  refine ⟨sourceResult, match irExec with
      | .continue next => .continue next
      | .return value next => .return value next
      | .stop next => .stop next
      | .revert next => .revert next, hsource, ?_, ?_⟩
  · have hcompat :=
      execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
        (bodyStmts.length + extraFuel + 1)
        state
        bodyStmts
        hdisjoint
    simpa [hbodyExec] using hcompat
  · cases irExec <;> simpa [stmtResultMatchesIRExecWithInternals] using hmatch

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
    (hhelperSurface : stmtListTouchesUnsupportedHelperSurface fn.body = false)
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
  have hlegacy :
      StmtListHelperFreeCompiledLegacyCompatible
        (SourceSemantics.effectiveFields model)
        (fn.params.map (·.name))
        fn.body := by
    simpa [hnormalized] using
      (stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface
        (fields := model.fields)
        (scope := fn.params.map (·.name))
        (stmts := fn.body)
        hnoPacked
        hcontractSurface)
  exact
    supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir
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
      hlegacy
      hbodyCompile
      hscope hbounded hstateRuntime hstateBindings hinternal

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
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]
  have hshape' : compiledIR = singletonIR := by
    simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by
    simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by
      simp [singletonIR]
      omega
    rw [hshape'] at hslack
    rw [hlenOne] at hslack
    omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]
    omega
  refine ⟨_, _, ?_, ?_, ?_⟩
  · exact SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
      (Stmt.internalCallAssign names calleeName args)
  · exact execIRStmtsWithInternals runtimeContract (compiledIR.length + extraFuel + 1) state compiledIR
  · rfl
  · rw [hshape', hFuelEq]
  · simpa [singletonIR] using hMatch

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
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]
  have hshape' : compiledIR = singletonIR := by
    simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by
    simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by
      simp [singletonIR]
      omega
    rw [hshape'] at hslack
    rw [hlenOne] at hslack
    omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]
    omega
  refine ⟨_, _, ?_, ?_, ?_⟩
  · exact SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
      (Stmt.internalCall calleeName args)
  · exact execIRStmtsWithInternals runtimeContract (compiledIR.length + extraFuel + 1) state compiledIR
  · rfl
  · rw [hshape', hFuelEq]
  · simpa [singletonIR] using hMatch

end Compiler.Proofs.IRGeneration
