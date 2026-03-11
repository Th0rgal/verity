import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.FunctionBody

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Scope seen by the tail after compiling a single statement. This matches the
statement-list compiler's `collectStmtNames` update. -/
def stmtNextScope (scope : List String) (stmt : Stmt) : List String :=
  collectStmtNames stmt ++ scope

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
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .revert, .revert _ => True
  | _, _ => False

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

/-- Statement lists whose heads all admit a generic compiled-step proof. -/
inductive StmtListGenericCore (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericCore fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStep fields scope stmt compiledIR →
      StmtListGenericCore fields (stmtNextScope scope stmt) rest →
      StmtListGenericCore fields scope (stmt :: rest)

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
    · refine ⟨rfl, ?_, hexact, hbounded, hscope⟩
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
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using
        And.intro hruntime <| And.intro hexact <| And.intro hbounded hscope

end Compiler.Proofs.IRGeneration
