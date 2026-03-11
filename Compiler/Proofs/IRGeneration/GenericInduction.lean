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

theorem stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec
    {fields : List Field}
    {scope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields scope sourceResult irExec) :
    FunctionBody.stmtResultMatchesIRExec fields sourceResult irExec := by
  cases sourceResult <;> cases irExec <;> simp [stmtStepMatchesIRExec] at hmatch <;>
    simp [FunctionBody.stmtResultMatchesIRExec, hmatch]

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
          case stop state' =>
            cases hhead
            simp [execIRStmts, hstmt]
          case revert state' =>
            cases hhead
            simp [execIRStmts, hstmt]

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
  induction hgeneric generalizing runtime state inScopeNames extraFuel with
  | nil =>
      refine ⟨[], by simp [CompilationModel.compileStmtList], ?_⟩
      simp [SourceSemantics.execStmtList, FunctionBody.stmtResultMatchesIRExec, hruntime]
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
        simpa [tailExtraFuel', bodyIR] using htailSem''
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
        exact stmtStepMatchesIRExec_implies_stmtResultMatchesIRExec hheadMatch
      ·
        rcases hheadMatch with ⟨rfl, hruntime', _, _, _⟩
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
        simp [FunctionBody.stmtResultMatchesIRExec]

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

end Compiler.Proofs.IRGeneration
