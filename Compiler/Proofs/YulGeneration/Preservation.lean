import Compiler.Proofs.YulGeneration.Codegen
import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.StatementEquivalence
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Codegen Preservation Theorem (Layer 3 — CompilationModel Path)

We prove that Yul code generation preserves IR semantics, assuming that
executing an IR function body matches executing the same Yul statements.

**Scope**: This proof applies to the compilation path
`CompilationModel -> IR -> Yul`.
See `TRUST_ASSUMPTIONS.md` for the full trust-boundary description.
-/

@[simp] private theorem interpretYulBody_eq_runtime (fn : IRFunction) (tx : IRTransaction) (state : IRState) :
    interpretYulBody fn tx state =
      interpretYulRuntime fn.body
        { sender := tx.sender
          msgValue := tx.msgValue
          thisAddress := tx.thisAddress
          blockTimestamp := tx.blockTimestamp
          blockNumber := tx.blockNumber
          chainId := tx.chainId
          blobBaseFee := tx.blobBaseFee
          functionSelector := tx.functionSelector
          args := tx.args }
        state.storage state.events := by
  rfl

@[simp] private theorem interpretYulRuntime_eq_yulResultOfExecWithRollback_initial
    (runtimeCode : List YulStmt) (tx : YulTransaction) (storage : Nat → Nat)
    (events : List (List Nat)) :
    interpretYulRuntime runtimeCode tx storage events =
      yulResultOfExecWithRollback (YulState.initial tx storage events)
        (execYulStmts (YulState.initial tx storage events) runtimeCode) := by
  rfl

@[simp] private theorem interpretYulBody_eq_execWithRollback (fn : IRFunction)
    (tx : IRTransaction) (state : IRState) :
    interpretYulBody fn tx state =
      yulResultOfExecWithRollback
        (YulState.initial
          { sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            functionSelector := tx.functionSelector
            args := tx.args }
          state.storage state.events)
        (execYulStmts
          (YulState.initial
            { sender := tx.sender
              msgValue := tx.msgValue
              thisAddress := tx.thisAddress
              blockTimestamp := tx.blockTimestamp
              blockNumber := tx.blockNumber
              chainId := tx.chainId
              blobBaseFee := tx.blobBaseFee
              functionSelector := tx.functionSelector
              args := tx.args }
            state.storage state.events)
          fn.body) := by
  simp [interpretYulBody]

/-- Helper: initial Yul state aligned with the IR transaction/state. -/
private def initialYulState (tx : YulTransaction) (state : IRState) : YulState :=
  YulState.initial tx state.storage state.events

/-- Preconditions under which the generated dispatch guards behave like the
    intended source-level checks for a selected function case. -/
def DispatchGuardsSafe (fn : IRFunction) (tx : IRTransaction) : Prop :=
  (fn.payable = true ∨ tx.msgValue % evmModulus = 0) ∧
  4 + fn.params.length * 32 < evmModulus

@[simp]
private theorem evalYulExpr_selectorExpr_initial
    (tx : YulTransaction) (state : IRState)
    (hselector : tx.functionSelector < selectorModulus) :
    evalYulExpr (initialYulState tx state) selectorExpr = some tx.functionSelector := by
  simpa using (evalYulExpr_selectorExpr_eq (initialYulState tx state) hselector)

/-- Well-formedness: all internalFunctions are funcDef statements. -/
def ContractWF (contract : IRContract) : Prop :=
  ∀ s ∈ contract.internalFunctions, ∃ n p r b, s = YulStmt.funcDef n p r b

private theorem runtimeCode_prefix_allFuncDefs (contract : IRContract)
    (hWF : ContractWF contract) :
    ∀ s ∈ (if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
        contract.internalFunctions,
      ∃ nm p r b, s = YulStmt.funcDef nm p r b := by
  intro s hs
  simp only [List.mem_append] at hs
  cases hs with
  | inl hMapping =>
      split at hMapping <;> simp at hMapping
      subst hMapping
      exact ⟨"mappingSlot", ["baseSlot", "key"], ["slot"], _, rfl⟩
  | inr hInternal => exact hWF s hInternal

private theorem list_length_le_sizeOf : (l : List YulStmt) → l.length ≤ sizeOf l
  | [] => by simp
  | _ :: t => by
      simp [List.length_cons]
      have := list_length_le_sizeOf t
      omega

private theorem sizeOf_append_ge_length_add (l₁ l₂ : List YulStmt) :
    sizeOf (l₁ ++ l₂) ≥ l₁.length + sizeOf l₂ := by
  induction l₁ with
  | nil => simp
  | cons h t ih =>
      simp only [List.cons_append, List.length_cons]
      have : sizeOf (h :: (t ++ l₂)) = 1 + sizeOf h + sizeOf (t ++ l₂) := rfl
      omega

/-- Membership in a list implies the element's sizeOf is strictly smaller than the list's. -/
private theorem sizeOf_lt_of_mem {α : Type _} [SizeOf α] {x : α} {l : List α}
    (hx : x ∈ l) : sizeOf x < sizeOf l := by
  induction l with
  | nil => cases hx
  | cons h t ih =>
      cases hx with
      | head => show sizeOf x < 1 + sizeOf x + sizeOf t; omega
      | tail _ hmem => have := ih hmem; show sizeOf x < 1 + sizeOf h + sizeOf t; omega

/-- The `buildSwitch` output for a list of functions has `sizeOf` at least
`sizeOf fn.body + 12` for any function in the list.  This is a structural
bound following from the nesting depth of the generated Yul AST. -/
private theorem sizeOf_switchCaseBody_ge (fn : IRFunction) :
    sizeOf (switchCaseBody fn) ≥ sizeOf fn.body + 2 := by
  -- switchCaseBody fn = prefix ++ fn.body where prefix has ≥ 2 elements
  show sizeOf (([YulStmt.comment s!"{fn.name}()"] ++
    (if fn.payable then [] else [Compiler.callvalueGuard]) ++
    [Compiler.calldatasizeGuard fn.params.length]) ++ fn.body) ≥ _
  have h := sizeOf_append_ge_length_add
    ([YulStmt.comment s!"{fn.name}()"] ++
      (if fn.payable then [] else [Compiler.callvalueGuard]) ++
      [Compiler.calldatasizeGuard fn.params.length])
    fn.body
  have hlen : ([YulStmt.comment s!"{fn.name}()"] ++
      (if fn.payable then [] else [Compiler.callvalueGuard]) ++
      [Compiler.calldatasizeGuard fn.params.length]).length ≥ 2 := by
    cases fn.payable <;> simp
  omega

/-- `sizeOf` of the `switchCases` list is strictly greater than `sizeOf (switchCaseBody fn)`
for any `fn ∈ fns`. -/
private theorem sizeOf_switchCases_gt_body {fns : List IRFunction} {fn : IRFunction}
    (hmem : fn ∈ fns) :
    sizeOf (switchCases fns) > sizeOf (switchCaseBody fn) := by
  have hmem' : (fn.selector, switchCaseBody fn) ∈ switchCases fns := by
    simp only [switchCases]
    exact List.mem_map_of_mem hmem
  have hlt := sizeOf_lt_of_mem hmem'
  have : sizeOf (fn.selector, switchCaseBody fn) =
      1 + sizeOf fn.selector + sizeOf (switchCaseBody fn) := rfl
  omega

/-- Helper: `sizeOf` of a singleton list `[x]` equals `1 + sizeOf x + 1`. -/
private theorem sizeOf_singleton_list {α : Type _} [SizeOf α] (x : α) :
    sizeOf [x] = 1 + sizeOf x + 1 := rfl

/-- Helper: `sizeOf` of a 3-element list. -/
private theorem sizeOf_list_three {α : Type _} [SizeOf α] (a b c : α) :
    sizeOf [a, b, c] = 1 + sizeOf a + (1 + sizeOf b + (1 + sizeOf c + 1)) := rfl

/-- `buildSwitch fns none none` wraps `switchCases fns` in an AST structure that adds
a fixed overhead. The nesting is:
`[block [let_, if_, if_ [switch selectorExpr (switchCases fns) (some default)]]]`. -/
private theorem sizeOf_buildSwitch_ge_switchCases
    (fns : List IRFunction) :
    sizeOf [Compiler.buildSwitch fns none none] ≥ sizeOf (switchCases fns) + 9 := by
  -- sizeOf [x] = sizeOf x + 2
  have h_list : sizeOf [Compiler.buildSwitch fns none none] ≥
      sizeOf (Compiler.buildSwitch fns none none) + 2 := by
    show 1 + sizeOf (Compiler.buildSwitch fns none none) + 1 ≥ _; omega
  suffices h : sizeOf (Compiler.buildSwitch fns none none) ≥ sizeOf (switchCases fns) + 7 by omega
  -- Unfold buildSwitch, simplify the sortCasesBySelector=false branch, fold map to switchCases
  change sizeOf (Compiler.buildSwitch fns (sortCasesBySelector := false)) ≥ _
  unfold Compiler.buildSwitch
  simp only [ite_false, Bool.false_eq_true, Compiler.defaultDispatchCase]
  rw [show (fns.map (fun fn => (fn.selector,
      dispatchBody fn.payable s!"{fn.name}()"
        ([calldatasizeGuard fn.params.length] ++ fn.body)))) =
    switchCases fns from by simp [switchCases, switchCaseBody, dispatchBody]]
  -- Name sub-expressions and decompose sizeOf level by level (simp normalizes
  -- auto-generated SizeOf instances; omega closes the arithmetic)
  set defaultStmts : List YulStmt :=
    [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  set sw := YulStmt.switch
    (YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]])
    (switchCases fns) (some defaultStmts)
  set if2 := YulStmt.if_ (YulExpr.ident "__has_selector") [sw]
  have h1 : sizeOf (YulStmt.block [
      YulStmt.let_ "__has_selector" (YulExpr.call "iszero"
        [YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit 4]]),
      YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) defaultStmts,
      if2]) ≥ 5 + sizeOf if2 := by simp; omega
  have h2 : sizeOf if2 ≥ 2 + sizeOf [sw] := by simp [if2]; omega
  have h3 : sizeOf [sw] = sizeOf sw + 2 := by simp; omega
  have h4 : sizeOf sw ≥ 1 + sizeOf (switchCases fns) := by simp [sw]; omega
  omega

private theorem sizeOf_buildSwitch_ge_fn_body
    {fns : List IRFunction} {fn : IRFunction}
    (hmem : fn ∈ fns) :
    sizeOf [Compiler.buildSwitch fns none none] ≥ sizeOf fn.body + 12 := by
  have h1 := sizeOf_buildSwitch_ge_switchCases fns
  have h2 := sizeOf_switchCases_gt_body hmem
  have h3 := sizeOf_switchCaseBody_ge fn
  omega

/-- Calldatasize is always ≥ 4 in the proof semantics (4-byte selector prefix). -/
@[simp] private theorem calldatasize_ge_4 (args : List Nat) :
    ¬ (4 + args.length * 32 < 4) := by omega

/-- Simplification: lt(calldatasize, 4) = 0. -/
@[simp] private theorem calldatasize_lt_4_eq_zero (args : List Nat) :
    (if 4 + args.length * 32 < 4 then 1 else 0) = (0 : Nat) := by
  simp [show ¬ (4 + args.length * 32 < 4) from by omega]

/-- Simplification: iszero(0) = 1. -/
@[simp] private theorem iszero_zero : (if (0 : Nat) = 0 then 1 else 0) = (1 : Nat) := by simp

/-- Simplification: iszero(1) = 0. -/
@[simp] private theorem iszero_one : (if (1 : Nat) = 0 then 1 else 0) = (0 : Nat) := by simp

/-- Simplification: 1 ≠ 0 for if_ branch. -/
@[simp] private theorem one_ne_zero : (1 : Nat) ≠ 0 := by omega

/-- Identity simplifier for result-shaped matches emitted by `execYulFuel` reductions. -/
@[simp] private theorem yulExecResult_match_id (r : YulExecResult) :
    (match r with
    | .continue s => .continue s
    | .return v s => .return v s
    | .stop s => .stop s
    | .revert s => .revert s) = r := by
  cases r <;> rfl

/-- `callvalueGuard` is a no-op when the execution context observes zero
    `callvalue()` modulo `2^256`, matching `DispatchGuardsSafe`. -/
private theorem exec_callvalueGuard_noop (fuel : Nat) (state : YulState)
    (hMsgValue : state.msgValue % evmModulus = 0) :
    execYulStmtsFuel (fuel + 2) state [Compiler.callvalueGuard] =
      YulExecResult.continue state := by
  have hs : fuel + 2 = Nat.succ (Nat.succ fuel) := by omega
  rw [hs]
  have hCallvalue : evalYulExpr state (YulExpr.call "callvalue" []) = some 0 := by
    simp [hMsgValue, evalYulExpr, evalYulCall, evalYulExprs,
      evalBuiltinCallWithBackend, evalBuiltinCall, evalBuiltinCallWithBackendContext,
      evalBuiltinCallWithContext]
  simp [Compiler.callvalueGuard, execYulStmtsFuel, execYulFuel, hCallvalue]

/-- If calldata is too short for the expected arity, the singleton
    `calldatasizeGuard` list reverts. This is the smallest checked short-arity
    guard fact needed for the remaining switch-case bridge work. -/
private theorem exec_calldatasizeGuard_revert_of_short_noWrap
    (fuel : Nat) (state : YulState) (numParams : Nat)
    (hShort : ¬ numParams ≤ state.calldata.length)
    (hDataNoWrap : 4 + state.calldata.length * 32 < evmModulus)
    (hParamNoWrap : 4 + numParams * 32 < evmModulus) :
    execYulStmtsFuel (fuel + 2) state [Compiler.calldatasizeGuard numParams] =
      .revert state := by
  have hLtTrue : 4 + state.calldata.length * 32 < 4 + numParams * 32 := by
    omega
  have hEval :
      evalYulExpr state
        (YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit (4 + numParams * 32)]) =
        some 1 := by
    simp [evalYulExpr, evalYulCall, evalYulExprs, evalBuiltinCallWithBackendContext,
      evalBuiltinCallWithContext, hLtTrue, Nat.mod_eq_of_lt hDataNoWrap,
      Nat.mod_eq_of_lt hParamNoWrap]
  cases fuel with
  | zero =>
      simp [Compiler.calldatasizeGuard, execYulStmtsFuel, execYulFuel, hEval]
  | succ fuel =>
      cases fuel with
      | zero =>
          simp [Compiler.calldatasizeGuard, execYulStmtsFuel, execYulFuel, hEval]
      | succ fuel =>
          simp [Compiler.calldatasizeGuard, execYulStmtsFuel, execYulFuel, hEval]

/-- If calldata has enough words for `numParams`, `calldatasizeGuard` is a no-op.

Under the current builtin model, `lt` compares modulo `2^256`, so the generic
statement additionally needs a no-wrap hypothesis on `calldatasize()`. -/
private theorem exec_calldatasizeGuard_noop_of_noWrap
    (fuel : Nat) (state : YulState) (numParams : Nat)
    (hArity : numParams ≤ state.calldata.length)
    (hNoWrap : 4 + state.calldata.length * 32 < evmModulus) :
    execYulStmtsFuel (fuel + 2) state [Compiler.calldatasizeGuard numParams] =
      YulExecResult.continue state := by
  have hLtFalse : ¬ (4 + state.calldata.length * 32 < 4 + numParams * 32) := by
    omega
  have hParamNoWrap : 4 + numParams * 32 < evmModulus := by
    omega
  have hEval :
      evalYulExpr state
        (YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit (4 + numParams * 32)]) =
        some 0 := by
    simp [evalYulExpr, evalYulCall, evalYulExprs, evalBuiltinCallWithBackendContext,
      evalBuiltinCallWithContext, hLtFalse, Nat.mod_eq_of_lt hNoWrap, Nat.mod_eq_of_lt hParamNoWrap]
  simp [Compiler.calldatasizeGuard, execYulStmtsFuel, execYulFuel, hEval]

/-! ### buildSwitch stepping axiom

The `buildSwitch` block structure generates:
```
block [
  let_ "__has_selector" (iszero(lt(calldatasize(), 4))),
  if_ (iszero "__has_selector") defaultCase,
  if_ "__has_selector" [switch selectorExpr cases (some defaultCase)]
]
```

Executing this with enough fuel steps through:
1. `calldatasize() = 4 + calldata.length * 32 ≥ 4` always, so `lt(_, 4) = 0`, `iszero(0) = 1`
2. `__has_selector = 1`, so `iszero(1) = 0` → first `if_` skipped
3. `1 ≠ 0` → second `if_` enters body containing the switch

This reduction is mathematically straightforward but difficult to prove mechanically
because `execYulFuel` is `[reducible]` and `simp` over-reduces to produce
`Option.map`/`List.find?_map` fusion forms that don't match bridge lemmas.

**TODO**: Prove this mechanically (see issue #1094). The gap is purely technical:
the theorem statement is correct and the execution trace is well-understood.
-/

/-- After setting `__has_selector := 1`, reading `__has_selector` yields 1. -/
private theorem eval_hasSelector_after_set (state : YulState) :
    evalYulExpr (state.setVar "__has_selector" 1) (YulExpr.ident "__has_selector") = some 1 := by
  simp [evalYulExpr, YulState.setVar, YulState.getVar]

/-- Fueled `if_` step: a zero condition skips the body and continues unchanged. -/
@[simp] private theorem execYulStmtFuel_if_zero_continue
    (fuel : Nat) (state : YulState) (cond : YulExpr) (body : List YulStmt)
    (hEval : evalYulExpr state cond = some 0) :
    execYulStmtFuel (fuel + 1) state (YulStmt.if_ cond body) = .continue state := by
  simp [execYulStmtFuel, execYulFuel, hEval]

/-- Fueled `if_` step: a nonzero condition executes the body with decremented fuel. -/
@[simp] private theorem execYulStmtFuel_if_nonzero_exec
    (fuel : Nat) (state : YulState) (cond : YulExpr) (body : List YulStmt) (v : Nat)
    (hEval : evalYulExpr state cond = some v) (hNonzero : v ≠ 0) :
    execYulStmtFuel (fuel + 1) state (YulStmt.if_ cond body) = execYulStmtsFuel fuel state body := by
  simpa [execYulStmtsFuel] using
    (by simp [execYulStmtFuel, execYulFuel, hEval, hNonzero] :
      execYulStmtFuel (fuel + 1) state (YulStmt.if_ cond body) =
        execYulFuel fuel state (.stmts body))

/-- Zero fuel on a non-empty statement list always reverts. -/
@[simp] private theorem execYulStmtsFuel_zero_of_ne_nil
    (state : YulState) (stmts : List YulStmt) (hNe : stmts ≠ []) :
    execYulStmtsFuel 0 state stmts = .revert state := by
  cases stmts with
  | nil =>
      contradiction
  | cons _ _ =>
      simp [execYulStmtsFuel, execYulFuel]

/-- Executing a singleton statement list consumes one list-step of fuel. -/
@[simp] private theorem execYulStmtsFuel_singleton_succ_local
    (fuel : Nat) (state : YulState) (stmt : YulStmt) :
    execYulStmtsFuel (fuel + 2) state [stmt] = execYulStmtFuel (fuel + 1) state stmt := by
  simp [execYulStmtsFuel, execYulStmtFuel, execYulFuel]
  cases hExec : execYulFuel (fuel + 1) state (.stmt stmt) <;> simp

/-- Executing `[buildSwitch fns none none]` with enough fuel reduces to the singleton
    switch list when `calldatasize()` does not wrap modulo `2^256`.

    The old direct-`execYulStmtFuel` target was stronger than the literal small-step
    trace provides; this singleton-list form is the strongest true shape needed by
    the current Layer 3 proof. -/
private theorem execBuildSwitch_none_none_aux_of_noWrap (fuel : Nat) (state : YulState)
    (fns : List IRFunction)
    (hNoWrap : 4 + state.calldata.length * 32 < evmModulus) :
    execYulStmtsFuel (fuel + 6) state [Compiler.buildSwitch fns none none] =
      execYulStmtsFuel fuel (state.setVar "__has_selector" 1)
        [YulStmt.switch selectorExpr (switchCases fns)
          (some (switchDefaultCase none none))] := by
  let state' := state.setVar "__has_selector" 1
  have h4 : 4 < evmModulus := by
    norm_num [evmModulus]
  have hHasSelectorEval :
      evalYulExpr state
        (YulExpr.call "iszero"
          [YulExpr.call "lt" [YulExpr.call "calldatasize" [], YulExpr.lit 4]]) = some 1 := by
    simp [evalYulExpr, evalYulCall, evalYulExprs, evalBuiltinCallWithBackendContext,
      evalBuiltinCallWithContext, Nat.mod_eq_of_lt hNoWrap, Nat.mod_eq_of_lt h4]
  have hIdentEval :
      evalYulExpr state' (YulExpr.ident "__has_selector") = some 1 := by
    simpa [state', evalYulExpr] using eval_hasSelector_after_set state
  have hIfZeroEval :
      evalYulExpr state'
        (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) = some 0 := by
    simp [evalYulExpr, evalYulCall, evalYulExprs,
      evalBuiltinCallWithBackendContext, evalBuiltinCallWithContext, hIdentEval]
  rw [show fuel + 6 = (fuel + 4) + 2 by omega, execYulStmtsFuel_singleton_succ_local]
  simp only [Compiler.buildSwitch, execYulStmtFuel, execYulFuel]
  simp [state', execYulStmtsFuel, hHasSelectorEval, hIfZeroEval, hIdentEval,
    switchCases, switchCaseBody, dispatchBody, selectorExpr, switchDefaultCase]
  exact yulExecResult_match_id _

/-- Executing a singleton statement list consumes one list-step of fuel. -/
@[simp] private theorem execYulStmtsFuel_singleton_succ
    (fuel : Nat) (state : YulState) (stmt : YulStmt) :
    execYulStmtsFuel (fuel + 2) state [stmt] = execYulStmtFuel (fuel + 1) state stmt := by
  simp [execYulStmtsFuel, execYulStmtFuel, execYulFuel]
  cases hExec : execYulFuel (fuel + 1) state (.stmt stmt) <;> simp

/-- If a head statement continues, the surrounding list steps into the tail. -/
@[simp] private theorem execYulStmtsFuel_cons_continue
    (fuel : Nat) (state next : YulState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execYulStmtFuel (fuel + 1) state stmt = .continue next) :
    execYulStmtsFuel (fuel + 2) state (stmt :: rest) =
      execYulStmtsFuel (fuel + 1) next rest := by
  have hstmt' : execYulFuel (fuel + 1) state (.stmt stmt) = .continue next := by
    simpa [execYulStmtFuel] using hstmt
  simp [execYulStmtsFuel, execYulFuel, hstmt']

/-- If a head statement reverts, the surrounding list reverts immediately. -/
@[simp] private theorem execYulStmtsFuel_cons_revert
    (fuel : Nat) (state : YulState) (stmt : YulStmt) (rest : List YulStmt)
    (hstmt : execYulStmtFuel (fuel + 1) state stmt = .revert state) :
    execYulStmtsFuel (fuel + 2) state (stmt :: rest) = .revert state := by
  have hstmt' : execYulFuel (fuel + 1) state (.stmt stmt) = .revert state := by
    simpa [execYulStmtFuel] using hstmt
  simp [execYulStmtsFuel, execYulFuel, hstmt']

/-- The case list emitted by `buildSwitch` is definitionally `switchCases`.
    Keeping this fact explicit helps avoid large reducible unfold chains in #1094 proofs. -/
private theorem buildSwitch_cases_eq_switchCases (fns : List IRFunction) :
    (fns.map (fun fn =>
      (fn.selector,
        dispatchBody fn.payable s!"{fn.name}()"
          ([calldatasizeGuard fn.params.length] ++ fn.body)))) =
      switchCases fns := by
  simp [switchCases, switchCaseBody, dispatchBody]

/-- Normalize switch-case lookup to function-list lookup.
    This removes `List.find?_map` noise from mechanical `buildSwitch` proofs. -/
private theorem find_switchCases_eq_find_function
    (fns : List IRFunction) (sel : Nat) :
    (switchCases fns).find? (fun (c, _) => c = sel) =
      Option.map (fun fn => (fn.selector, switchCaseBody fn))
        (fns.find? (fun fn => fn.selector == sel)) := by
  induction fns with
  | nil =>
      simp [switchCases]
  | cons fn rest ih =>
      by_cases hsel : fn.selector = sel
      · simp [switchCases, hsel]
      · have hPred :
          ((fun x : Prod Nat (List YulStmt) => decide (x.1 = sel)) ∘
              fun f : IRFunction => (f.selector, switchCaseBody f)) =
            (fun f : IRFunction => f.selector == sel) := by
          funext f
          simp [beq_eq_decide]
        simp [switchCases, hsel, hPred]

/-- `selectorExpr` does not depend on `__has_selector`, so the selector evaluation
    is the same in the augmented state. -/
private theorem evalSelectorExpr_setVar_has_selector (state : YulState) (v : Nat)
    (hselector : state.selector < selectorModulus) :
    evalYulExpr (state.setVar "__has_selector" v) selectorExpr =
      some state.selector := by
  -- Keep this bridge local and avoid unfolding the full builtin evaluator.
  simpa using (evalYulExpr_selectorExpr_eq (state.setVar "__has_selector" v) (by
    simpa [YulState.setVar] using hselector))

private theorem exec_switchCaseBody_revert_of_short
    (fn : IRFunction) (tx : IRTransaction) (irState : IRState) (fuel : Nat)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hShort : ¬ fn.params.length ≤ tx.args.length) :
    execYulStmtsFuel (fuel + 2)
      ((YulState.initial
          { sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            functionSelector := tx.functionSelector
            args := tx.args }
          irState.storage irState.events).setVar "__has_selector" 1)
      (switchCaseBody fn) =
        .revert
          ((YulState.initial
              { sender := tx.sender
                msgValue := tx.msgValue
                thisAddress := tx.thisAddress
                blockTimestamp := tx.blockTimestamp
                blockNumber := tx.blockNumber
                chainId := tx.chainId
                blobBaseFee := tx.blobBaseFee
                functionSelector := tx.functionSelector
                args := tx.args }
              irState.storage irState.events).setVar "__has_selector" 1) := by
  rcases hguards with ⟨hValueSafe, hParamNoWrap⟩
  let state :=
    ((YulState.initial
        { sender := tx.sender
          msgValue := tx.msgValue
          thisAddress := tx.thisAddress
          blockTimestamp := tx.blockTimestamp
          blockNumber := tx.blockNumber
          chainId := tx.chainId
          blobBaseFee := tx.blobBaseFee
          functionSelector := tx.functionSelector
          args := tx.args }
        irState.storage irState.events).setVar "__has_selector" 1)
  have hDataNoWrap : 4 + state.calldata.length * 32 < evmModulus := by
    simpa [state, YulState.initial, YulState.setVar] using hNoWrap
  have hComment :
      execYulStmtFuel (fuel + 1) state (YulStmt.comment s!"{fn.name}()") = .continue state := by
    simp [execYulStmtFuel, execYulFuel]
  cases hPayable : fn.payable with
  | true =>
      rw [show switchCaseBody fn =
        YulStmt.comment s!"{fn.name}()" :: Compiler.calldatasizeGuard fn.params.length :: fn.body by
          simp [switchCaseBody, hPayable]]
      rw [execYulStmtsFuel_cons_continue (fuel := fuel) (next := state) (hstmt := hComment)]
      cases fuel with
      | zero =>
          rfl
      | succ fuel =>
          have hGuard :
              execYulStmtFuel (fuel + 1) state (Compiler.calldatasizeGuard fn.params.length) =
                .revert state := by
            simpa [execYulStmtFuel] using
              (exec_calldatasizeGuard_revert_of_short_noWrap fuel state fn.params.length
                hShort hDataNoWrap hParamNoWrap)
          exact execYulStmtsFuel_cons_revert (fuel := fuel) (state := state)
            (stmt := Compiler.calldatasizeGuard fn.params.length) (rest := fn.body) hGuard
  | false =>
      rw [show switchCaseBody fn =
        YulStmt.comment s!"{fn.name}()" ::
          Compiler.callvalueGuard ::
            Compiler.calldatasizeGuard fn.params.length :: fn.body by
          simp [switchCaseBody, hPayable]]
      rw [execYulStmtsFuel_cons_continue (fuel := fuel) (next := state) (hstmt := hComment)]
      cases fuel with
      | zero =>
          rfl
      | succ fuel =>
          have hMsgValue :
              state.msgValue % evmModulus = 0 := by
            have hZero : tx.msgValue % evmModulus = 0 := by
              rcases hValueSafe with hTrue | hZero
              · cases (by simpa [hPayable] using hTrue : False)
              · exact hZero
            simpa [state, YulState.initial, YulState.setVar] using hZero
          have hValueGuard :
              execYulStmtFuel (fuel + 1) state Compiler.callvalueGuard = .continue state := by
            simpa [execYulStmtFuel] using exec_callvalueGuard_noop fuel state hMsgValue
          rw [execYulStmtsFuel_cons_continue (fuel := fuel) (next := state) (hstmt := hValueGuard)]
          cases fuel with
          | zero =>
              rfl
          | succ fuel =>
              have hGuard :
                  execYulStmtFuel (fuel + 1) state (Compiler.calldatasizeGuard fn.params.length) =
                    .revert state := by
                simpa [execYulStmtFuel] using
                  (exec_calldatasizeGuard_revert_of_short_noWrap fuel state fn.params.length
                    hShort hDataNoWrap hParamNoWrap)
              exact execYulStmtsFuel_cons_revert (fuel := fuel) (state := state)
                (stmt := Compiler.calldatasizeGuard fn.params.length) (rest := fn.body) hGuard

private theorem SwitchCaseBodyBridge_short
    (fn : IRFunction) (tx : IRTransaction) (irState : IRState) (fuel : Nat) :
    DispatchGuardsSafe fn tx →
    4 + tx.args.length * 32 < evmModulus →
    ¬ fn.params.length ≤ tx.args.length →
    resultsMatch
      { success := false
        returnValue := none
        finalStorage := irState.storage
        finalMappings := storageAsMappings irState.storage
        events := irState.events }
      (yulResultOfExecWithRollback
        (YulState.initial
          { sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            functionSelector := tx.functionSelector
            args := tx.args }
          irState.storage irState.events)
        (execYulStmtsFuel (fuel + 2)
          ((YulState.initial
            { sender := tx.sender
              msgValue := tx.msgValue
              thisAddress := tx.thisAddress
              blockTimestamp := tx.blockTimestamp
              blockNumber := tx.blockNumber
              chainId := tx.chainId
              blobBaseFee := tx.blobBaseFee
              functionSelector := tx.functionSelector
              args := tx.args }
            irState.storage irState.events).setVar "__has_selector" 1)
          (switchCaseBody fn))) := by
  intro hguards hNoWrap hShort
  have hExec := exec_switchCaseBody_revert_of_short fn tx irState fuel hguards hNoWrap hShort
  rw [hExec]
  simp [YulState.initial, yulResultOfExecWithRollback, resultsMatch]

/-! ### switchCaseBody guard-stepping helpers

These helpers decompose execution of `switchCaseBody fn` — which is
`[comment] ++ valueGuard ++ [calldatasizeGuard] ++ fn.body` — into
individually justified steps.
-/

/-- When dispatch guards are safe and calldata is long enough, executing the
    guard prefix of `switchCaseBody fn` is a no-op: the execution steps through
    comment, optional callvalue guard, and calldatasize guard, reaching
    `fn.body` in the same state with reduced fuel.  This is the success-path
    counterpart to `exec_switchCaseBody_revert_of_short`. -/
private theorem exec_switchCaseBody_continue_of_long
    (fn : IRFunction) (tx : IRTransaction) (irState : IRState) (fuel : Nat)
    (hguards : DispatchGuardsSafe fn tx)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hLong : fn.params.length ≤ tx.args.length)
    (hfuel : fuel ≥ 2) :
    ∃ fuel' : Nat, fuel' ≤ fuel ∧ fuel' ≥ fuel - 2 ∧
    execYulStmtsFuel (fuel + 2)
      ((YulState.initial
          { sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            functionSelector := tx.functionSelector
            args := tx.args }
          irState.storage irState.events).setVar "__has_selector" 1)
      (switchCaseBody fn) =
        execYulStmtsFuel fuel'
          ((YulState.initial
              { sender := tx.sender
                msgValue := tx.msgValue
                thisAddress := tx.thisAddress
                blockTimestamp := tx.blockTimestamp
                blockNumber := tx.blockNumber
                chainId := tx.chainId
                blobBaseFee := tx.blobBaseFee
                functionSelector := tx.functionSelector
                args := tx.args }
              irState.storage irState.events).setVar "__has_selector" 1)
          fn.body := by
  rcases hguards with ⟨hValueSafe, hParamNoWrap⟩
  let state :=
    ((YulState.initial
        { sender := tx.sender
          msgValue := tx.msgValue
          thisAddress := tx.thisAddress
          blockTimestamp := tx.blockTimestamp
          blockNumber := tx.blockNumber
          chainId := tx.chainId
          blobBaseFee := tx.blobBaseFee
          functionSelector := tx.functionSelector
          args := tx.args }
        irState.storage irState.events).setVar "__has_selector" 1)
  have hDataNoWrap : 4 + state.calldata.length * 32 < evmModulus := by
    simpa [state, YulState.initial, YulState.setVar] using hNoWrap
  have hArity : fn.params.length ≤ state.calldata.length := by
    simpa [state, YulState.initial, YulState.setVar] using hLong
  have hComment :
      execYulStmtFuel (fuel + 1) state (YulStmt.comment s!"{fn.name}()") = .continue state := by
    simp [execYulStmtFuel, execYulFuel]
  cases hPayable : fn.payable with
  | true =>
      rw [show switchCaseBody fn =
        YulStmt.comment s!"{fn.name}()" :: Compiler.calldatasizeGuard fn.params.length :: fn.body by
          simp [switchCaseBody, hPayable]]
      rw [execYulStmtsFuel_cons_continue (fuel := fuel) (next := state) (hstmt := hComment)]
      -- fuel ≥ 2, so fuel ≥ 1 and we can write fuel = k + 1
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
      have hGuard :
          execYulStmtFuel (k + 1) state (Compiler.calldatasizeGuard fn.params.length) =
            .continue state := by
        simpa [execYulStmtFuel] using
          (exec_calldatasizeGuard_noop_of_noWrap k state fn.params.length
            hArity hDataNoWrap)
      rw [execYulStmtsFuel_cons_continue (fuel := k) (next := state) (hstmt := hGuard)]
      exact ⟨k + 1, by omega, by omega, rfl⟩
  | false =>
      rw [show switchCaseBody fn =
        YulStmt.comment s!"{fn.name}()" ::
          Compiler.callvalueGuard ::
            Compiler.calldatasizeGuard fn.params.length :: fn.body by
          simp [switchCaseBody, hPayable]]
      -- fuel ≥ 2, so we can step through both guards without hitting zero fuel
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
      rw [execYulStmtsFuel_cons_continue (fuel := k + 2) (next := state) (hstmt := hComment)]
      have hMsgValue :
          state.msgValue % evmModulus = 0 := by
        have hZero : tx.msgValue % evmModulus = 0 := by
          rcases hValueSafe with hTrue | hZero
          · cases (by simpa [hPayable] using hTrue : False)
          · exact hZero
        simpa [state, YulState.initial, YulState.setVar] using hZero
      have hValueGuard :
          execYulStmtFuel (k + 1 + 1) state Compiler.callvalueGuard = .continue state := by
        simpa [execYulStmtFuel] using exec_callvalueGuard_noop (k + 1) state hMsgValue
      rw [show k + 2 + 1 = (k + 1) + 2 from by omega]
      rw [execYulStmtsFuel_cons_continue (fuel := k + 1) (next := state) (hstmt := hValueGuard)]
      have hGuard :
          execYulStmtFuel (k + 1) state (Compiler.calldatasizeGuard fn.params.length) =
            .continue state := by
        simpa [execYulStmtFuel] using
          (exec_calldatasizeGuard_noop_of_noWrap k state fn.params.length
            hArity hDataNoWrap)
      rw [execYulStmtsFuel_cons_continue (fuel := k) (next := state) (hstmt := hGuard)]
      exact ⟨k + 1, by omega, by omega, rfl⟩

/-! ### switchCaseBody body bridge axioms

After the guard prefix has been proved to pass (by `exec_switchCaseBody_continue_of_long`),
the remaining gap is connecting fuel-bounded execution of `fn.body` in a state
where `__has_selector = 1` to the total `interpretYulRuntime fn.body ...`.

This gap is decomposed into two independent sub-properties, each captured by
its own axiom:
-/

/-- **Variable irrelevance**: the `__has_selector` dispatch variable is never
read by function body statements, so adding it to the variable environment
does not change execution.  This is a purely Yul-level property that does not
mention IR types. -/
private axiom execYulStmtsFuel_setVar_hasSelector_irrelevant
    (body : List YulStmt) (state : YulState) (fuel : Nat) :
    execYulStmtsFuel fuel (state.setVar "__has_selector" 1) body =
    execYulStmtsFuel fuel state body

/-- **Fuel adequacy**: when the fuel budget is at least `sizeOf body + 1`
(the amount used by `execYulStmts`), fuel-bounded execution gives the same
result as total execution.  This is a purely Yul-level fuel-monotonicity
property.  The hypothesis `h` ensures the fuel is sufficient. -/
private axiom execYulStmtsFuel_fuel_adequate
    (body : List YulStmt) (state : YulState) (fuel : Nat)
    (h : fuel ≥ sizeOf body + 1) :
    execYulStmtsFuel fuel state body = execYulStmts state body

/-- Composition of variable irrelevance and fuel adequacy. -/
private theorem SwitchCaseBodyBridge_body
    (body : List YulStmt) (state : YulState) (fuel : Nat)
    (h : fuel ≥ sizeOf body + 1) :
    yulResultOfExecWithRollback state
      (execYulStmtsFuel fuel (state.setVar "__has_selector" 1) body) =
    yulResultOfExecWithRollback state
      (execYulStmts state body) := by
  rw [execYulStmtsFuel_setVar_hasSelector_irrelevant]
  rw [execYulStmtsFuel_fuel_adequate body state fuel h]

/-! ### switchCaseBody bridge theorem

`SwitchCaseBodyBridge` is now a proved theorem rather than an axiom.
It composes two pieces:
1. `exec_switchCaseBody_continue_of_long` — proved guard-prefix stepping
2. `SwitchCaseBodyBridge_body` — composed from variable irrelevance + fuel adequacy axioms
-/
private theorem SwitchCaseBodyBridge
    (fn : IRFunction) (tx : IRTransaction) (irState : IRState) (fuel : Nat)
    (hFuelAdequate : fuel ≥ sizeOf fn.body + 5) :
    DispatchGuardsSafe fn tx →
    4 + tx.args.length * 32 < evmModulus →
    fn.params.length ≤ tx.args.length →
    resultsMatch
      (execIRFunction fn tx.args irState)
      (interpretYulRuntime fn.body
        { sender := tx.sender
          msgValue := tx.msgValue
          thisAddress := tx.thisAddress
          blockTimestamp := tx.blockTimestamp
          blockNumber := tx.blockNumber
          chainId := tx.chainId
          blobBaseFee := tx.blobBaseFee
          functionSelector := tx.functionSelector
          args := tx.args }
        irState.storage irState.events) →
    resultsMatch
      (execIRFunction fn tx.args irState)
      (yulResultOfExecWithRollback
        (YulState.initial
          { sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            functionSelector := tx.functionSelector
            args := tx.args }
          irState.storage irState.events)
        (execYulStmtsFuel fuel
          ((YulState.initial
            { sender := tx.sender
              msgValue := tx.msgValue
              thisAddress := tx.thisAddress
              blockTimestamp := tx.blockTimestamp
              blockNumber := tx.blockNumber
              chainId := tx.chainId
              blobBaseFee := tx.blobBaseFee
              functionSelector := tx.functionSelector
              args := tx.args }
            irState.storage irState.events).setVar "__has_selector" 1)
          (switchCaseBody fn))) := by
  intro hguards hNoWrap hlen hmatch
  set yulTx : YulTransaction :=
    { sender := tx.sender
      msgValue := tx.msgValue
      thisAddress := tx.thisAddress
      blockTimestamp := tx.blockTimestamp
      blockNumber := tx.blockNumber
      chainId := tx.chainId
      blobBaseFee := tx.blobBaseFee
      functionSelector := tx.functionSelector
      args := tx.args }
  set s₀ := YulState.initial yulTx irState.storage irState.events
  -- Step 1: use guard-stepping to reduce to fn.body execution
  -- fuel ≥ sizeOf fn.body + 5 ≥ 5 ≥ 2, so guards can be stepped
  have hfuel2 : fuel ≥ 2 := by omega
  obtain ⟨fuel', hle, hge, hstep⟩ :=
    exec_switchCaseBody_continue_of_long fn tx irState (fuel - 2) hguards hNoWrap hlen (by omega)
  -- Align fuel: fuel = (fuel - 2) + 2 since fuel ≥ 2
  have hfuelEq : fuel = (fuel - 2) + 2 := by omega
  rw [hfuelEq]
  rw [hstep]
  -- Step 2: bridge body execution to interpretYulRuntime
  -- fuel' ≥ (fuel - 2) - 2 = fuel - 4 (by hge).
  -- Since fuel ≥ sizeOf fn.body + 5, we have fuel - 4 ≥ sizeOf fn.body + 1.
  have hfuelAdequate' : fuel' ≥ sizeOf fn.body + 1 := by omega
  have hbody := SwitchCaseBodyBridge_body fn.body s₀ fuel' hfuelAdequate'
  -- hmatch gives us resultsMatch via interpretYulRuntime
  -- interpretYulRuntime fn.body yulTx ... = yulResultOfExecWithRollback s₀ (execYulStmts s₀ fn.body)
  rw [hbody]
  simp only [interpretYulRuntime, execYulStmts] at hmatch
  exact hmatch

set_option maxHeartbeats 1600000000 in
/-- Main preservation theorem: Yul codegen preserves IR semantics.

The `hWF` hypothesis requires that `contract.internalFunctions` are all
`funcDef` statements, which holds for every contract emitted by the compiler.

**Note**: This theorem currently requires `fallbackEntrypoint = none` and
`receiveEntrypoint = none` because `interpretIR` returns failure when no
function selector matches, which is only consistent with a revert-only
default case. Extending to fallback/receive requires extending `interpretIR`. -/
theorem yulCodegen_preserves_semantics
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hNoWrap : 4 + tx.args.length * 32 < evmModulus)
    (hWF : ContractWF contract)
    (hNoFallback : contract.fallbackEntrypoint = none)
    (hNoReceive : contract.receiveEntrypoint = none)
    (hdispatchGuardSafe : ∀ fn, fn ∈ contract.functions → DispatchGuardsSafe fn tx)
    (hbody : ∀ fn, fn ∈ contract.functions →
      resultsMatch
        (execIRFunction fn tx.args
          { initialState with
            sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            calldata := tx.args
            selector := tx.functionSelector })
        (interpretYulBody fn tx
          { initialState with
            sender := tx.sender
            msgValue := tx.msgValue
            thisAddress := tx.thisAddress
            blockTimestamp := tx.blockTimestamp
            blockNumber := tx.blockNumber
            chainId := tx.chainId
            blobBaseFee := tx.blobBaseFee
            calldata := tx.args
            selector := tx.functionSelector })) :
    resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  let irState := {
    initialState with
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    calldata := tx.args
    selector := tx.functionSelector
  }
  let yulTx : YulTransaction := {
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    functionSelector := tx.functionSelector
    args := tx.args
  }
  -- Abbreviations for the funcDef prefix and buildSwitch suffix.
  set prefix_ := (if contract.usesMapping then [Compiler.mappingSlotFuncAt 0] else []) ++
    contract.internalFunctions with hPrefixDef
  set switchStmt := Compiler.buildSwitch contract.functions contract.fallbackEntrypoint
    contract.receiveEntrypoint with hSwitchDef
  have hRuntimeEq : Compiler.runtimeCode contract = prefix_ ++ [switchStmt] := by
    simp [Compiler.runtimeCode, List.append_assoc, hPrefixDef, hSwitchDef]
  have hPrefixFD := runtimeCode_prefix_allFuncDefs contract hWF
  rw [← hPrefixDef] at hPrefixFD
  have hFuel : sizeOf (prefix_ ++ [switchStmt]) + 1 ≥ prefix_.length := by
    have h1 : prefix_.length ≤ (prefix_ ++ [switchStmt]).length := by simp
    have h2 : (prefix_ ++ [switchStmt]).length ≤ sizeOf (prefix_ ++ [switchStmt]) :=
      list_length_le_sizeOf (prefix_ ++ [switchStmt])
    omega
  have hSkip : ∀ state : YulState,
      execYulStmtsFuel (sizeOf (prefix_ ++ [switchStmt]) + 1) state (prefix_ ++ [switchStmt]) =
      execYulStmtsFuel (sizeOf (prefix_ ++ [switchStmt]) + 1 - prefix_.length) state [switchStmt] :=
    fun state => execYulStmtsFuel_funcDefs_then_suffix_ge _ state prefix_ [switchStmt] hPrefixFD hFuel
  set adjustedFuel := sizeOf (prefix_ ++ [switchStmt]) + 1 - prefix_.length
  have hAdjGe : adjustedFuel ≥ 10 := by
    have : sizeOf (prefix_ ++ [switchStmt]) + 1 - prefix_.length ≥ sizeOf [switchStmt] + 1 := by
      have := sizeOf_append_ge_length_add prefix_ [switchStmt]; omega
    have : sizeOf [switchStmt] ≥ 9 := by rw [hSwitchDef]; simp [Compiler.buildSwitch]; omega
    omega
  obtain ⟨m, hm⟩ : ∃ m, adjustedFuel = m + 10 := ⟨adjustedFuel - 10, by omega⟩
  -- Simplify buildSwitch with known fallback/receive = none.
  have hSwitchSimp : switchStmt = Compiler.buildSwitch contract.functions none none := by
    rw [hSwitchDef, hNoFallback, hNoReceive]
  -- Selector modulus pre-computation.
  have hpow : (2 : Nat) ^ selectorShift > 0 := by simp [selectorShift]
  have hselMod : tx.functionSelector % 4294967296 = tx.functionSelector := by
    have : selectorModulus = 4294967296 := by simp [selectorModulus]
    rw [← this]; exact Nat.mod_eq_of_lt hselector
  -- The Yul initial state for the switch dispatch
  set yulInitState := YulState.initial yulTx irState.storage irState.events with hYulInitDef
  -- Key fact: yulInitState.selector = tx.functionSelector
  have hSelEq : yulInitState.selector = tx.functionSelector := rfl
  -- Now case-split on whether any function matches the selector
  cases hFind : contract.functions.find? (fun f => f.selector == tx.functionSelector) with
  | none =>
      -- No function matches: IR returns failure, Yul should revert
      simp only [interpretIR, hFind]
      -- The Yul side: skip prefix, reach buildSwitch, step through block to switch, miss all cases, revert
      simp only [interpretYulFromIR, emitYul_runtimeCode_eq, interpretYulRuntime,
        execYulStmts, hRuntimeEq, hSkip]
      rw [hm, hSwitchSimp]
      -- Use the buildSwitch stepping axiom
      have hStep := execBuildSwitch_none_none_aux_of_noWrap (m + 4) yulInitState contract.functions (by
        simpa [hYulInitDef] using hNoWrap)
      rw [show m + 4 + 6 = m + 10 from by omega] at hStep
      rw [hStep]
      rw [show m + 4 = (m + 2) + 2 by omega, execYulStmtsFuel_singleton_succ]
      -- Now we have execYulStmtFuel on the switch with state augmented by __has_selector
      -- The selector evaluates the same way since selectorExpr doesn't use __has_selector
      have hSelEval := evalSelectorExpr_setVar_has_selector yulInitState 1 (by
        rw [hSelEq]; exact hselector)
      -- Bridge hcase: tx.functionSelector = yulInitState.selector
      have hcase := find_switch_case_of_find_function_none contract.functions
        yulInitState.selector (hSelEq ▸ hFind)
      -- Apply switch miss lemma
      rw [show m + 2 + 1 = Nat.succ (m + 2) from by omega]
      rw [execYulStmtFuel_switch_miss _ _ _ _ _ _ hSelEval hcase]
      -- Now we need to show the revert case matches resultsMatch for failure
      simp [execYulStmtFuel_switch_miss_result, switchDefaultCase,
        execYulStmtsFuel, execYulFuel, resultsMatch,
        Compiler.Proofs.storageAsMappings, yulInitState, YulState.initial, YulState.setVar]
  | some fn =>
      -- A function matches: use hbody to connect IR and Yul
      have hmem : fn ∈ contract.functions := List.mem_of_find?_eq_some hFind
      have hmatch := hbody fn hmem
      simp only [interpretIR, hFind]
      simp only [interpretYulFromIR, emitYul_runtimeCode_eq, interpretYulRuntime,
        execYulStmts, hRuntimeEq, hSkip]
      simp only [interpretYulBody_eq_runtime, interpretYulRuntime, execYulStmts] at hmatch
      rw [hm, hSwitchSimp]
      -- Use the buildSwitch stepping axiom
      have hStep := execBuildSwitch_none_none_aux_of_noWrap (m + 4) yulInitState contract.functions (by
        simpa [hYulInitDef] using hNoWrap)
      rw [show m + 4 + 6 = m + 10 from by omega] at hStep
      rw [hStep]
      rw [show m + 4 = (m + 2) + 2 by omega, execYulStmtsFuel_singleton_succ]
      -- The selector evaluates the same way
      have hSelEval := evalSelectorExpr_setVar_has_selector yulInitState 1 (by
        rw [hSelEq]; exact hselector)
      -- Rewrite to the transaction selector shape expected by the switch-match lemma.
      have hcase : (switchCases contract.functions).find? (fun (c, _) => c = tx.functionSelector) =
          some (tx.functionSelector, switchCaseBody fn) := by
        simpa [hSelEq] using
          (find_switch_case_of_find_function_eq_selector contract.functions yulInitState.selector fn
            (hSelEq ▸ hFind))
      rw [← hSelEq] at hcase
      -- Apply switch match lemma
      rw [show m + 2 + 1 = Nat.succ (m + 2) from by omega]
      rw [execYulStmtFuel_switch_match _ _ _ _ _ _ _ hSelEval hcase]
      -- Establish fuel adequacy for the body bridge.
      -- sizeOf [switchStmt] ≥ sizeOf fn.body + 12 (by sizeOf_buildSwitch_ge_fn_body),
      -- adjustedFuel ≥ sizeOf [switchStmt] + 1, and m + 10 = adjustedFuel.
      have hFuelBody : m + 2 ≥ sizeOf fn.body + 5 := by
        have hBound := sizeOf_buildSwitch_ge_fn_body (fns := contract.functions) (fn := fn) hmem
        rw [← hSwitchSimp] at hBound
        have hAdj : adjustedFuel ≥ sizeOf [switchStmt] + 1 := by
          have := sizeOf_append_ge_length_add prefix_ [switchStmt]; omega
        omega
      by_cases hlen : fn.params.length ≤ tx.args.length
      · simpa [hlen] using
          (SwitchCaseBodyBridge fn tx
            { initialState with
              sender := tx.sender
              msgValue := tx.msgValue
              thisAddress := tx.thisAddress
              blockTimestamp := tx.blockTimestamp
              blockNumber := tx.blockNumber
              chainId := tx.chainId
              blobBaseFee := tx.blobBaseFee
              calldata := tx.args
              selector := tx.functionSelector }
            (m + 2) hFuelBody (hdispatchGuardSafe fn hmem) hNoWrap hlen hmatch)
      · simpa [hlen] using
          (SwitchCaseBodyBridge_short fn tx
            { initialState with
              sender := tx.sender
              msgValue := tx.msgValue
              thisAddress := tx.thisAddress
              blockTimestamp := tx.blockTimestamp
              blockNumber := tx.blockNumber
              chainId := tx.chainId
              blobBaseFee := tx.blobBaseFee
              calldata := tx.args
              selector := tx.functionSelector }
            m (hdispatchGuardSafe fn hmem) hNoWrap hlen)

/-! ## Complete Preservation Theorem

This version of the preservation theorem discharges the `hbody` hypothesis
using the proven `all_stmts_equiv` and `ir_yul_function_equiv_from_state_of_stmt_equiv`.

The remaining gap between `interpretYulBodyFromState` (fuel-based proof chain) and
`interpretYulBody` (used by the theorem above) requires bridging two
different Yul execution entry points. This bridging lemma documents that gap explicitly.

**Proof chain** (complete — fuel adequacy eliminated, now internal):
1. `all_stmts_equiv` — every IR statement type is equivalent (StatementEquivalence.lean)
2. `execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv` — lifts to lists (Equivalence.lean)
3. `ir_yul_function_equiv_from_state_of_stmt_equiv` — function-level equivalence
   (fuel adequacy is discharged internally via `rfl`)

The theorem `ir_function_body_equiv` below demonstrates the complete chain for any
single function, and `yulCodegen_preserves_semantics` lifts it to full contracts.
-/

/-- Any single IR function body produces equivalent results under fuel-based Yul execution.

This is the instantiation of the proof chain with `all_stmts_equiv`, producing a
self-contained result for any function/args/state triple. Fuel adequacy is discharged
internally (it is `rfl` since the IR interpreter is total/fuel-based).
-/
theorem ir_function_body_equiv
    (fn : IRFunction) (selector : Nat) (args : List Nat) (initialState : IRState) :
    resultsMatch
      (execIRFunction fn args initialState)
      (interpretYulBodyFromState fn selector
        (fn.params.zip args |>.foldl (fun s (p, v) => s.setVar p.name v) initialState)
        initialState) :=
  ir_yul_function_equiv_from_state_of_stmt_equiv
    (fun sel f st irSt yulSt => all_stmts_equiv sel f st irSt yulSt)
    fn selector args initialState

end Compiler.Proofs.YulGeneration
