import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanPureBuiltinLemmas

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Codegen Proof Obligations (Layer 3)

These lemmas capture the core obligations for Yul codegen correctness:
1. Selector extraction matches the function selector.
2. Runtime switch dispatch executes the selected function body.
-/

@[simp]
private theorem emitYul_runtimeCode_eq (contract : IRContract) :
    (Compiler.emitYul contract).runtimeCode = Compiler.runtimeCode contract := by
  rfl

/-- Selector extraction via `selectorExpr` yields the 4-byte selector. -/
@[simp]
private theorem evalYulExpr_selectorExpr (state : YulState) :
    evalYulExpr state selectorExpr = some (state.selector % selectorModulus) :=
by
  have hShiftModEq : selectorShift % evmModulus = selectorShift := by
    have hShiftLtModulus : selectorShift < evmModulus := by
      norm_num [selectorShift, evmModulus]
    exact Nat.mod_eq_of_lt hShiftLtModulus
  have hSelectorShiftLt256 : selectorShift < 256 := by
    norm_num [selectorShift]
  have hSelectorShiftNotGe256 : ¬ 256 ≤ selectorShift := Nat.not_le_of_lt hSelectorShiftLt256
  have hSelectorWordLt :
      (state.selector % selectorModulus) * 2 ^ selectorShift < evmModulus := by
    have hModLt : state.selector % selectorModulus < selectorModulus := by
      exact Nat.mod_lt _ (by decide)
    have hPowPos : 0 < 2 ^ selectorShift := by
      exact Nat.pow_pos (a := 2) (n := selectorShift) (by decide)
    have hMulLt :
        (state.selector % selectorModulus) * 2 ^ selectorShift <
          selectorModulus * 2 ^ selectorShift := by
      exact Nat.mul_lt_mul_of_pos_right hModLt hPowPos
    have hModulusSplit : selectorModulus * 2 ^ selectorShift = evmModulus := by
      norm_num [selectorModulus, selectorShift, evmModulus, Nat.pow_add, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc]
    simpa [hModulusSplit] using hMulLt
  have hSelectorWordMod :
      ((state.selector % selectorModulus) * 2 ^ selectorShift) % evmModulus =
        (state.selector % selectorModulus) * 2 ^ selectorShift := by
    exact Nat.mod_eq_of_lt hSelectorWordLt
  simp [selectorExpr, evalYulExpr, evalYulCall, evalYulExprs,
    evalBuiltinCallWithBackendContext, Backends.evalBuiltinCallWithEvmYulLeanContext,
    Backends.evalBuiltinCallViaEvmYulLean,
    calldataloadWord, selectorWord,
    hShiftModEq, hSelectorWordMod, hSelectorShiftNotGe256]

/-- Selector extraction yields the raw selector when it fits in 4 bytes. -/
@[simp]
private theorem evalYulExpr_selectorExpr_eq (state : YulState)
    (hselector : state.selector < selectorModulus) :
    evalYulExpr state selectorExpr = some state.selector :=
by
  simp [Nat.mod_eq_of_lt hselector]

/-- Dispatch body emitted for one external function case. -/
def switchCaseBody (fn : IRFunction) : List YulStmt :=
  let valueGuard := if fn.payable then [] else [Compiler.callvalueGuard]
  [YulStmt.comment s!"{fn.name}()"] ++ valueGuard ++ [Compiler.calldatasizeGuard fn.params.length] ++ fn.body

/-- Switch cases generated from IR functions. -/
def switchCases (fns : List IRFunction) : List (Prod Nat (List YulStmt)) :=
  fns.map (fun f => (f.selector, switchCaseBody f))

/-- Default dispatch body used by `buildSwitch`. -/
def switchDefaultCase
    (fallback : Option IREntrypoint)
    (receive : Option IREntrypoint) : List YulStmt :=
  match receive, fallback with
  | none, none =>
      [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
  | none, some fb =>
      let valueGuard := if fb.payable then [] else [Compiler.callvalueGuard]
      [YulStmt.comment "fallback()"] ++ valueGuard ++ fb.body
  | some rc, none =>
      let receiveGuard := if rc.payable then [] else [Compiler.callvalueGuard]
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          ([YulStmt.comment "receive()"] ++ receiveGuard ++ rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])]
      ]]
  | some rc, some fb =>
      let receiveGuard := if rc.payable then [] else [Compiler.callvalueGuard]
      let fallbackGuard := if fb.payable then [] else [Compiler.callvalueGuard]
      [YulStmt.block [
        YulStmt.let_ "__is_empty_calldata" (YulExpr.call "eq" [YulExpr.call "calldatasize" [], YulExpr.lit 0]),
        YulStmt.if_ (YulExpr.ident "__is_empty_calldata")
          ([YulStmt.comment "receive()"] ++ receiveGuard ++ rc.body),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__is_empty_calldata"])
          ([YulStmt.comment "fallback()"] ++ fallbackGuard ++ fb.body)
      ]]

/-- If the selector matches a case, the switch executes that case body (fueled). -/
private theorem execYulStmtFuel_switch_match
    (state : YulState) (expr : YulExpr) (cases' : List (Prod Nat (List YulStmt)))
    (defaultCase : Option (List YulStmt)) (fuel v : Nat) (body : List YulStmt)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = some (v, body)) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' defaultCase) =
      execYulStmtsFuel fuel state body := by
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, execYulStmtsFuel, legacyExecYulFuel, hEval, hFind]
  | succ fuel =>
      simp [execYulStmtFuel, execYulStmtsFuel, legacyExecYulFuel, hEval, hFind]

/-- If no selector case matches, the switch executes the default (or continues). -/
private def execYulStmtFuel_switch_miss_result (state : YulState) (fuel : Nat)
    (defaultCase : Option (List YulStmt)) : YulExecResult :=
  match defaultCase with
  | some body => execYulStmtsFuel fuel state body
  | none => YulExecResult.continue state

private theorem execYulStmtFuel_switch_miss
    (state : YulState) (expr : YulExpr) (cases' : List (Prod Nat (List YulStmt)))
    (defaultCase : Option (List YulStmt)) (fuel v : Nat)
    (hEval : evalYulExpr state expr = some v)
    (hFind : List.find? (fun (c, _) => c = v) cases' = none) :
    execYulStmtFuel (Nat.succ fuel) state (YulStmt.switch expr cases' defaultCase) =
      execYulStmtFuel_switch_miss_result state fuel defaultCase := by
  cases fuel with
  | zero =>
      simp [execYulStmtFuel, execYulStmtsFuel, legacyExecYulFuel, hEval, hFind,
        execYulStmtFuel_switch_miss_result]
      rfl
  | succ fuel =>
      simp [execYulStmtFuel, execYulStmtsFuel, legacyExecYulFuel, hEval, hFind,
        execYulStmtFuel_switch_miss_result]
      rfl

/- Bridge lemmas for switch-case lookup. -/
private theorem find_switch_case_of_find_function
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

/-- Selector-specialized variant: if `find?` hits `fn` at `sel`, the switch case
lookup returns the same selector `sel` paired with `switchCaseBody fn`. -/
private theorem find_switch_case_of_find_function_eq_selector
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

private theorem find_switch_case_of_find_function_none
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


/-! ## Runtime code reduction lemmas -/

/-- Function definitions are no-ops in execution. -/
@[simp] theorem execYulStmtFuel_funcDef (fuel : Nat) (state : YulState)
    (name : String) (params ret : List String) (body : List YulStmt) :
    execYulStmtFuel fuel state (YulStmt.funcDef name params ret body) =
      YulExecResult.continue state := by
  cases fuel <;> simp [execYulStmtFuel, legacyExecYulFuel]

/-- `legacyExecYulFuel` on a funcDef target gives `.continue state` for any fuel. -/
@[simp] theorem legacyExecYulFuel_funcDef (fuel : Nat) (state : YulState)
    (name : String) (params ret : List String) (body : List YulStmt) :
    legacyExecYulFuel fuel state (.stmt (YulStmt.funcDef name params ret body)) =
      YulExecResult.continue state := by
  cases fuel <;> simp [legacyExecYulFuel]

/-- Stepping through a funcDef in a statement list consumes one fuel unit. -/
@[simp] theorem execYulStmtsFuel_cons_funcDef (fuel : Nat) (state : YulState)
    (name : String) (params ret : List String) (body rest : List YulStmt) :
    execYulStmtsFuel (Nat.succ fuel) state (YulStmt.funcDef name params ret body :: rest) =
      execYulStmtsFuel fuel state rest := by
  simp only [execYulStmtsFuel, legacyExecYulFuel]
  rw [legacyExecYulFuel_funcDef]

/-- Executing funcDef statements followed by a suffix: the funcDefs are no-ops
and each one burns one fuel unit. -/
private theorem execYulStmtsFuel_funcDefs_then_suffix (fuel : Nat) (state : YulState)
    (prefix_ : List YulStmt) (suffix_ : List YulStmt)
    (hFuncDefs : ∀ s ∈ prefix_, ∃ nm p r b, s = YulStmt.funcDef nm p r b) :
    execYulStmtsFuel (prefix_.length + fuel) state (prefix_ ++ suffix_) =
      execYulStmtsFuel fuel state suffix_ := by
  induction prefix_ generalizing state with
  | nil => simp
  | cons h t ih =>
      have hmem : h ∈ h :: t := .head t
      obtain ⟨nm, p, r, b, rfl⟩ := hFuncDefs h hmem
      simp only [List.cons_append, List.length_cons]
      conv_lhs => rw [show t.length + 1 + fuel = Nat.succ (t.length + fuel) from by omega]
      rw [execYulStmtsFuel_cons_funcDef]
      exact ih state (fun s hs => hFuncDefs s (List.mem_cons_of_mem _ hs))

/-- Variant with `fuel ≥ prefix_.length` instead of exact `prefix_.length + fuel`. -/
private theorem execYulStmtsFuel_funcDefs_then_suffix_ge (fuel : Nat) (state : YulState)
    (prefix_ : List YulStmt) (suffix_ : List YulStmt)
    (hFuncDefs : ∀ s ∈ prefix_, ∃ nm p r b, s = YulStmt.funcDef nm p r b)
    (hFuel : fuel ≥ prefix_.length) :
    execYulStmtsFuel fuel state (prefix_ ++ suffix_) =
      execYulStmtsFuel (fuel - prefix_.length) state suffix_ := by
  have : fuel = prefix_.length + (fuel - prefix_.length) := by omega
  conv_lhs => rw [this]
  exact execYulStmtsFuel_funcDefs_then_suffix _ state prefix_ suffix_ hFuncDefs

end Compiler.Proofs.YulGeneration
