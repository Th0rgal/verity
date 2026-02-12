import Compiler.Proofs.YulGeneration.Codegen
import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Codegen Preservation Theorem (Layer 3)

We prove that Yul code generation preserves IR semantics, assuming that
executing an IR function body matches executing the same Yul statements.
-/

/-- Results match when success, return value, and storage/mapping functions agree. -/
def resultsMatch (ir : IRResult) (yul : YulResult) : Prop :=
  ir.success = yul.success ∧
  ir.returnValue = yul.returnValue ∧
  (∀ slot, ir.finalStorage slot = yul.finalStorage slot) ∧
  (∀ base key, ir.finalMappings base key = yul.finalMappings base key)

/-- Interpret just a function body as Yul runtime code. -/
noncomputable def interpretYulBody (fn : IRFunction) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime fn.body yulTx state.storage state.mappings

/-- Helper: initial Yul state aligned with the IR transaction/state. -/
def initialYulState (tx : YulTransaction) (state : IRState) : YulState :=
  YulState.initial tx state.storage state.mappings

@[simp]
theorem evalYulExpr_selectorExpr_initial
    (tx : YulTransaction) (state : IRState)
    (hselector : tx.functionSelector < selectorModulus) :
    evalYulExpr (initialYulState tx state) selectorExpr = some tx.functionSelector := by
  simpa using (evalYulExpr_selectorExpr_eq (initialYulState tx state) hselector)

/-- Main preservation theorem: Yul codegen preserves IR semantics. -/
theorem yulCodegen_preserves_semantics
    (contract : IRContract) (tx : IRTransaction) (initialState : IRState)
    (hselector : tx.functionSelector < selectorModulus)
    (hbody : ∀ fn, fn ∈ contract.functions →
      resultsMatch
        (execIRFunction fn tx.args { initialState with sender := tx.sender, calldata := tx.args })
        (interpretYulBody fn tx { initialState with sender := tx.sender, calldata := tx.args })) :
    resultsMatch
      (interpretIR contract tx initialState)
      (interpretYulFromIR contract tx initialState) := by
  -- Normalize the initial IR state with sender/calldata.
  let irState := { initialState with sender := tx.sender, calldata := tx.args }
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  -- Case split on whether the selector matches a function.
  cases hFind : contract.functions.find? (fun f => f.selector == tx.functionSelector) with
  | none =>
      -- IR interpreter reverts on missing selector.
      have hcase :
          (switchCases contract.functions).find? (fun (c, _) => c = tx.functionSelector) = none := by
        exact find_switch_case_of_find_function_none contract.functions tx.functionSelector hFind
      have hsel :
          evalYulExpr (initialYulState yulTx irState) selectorExpr =
            some tx.functionSelector := by
        simpa [yulTx] using (evalYulExpr_selectorExpr_initial yulTx irState hselector)
      simp [interpretIR, hFind, interpretYulFromIR, interpretYulRuntime, irState,
        execYulStmts, execYulStmtsFuel, execYulStmts_runtimeCode_eq,
        emitYul_runtimeCode_eq, Compiler.runtimeCode, hcase, hsel]
  | some fn =>
      -- Use the function-body preservation hypothesis.
      have hmem : fn ∈ contract.functions := by
        exact List.mem_of_find?_eq_some hFind
      have hmatch := hbody fn hmem
      -- Selector extraction is deterministic.
      -- The switch cases align with `find?` on selectors.
      have hcase :
          (switchCases contract.functions).find? (fun (c, _) => c = tx.functionSelector) =
            some (fn.selector, [YulStmt.comment s!"{fn.name}()"] ++ fn.body) := by
        exact find_switch_case_of_find_function contract.functions tx.functionSelector fn hFind
      -- Apply switch rule.
      have hsel :
          evalYulExpr (initialYulState yulTx irState) selectorExpr =
            some tx.functionSelector := by
        simpa [yulTx] using (evalYulExpr_selectorExpr_initial yulTx irState hselector)
      -- Unfold Yul runtime dispatch and reduce the switch.
      -- The runtime code is the switch (mapping helper is a no-op).
      simp [interpretIR, hFind, interpretYulFromIR, interpretYulRuntime, irState,
        execYulStmts, execYulStmtsFuel, execYulStmts_runtimeCode_eq,
        emitYul_runtimeCode_eq, Compiler.runtimeCode, hsel, hcase] at hmatch ⊢
      -- Finish by aligning the switch-selected body with the hypothesis.
      exact hmatch

end Compiler.Proofs.YulGeneration
