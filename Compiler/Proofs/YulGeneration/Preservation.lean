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
-/-

/-- Results match when success, return value, and storage/mapping functions agree. -/
def resultsMatch (ir : IRResult) (yul : YulResult) : Prop :=
  ir.success = yul.success ∧
  ir.returnValue = yul.returnValue ∧
  (∀ slot, ir.finalStorage slot = yul.finalStorage slot) ∧
  (∀ base key, ir.finalMappings base key = yul.finalMappings base key)

/-- Interpret just a function body as Yul runtime code. -/
def interpretYulBody (fn : IRFunction) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime fn.body yulTx state.storage state.mappings

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
  -- Case split on whether the selector matches a function.
  cases hFind : contract.functions.find? (fun f => f.selector == tx.functionSelector) with
  | none =>
      -- IR interpreter reverts on missing selector.
      simp [interpretIR, hFind, interpretYulFromIR, interpretYulRuntime, irState,
        emitYul_runtimeCode_eq]
  | some fn =>
      -- Use the function-body preservation hypothesis.
      have hmem : fn ∈ contract.functions := by
        exact List.mem_of_find?_eq_some hFind
      have hmatch := hbody fn hmem
      -- Unfold Yul runtime dispatch and reduce the switch.
      -- The runtime code is the switch (mapping helper is a no-op).
      simp [interpretIR, hFind, interpretYulFromIR, interpretYulRuntime, irState,
        emitYul_runtimeCode_eq, execYulStmts_runtimeCode_eq, Compiler.runtimeCode,
        Compiler.buildSwitch, selectorExpr] at hmatch ⊢
      -- Selector extraction is deterministic.
      -- The switch cases align with `find?` on selectors.
      have hcase :
          (contract.functions.map (fun f =>
            let body := [YulStmt.comment s!"{f.name}()"] ++ f.body
            (f.selector, body)
          )).find? (fun (c, _) => c = tx.functionSelector) =
            some (fn.selector, [YulStmt.comment s!"{fn.name}()"] ++ fn.body) := by
        exact find_switch_case_of_find_function contract.functions tx.functionSelector fn hFind
      -- Apply switch rule.
      have hsel :
          evalYulExpr (YulState.initial {
            sender := tx.sender
            functionSelector := tx.functionSelector
            args := tx.args
          } irState.storage irState.mappings) selectorExpr =
            some (tx.functionSelector % selectorModulus) := by
        simpa using (evalYulExpr_selectorExpr
          (YulState.initial {
            sender := tx.sender
            functionSelector := tx.functionSelector
            args := tx.args
          } irState.storage irState.mappings))
      have hsel' : tx.functionSelector % selectorModulus = tx.functionSelector := by
        exact Nat.mod_eq_of_lt hselector
      -- Finish by aligning the switch-selected body with the hypothesis.
      simp [hsel, hsel', hcase] at hmatch
      exact hmatch

end Compiler.Proofs.YulGeneration
