import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Bridging IR and Yul Semantics

These helpers wire IR-level execution to Yul runtime execution so we can
compare results directly in smoke tests.
-/

noncomputable def interpretYulFromIR (contract : IRContract) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime (Compiler.emitYul contract).runtimeCode yulTx state.storage state.mappings

/-- Align a Yul state with an IR transaction/state (used for equivalence lemmas). -/
def alignedYulState (tx : IRTransaction) (state : IRState) : YulState :=
  YulState.initial
    { sender := tx.sender, functionSelector := tx.functionSelector, args := tx.args }
    state.storage
    state.mappings

theorem evalYulExpr_calldataload_ge4
    (tx : IRTransaction) (state : IRState) (offset : Nat) (hOffset : 4 <= offset) :
    evalYulExpr (alignedYulState tx state) (YulExpr.call "calldataload" [YulExpr.lit offset]) =
      if (offset - 4) % 32 = 0 then
        some (tx.args[(offset - 4) / 32]?.getD 0 % evmModulus)
      else
        some 0 := by
  have hnotlt : ¬ offset < 4 := Nat.not_lt_of_ge hOffset
  have hne : offset ≠ 0 := by
    intro hzero
    subst hzero
    exact hnotlt (by decide : 0 < 4)
  simp [evalYulExpr, evalYulCall, evalYulExprs, alignedYulState, YulState.initial, hne, hnotlt]

def resultsMatchOn (slots : List Nat) (mappingKeys : List (Nat × Nat))
    (ir : IRResult) (yul : YulResult) : Bool :=
  ir.success == yul.success &&
  ir.returnValue == yul.returnValue &&
  slots.all (fun slot => ir.finalStorage slot == yul.finalStorage slot) &&
  mappingKeys.all (fun (base, key) => ir.finalMappings base key == yul.finalMappings base key)

end Compiler.Proofs.YulGeneration
