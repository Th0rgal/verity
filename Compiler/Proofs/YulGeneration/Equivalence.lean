import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Semantics

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Proofs.IRGeneration
open Compiler.Yul

/-! ## IR ↔ Yul State Alignment -/

def yulStateOfIR (selector : Nat) (state : IRState) : YulState :=
  { vars := state.vars
    storage := state.storage
    mappings := state.mappings
    memory := state.memory
    calldata := state.calldata
    selector := selector
    returnValue := state.returnValue
    sender := state.sender }

def statesAligned (selector : Nat) (ir : IRState) (yul : YulState) : Prop :=
  yul = yulStateOfIR selector ir

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

/-- Interpret just a function body as Yul runtime code. -/
noncomputable def interpretYulBody (fn : IRFunction) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := {
    sender := tx.sender
    functionSelector := tx.functionSelector
    args := tx.args
  }
  interpretYulRuntime fn.body yulTx state.storage state.mappings

set_option allowUnsafeReducibility true in
attribute [reducible] execIRStmts

def resultsMatchOn (slots : List Nat) (mappingKeys : List (Nat × Nat))
    (ir : IRResult) (yul : YulResult) : Bool :=
  ir.success == yul.success &&
  ir.returnValue == yul.returnValue &&
  slots.all (fun slot => ir.finalStorage slot == yul.finalStorage slot) &&
  mappingKeys.all (fun (base, key) => ir.finalMappings base key == yul.finalMappings base key)

/-! ## Layer 3 Equivalence Scaffolding

These statements capture the generic proof shape for IR → Yul equivalence.
They are intentionally parameterized so contract-level results become
mechanical instantiations once the instruction-level lemmas are proven.
-/

def execResultsAligned (selector : Nat) : IRExecResult → YulExecResult → Prop
  | .continue ir, .continue yul => statesAligned selector ir yul
  | .return v ir, .return v' yul => v = v' ∧ statesAligned selector ir yul
  | .stop ir, .stop yul => statesAligned selector ir yul
  | .revert ir, .revert yul => statesAligned selector ir yul
  | _, _ => False

/-- Results match when success, return value, and storage/mapping functions agree. -/
def resultsMatch (ir : IRResult) (yul : YulResult) : Prop :=
  ir.success = yul.success ∧
  ir.returnValue = yul.returnValue ∧
  (∀ slot, ir.finalStorage slot = yul.finalStorage slot) ∧
  (∀ base key, ir.finalMappings base key = yul.finalMappings base key)

/-- Instruction-level equivalence goal: single IR statement matches Yul statement. -/
def execIRStmt_equiv_execYulStmt_goal
    (selector : Nat) (stmt : YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmt irState stmt) (execYulStmt yulState stmt)

/-- Sequence/program equivalence goal: statement lists compose under alignment. -/
def execIRStmts_equiv_execYulStmts_goal
    (selector : Nat) (stmts : List YulStmt) (irState : IRState) (yulState : YulState) : Prop :=
    statesAligned selector irState yulState →
    execResultsAligned selector (execIRStmts irState stmts) (execYulStmts yulState stmts)

/-- Generic function equivalence goal: holds for any IR function and its compiled Yul body. -/
def ir_yul_function_equiv_goal
    (fn : IRFunction) (tx : IRTransaction) (state : IRState) : Prop :=
    tx.functionSelector < selectorModulus →
    resultsMatch
      (execIRFunction fn tx.args { state with sender := tx.sender, calldata := tx.args })
      (interpretYulBody fn tx { state with sender := tx.sender, calldata := tx.args })

/-! ## Generic Layer 3 Lemmas (Fuel-Agnostic)

These lemmas lift instruction-level equivalence to sequences and function
bodies. They do not assume any specific instruction equivalence proof;
instead, they require it as a parameter and then compose it.
-/

theorem statesAligned_refl (selector : Nat) (state : IRState) :
    statesAligned selector state (yulStateOfIR selector state) := by
  rfl

/-! ## Fuel-Parametric Sequencing Lemmas

These unfolding lemmas expose how `execYulStmtsFuel` consumes one unit of
fuel before executing the first statement. They are intended as building
blocks for the generic sequence equivalence proof.
-/

theorem execYulStmtsFuel_nil (fuel : Nat) (state : YulState) :
    execYulStmtsFuel fuel state [] = .continue state := by
  cases fuel <;> rfl

theorem execYulStmtsFuel_cons
    (fuel : Nat) (state : YulState) (stmt : YulStmt) (rest : List YulStmt) :
    execYulStmtsFuel (Nat.succ fuel) state (stmt :: rest) =
      match execYulStmtFuel fuel state stmt with
      | .continue s' => execYulStmtsFuel fuel s' rest
      | .return v s => .return v s
      | .stop s => .stop s
      | .revert s => .revert s := by
  rfl


/-! ## Generic Sequence Equivalence (TODO)

We still need a compositional lemma that lifts `stmt_equiv` to statement
lists with fuel/length constraints. This will live here once `execIRStmts`
can be unfolded safely in proof contexts.
-/


end Compiler.Proofs.YulGeneration
