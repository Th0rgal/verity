/-
  IRInterpreter: Execution semantics for IR (Yul-based intermediate representation)

  This defines how IR contracts execute, enabling proofs that spec→IR compilation preserves semantics.

  Key differences from SpecInterpreter:
  - IR uses Yul expressions (ident, call) instead of high-level Spec expressions (storage, param)
  - IR has explicit variables and assignment instead of automatic scoping
  - IR is lower-level but simpler to reason about than full spec interpreter

  All functions in this module are **total** (no `partial` annotations):
  - Expression evaluators use structural recursion on expression size (exprSize/exprsSize)
  - Statement executors use an explicit fuel parameter

  This eliminates 3 axioms that were previously needed to bridge partial and total definitions.
  See Issue #148 for the full motivation.
-/

import Compiler.IR
import Compiler.ContractSpec
import Compiler.Proofs.MappingSlot
import Compiler.Proofs.YulGeneration.Builtins
import Verity.Proofs.Stdlib.SpecInterpreter
import Verity.Core

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Yul
open Verity.Core
open Compiler.Proofs

/-! ## Execution State for IR -/

structure IRState where
  /-- Variable bindings (name → value) -/
  vars : List (String × Nat)
  /-- Storage slots (slot → value) -/
  storage : Nat → Nat
  /-- Storage mappings (baseSlot → key → value) -/
  mappings : Nat → Nat → Nat
  /-- Memory words (offset → value) -/
  memory : Nat → Nat
  /-- Calldata words (argument index → value) -/
  calldata : List Nat
  /-- Return value (if any) -/
  returnValue : Option Nat
  /-- Sender address -/
  sender : Nat
  /-- Function selector (4-byte value used by calldataload(0)) -/
  selector : Nat
  deriving Nonempty

/-- Initial state for IR execution -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    mappings := fun _ _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := sender
    selector := 0 }

/-- Lookup variable in state -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-! ## IR Expression Evaluation (Total)

Expression evaluators use structural recursion on expression size, matching the
pattern already used by `evalYulExpr` in `Semantics.lean`. The `exprSize`/`exprsSize`
measures from Semantics.lean are reused.
-/

/-!
Mapping slots in Yul are derived via keccak(baseSlot, key). IR proof semantics
call through the `MappingSlot` abstraction; the current backend is tagged
encoding so `sload`/`sstore` can route to `mappings` instead of flat storage.
-/

open Compiler.Proofs.YulGeneration in
mutual

/-- Evaluate a list of Yul expressions in the IR context.

Total: uses `exprsSize` for termination (structural recursion on expression tree). -/
def evalIRExprs (state : IRState) : List YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalIRExpr state e
    let vs ← evalIRExprs state es
    pure (v :: vs)
termination_by es => exprsSize es
decreasing_by
  all_goals
    simp [exprsSize, exprSize]
    omega

/-- Evaluate an IR function call by evaluating all arguments first, then dispatching.

Total: uses `exprsSize args + 1` for termination. Evaluating args decreases the measure.

NOTE: This function always evaluates all arguments via `evalIRExprs` before dispatching,
matching the structure of `evalYulCall` in Semantics.lean. For `sload`, mapping slot
routing uses `Compiler.Proofs.abstractDecodeMappingSlot` on the evaluated slot value
(not pattern-matching on the argument expression). This makes the function structurally
identical to the Yul version, enabling direct equivalence proofs without axioms. -/
def evalIRCall (state : IRState) (func : String) : List YulExpr → Option Nat
  | args => do
    let argVals ← evalIRExprs state args
    Compiler.Proofs.YulGeneration.evalBuiltinCallWithBackend
      Compiler.Proofs.YulGeneration.defaultBuiltinBackend
      state.storage state.mappings state.sender state.selector state.calldata func argVals
termination_by args => exprsSize args + 1
decreasing_by
  simp [exprsSize, exprSize]

/-- Evaluate a Yul expression in the IR context.

Total: uses `exprSize` for termination (structural recursion on expression tree). -/
def evalIRExpr (state : IRState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none  -- Strings not supported in our IR subset
  | .ident name => state.getVar name
  | .call func args => evalIRCall state func args
termination_by e => exprSize e
decreasing_by
  simp [exprsSize, exprSize]

end -- mutual

/-! ## IR Statement Execution (Fuel-Based, Total)

Statement executors use an explicit fuel parameter to ensure totality.
This eliminates the need for `partial def` and the corresponding
`execIRStmtsFuel_adequate` axiom. The fuel-based versions are now the
canonical definitions.
-/

/-- Result of executing IR statements -/
inductive IRExecResult
  | continue (state : IRState)
  | return (value : Nat) (state : IRState)
  | stop (state : IRState)
  | revert (state : IRState)
  deriving Nonempty

mutual

/-- Execute a single Yul statement with fuel bound.

Total: uses explicit fuel parameter for recursion control.
When fuel is 0, execution reverts (safe fallback). -/
def execIRStmt : Nat → IRState → YulStmt → IRExecResult
  | 0, state, _ => .revert state  -- Out of fuel
  | Nat.succ fuel, state, stmt =>
      match stmt with
      | .comment _ => .continue state
      | .let_ name value =>
          match evalIRExpr state value with
          | some v => .continue (state.setVar name v)
          | none => .revert state
      | .assign name value =>
          match evalIRExpr state value with
          | some v => .continue (state.setVar name v)
          | none => .revert state
      | .expr e =>
          match e with
          | .call "sstore" [slotExpr, valExpr] =>
              match slotExpr with
              | .call "mappingSlot" [baseExpr, keyExpr] =>
                  match evalIRExpr state baseExpr, evalIRExpr state keyExpr, evalIRExpr state valExpr with
                  | some baseSlot, some key, some val =>
                      let updated := Compiler.Proofs.abstractStoreMappingEntry
                        state.storage state.mappings baseSlot key val
                      .continue {
                        state with
                        storage := updated.1
                        mappings := updated.2
                      }
                  | _, _, _ => .revert state
              | _ =>
                  match evalIRExpr state slotExpr, evalIRExpr state valExpr with
                  | some slot, some val =>
                      let updated := Compiler.Proofs.abstractStoreStorageOrMapping
                        state.storage state.mappings slot val
                      .continue {
                        state with
                        storage := updated.1
                        mappings := updated.2
                      }
                  | _, _ => .revert state
          | .call "mstore" [offsetExpr, valExpr] =>
              match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
              | some offset, some val =>
                .continue { state with memory := fun o => if o = offset then val else state.memory o }
              | _, _ => .revert state
          | .call "stop" [] => .stop state
          | .call "revert" _ => .revert state
          | .call "return" [offsetExpr, sizeExpr] =>
              match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
              | some offset, some size =>
                if size = 32 then
                  .return (state.memory offset) state
                else
                  .return 0 state
              | _, _ => .revert state
          | _ => .continue state  -- Other expressions are no-ops
      | .if_ cond body =>
          match evalIRExpr state cond with
          | some c => if c ≠ 0 then execIRStmts fuel state body else .continue state
          | none => .revert state
      | .switch expr cases default =>
          match evalIRExpr state expr with
          | some v =>
            match cases.find? (·.1 == v) with
            | some (_, body) => execIRStmts fuel state body
            | none =>
              match default with
              | some body => execIRStmts fuel state body
              | none => .continue state
          | none => .revert state
      | .for_ init cond post body =>
          -- Execute init, then loop: check cond, run body, run post, repeat
          match execIRStmts fuel state init with
          | .continue s' =>
              match evalIRExpr s' cond with
              | some v =>
                  if v ≠ 0 then
                    match execIRStmts fuel s' body with
                    | .continue s'' =>
                        match execIRStmts fuel s'' post with
                        | .continue s''' => execIRStmt fuel s''' (.for_ [] cond post body)
                        | other => other
                    | other => other
                  else .continue s'
              | none => .revert s'
          | other => other
      | .block stmts => execIRStmts fuel state stmts
      | .funcDef _ _ _ _ => .continue state

/-- Execute a sequence of IR statements with fuel bound.

Total: uses explicit fuel parameter for recursion control. -/
def execIRStmts (fuel : Nat) (state : IRState) : List YulStmt → IRExecResult
  | [] => .continue state
  | stmt :: rest =>
      match fuel with
      | 0 => .revert state
      | Nat.succ fuel =>
          match execIRStmt fuel state stmt with
          | .continue s' => execIRStmts fuel s' rest
          | .return v s => .return v s
          | .stop s => .stop s
          | .revert s => .revert s

end -- mutual

/-! ## IR Function Execution -/

structure IRTransaction where
  sender : Nat
  functionSelector : Nat
  args : List Nat
  deriving Repr

structure IRResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  finalMappings : Nat → Nat → Nat

/-- Execute an IR function with given arguments.
Uses `sizeOf fn.body + 1` fuel, which is sufficient for any terminating execution
of a non-looping function body. -/
def execIRFunction (fn : IRFunction) (args : List Nat) (initialState : IRState) : IRResult :=
  -- Initialize parameters as variables
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState

  match execIRStmts (sizeOf fn.body + 1) stateWithParams fn.body with
  | .continue s =>
    { success := true
      returnValue := s.returnValue
      finalStorage := s.storage
      finalMappings := s.mappings }
  | .return v s =>
    { success := true
      returnValue := some v
      finalStorage := s.storage
      finalMappings := s.mappings }
  | .stop s =>
    { success := true
      returnValue := none
      finalStorage := s.storage
      finalMappings := s.mappings }
  | .revert s =>
    { success := false
      returnValue := none
      -- On revert, storage and mappings roll back to the initial state
      finalStorage := initialState.storage
      finalMappings := initialState.mappings }

/-- Interpret an entire IR contract execution -/
def interpretIR (contract : IRContract) (tx : IRTransaction) (initialState : IRState) : IRResult :=
  -- Execution sender and selector come from the transaction (matches SpecInterpreter)
  let initialState := { initialState with sender := tx.sender, calldata := tx.args, selector := tx.functionSelector }

  -- Find matching function by selector
  match contract.functions.find? (·.selector == tx.functionSelector) with
  | some fn => execIRFunction fn tx.args initialState
  | none =>
    { success := false
      returnValue := none
      finalStorage := initialState.storage
      finalMappings := initialState.mappings }

end Compiler.Proofs.IRGeneration
