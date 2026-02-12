/-
  IRInterpreter: Execution semantics for IR (Yul-based intermediate representation)

  This defines how IR contracts execute, enabling proofs that spec→IR compilation preserves semantics.

  Key differences from SpecInterpreter:
  - IR uses Yul expressions (ident, call) instead of high-level Spec expressions (storage, param)
  - IR has explicit variables and assignment instead of automatic scoping
  - IR is lower-level but simpler to reason about than full spec interpreter
-/

import Compiler.IR
import Compiler.ContractSpec
import Compiler.Proofs.SpecInterpreter
import DumbContracts.Core

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Yul
open DumbContracts.Core

/-! ## Execution State for IR -/

structure IRState where
  /-- Variable bindings (name → value) -/
  vars : List (String × Nat)
  /-- Storage slots (slot → value) -/
  storage : Nat → Nat
  /-- Storage mappings (baseSlot → key → value) -/
  mappings : Nat → Nat → Nat
  /-- Return value (if any) -/
  returnValue : Option Nat
  /-- Sender address -/
  sender : Nat
  deriving Nonempty

/-- Initial state for IR execution -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    mappings := fun _ _ => 0
    returnValue := none
    sender := sender }

/-- Lookup variable in state -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-! ## IR Expression Evaluation -/

/-- Evaluate a Yul expression in the IR context -/
partial def evalIRExpr (state : IRState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none  -- Strings not supported in our IR subset
  | .ident name => state.getVar name
  | .call func args => do
    let argVals ← args.mapM (evalIRExpr state)
    match func, argVals with
    | "add", [a, b] => some ((a + b) % (2^256))  -- EVM modular arithmetic
    | "sub", [a, b] => some ((a - b) % (2^256))
    | "mul", [a, b] => some ((a * b) % (2^256))
    | "div", [a, b] => if b = 0 then some 0 else some (a / b)
    | "mod", [a, b] => if b = 0 then some 0 else some (a % b)
    | "lt", [a, b] => some (if a < b then 1 else 0)
    | "gt", [a, b] => some (if a > b then 1 else 0)
    | "eq", [a, b] => some (if a = b then 1 else 0)
    | "iszero", [a] => some (if a = 0 then 1 else 0)
    | "and", [a, b] => some (a &&& b)  -- Bitwise AND
    | "or", [a, b] => some (a ||| b)   -- Bitwise OR
    | "sload", [slot] => some (state.storage slot)
    | "caller", [] => some state.sender
    | _, _ => none  -- Unknown or invalid function call

/-! ## IR Statement Execution -/

/-- Result of executing IR statements -/
inductive IRExecResult
  | continue (state : IRState)
  | return (value : Nat) (state : IRState)
  | revert (state : IRState)
  deriving Nonempty

mutual

/-- Execute a single Yul statement -/
partial def execIRStmt (state : IRState) : YulStmt → IRExecResult
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
    -- Expression statements for side effects (like sstore)
    match e with
    | .call "sstore" [slotExpr, valExpr] =>
      match evalIRExpr state slotExpr, evalIRExpr state valExpr with
      | some slot, some val =>
        .continue { state with storage := fun s => if s = slot then val else state.storage s }
      | _, _ => .revert state
    | .call "revert" _ => .revert state
    | .call "return" [valExpr] =>
      match evalIRExpr state valExpr with
      | some v => .return v state
      | none => .revert state
    | _ => .continue state  -- Other expressions are no-ops
  | .if_ cond body =>
    match evalIRExpr state cond with
    | some c => if c ≠ 0 then execIRStmts state body else .continue state
    | none => .revert state
  | .switch expr cases default =>
    match evalIRExpr state expr with
    | some v =>
      match cases.find? (·.1 == v) with
      | some (_, body) => execIRStmts state body
      | none =>
        match default with
        | some body => execIRStmts state body
        | none => .continue state
    | none => .revert state
  | .block stmts => execIRStmts state stmts
  | .funcDef _ _ _ _ => .continue state  -- Function definitions don't execute

/-- Execute a sequence of IR statements -/
partial def execIRStmts (state : IRState) : List YulStmt → IRExecResult
  | [] => .continue state
  | stmt :: rest =>
    match execIRStmt state stmt with
    | .continue s' => execIRStmts s' rest
    | .return v s => .return v s
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

/-- Execute an IR function with given arguments -/
def execIRFunction (fn : IRFunction) (args : List Nat) (initialState : IRState) : IRResult :=
  -- Initialize parameters as variables
  let stateWithParams := fn.params.zip args |>.foldl
    (fun s (p, v) => s.setVar p.name v)
    initialState

  match execIRStmts stateWithParams fn.body with
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
  | .revert s =>
    { success := false
      returnValue := none
      finalStorage := s.storage
      finalMappings := s.mappings }

/-- Interpret an entire IR contract execution -/
def interpretIR (contract : IRContract) (tx : IRTransaction) : IRResult :=
  let initialState := IRState.initial tx.sender

  -- Find matching function by selector
  match contract.functions.find? (·.selector == tx.functionSelector) with
  | some fn => execIRFunction fn tx.args initialState
  | none =>
    { success := false
      returnValue := none
      finalStorage := initialState.storage
      finalMappings := initialState.mappings }

end Compiler.Proofs.IRGeneration
