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
import Compiler.Proofs.MappingEncoding
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import DumbContracts.Core

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Yul
open DumbContracts.Core
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
  deriving Nonempty

/-- Initial state for IR execution -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    mappings := fun _ _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := sender }

/-- Lookup variable in state -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-! ## IR Expression Evaluation -/

abbrev evmModulus : Nat := Compiler.Proofs.evmModulus

/-!
Mapping slots in Yul are derived via keccak(baseSlot, key). For proofs, we model
them with a tagged encoding so `sload`/`sstore` can route to `mappings` rather
than flat `storage`. The tag is `2^256`, which is outside the EVM word range,
so it cannot collide with real storage slots produced by arithmetic.
-/
abbrev mappingTag : Nat := Compiler.Proofs.mappingTag
abbrev encodeMappingSlot := Compiler.Proofs.encodeMappingSlot
abbrev decodeMappingSlot := Compiler.Proofs.decodeMappingSlot

mutual

/-- Evaluate a list of Yul expressions in the IR context -/
partial def evalIRExprs (state : IRState) : List YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalIRExpr state e
    let vs ← evalIRExprs state es
    pure (v :: vs)
partial def evalIRCall (state : IRState) (func : String) : List YulExpr → Option Nat
  | args => do
    match func, args with
  | "mappingSlot", [baseExpr, keyExpr] => do
      let base ← evalIRExpr state baseExpr
      let key ← evalIRExpr state keyExpr
      pure (encodeMappingSlot base key)
  | "sload", [slotExpr] => do
      match slotExpr with
      | .call "mappingSlot" [baseExpr, keyExpr] => do
          let base ← evalIRExpr state baseExpr
          let key ← evalIRExpr state keyExpr
          pure (state.mappings base key)
      | _ => do
          let slot ← evalIRExpr state slotExpr
          match decodeMappingSlot slot with
          | some (baseSlot, key) => pure (state.mappings baseSlot key)
          | none => pure (state.storage slot)
  | _, _ =>
      let argVals ← evalIRExprs state args
      match func, argVals with
      | "add", [a, b] => some ((a + b) % evmModulus)  -- EVM modular arithmetic
      | "sub", [a, b] =>
          -- EVM SUB uses modular two's-complement wrapping, not truncating subtraction
          -- If a >= b: result is a - b
          -- If a < b: result wraps around: 2^256 - (b - a) = 2^256 + a - b
          some ((evmModulus + a - b) % evmModulus)
      | "mul", [a, b] => some ((a * b) % evmModulus)
      | "div", [a, b] => if b = 0 then some 0 else some (a / b)
      | "mod", [a, b] => if b = 0 then some 0 else some (a % b)
      | "lt", [a, b] => some (if a < b then 1 else 0)
      | "gt", [a, b] => some (if a > b then 1 else 0)
      | "eq", [a, b] => some (if a = b then 1 else 0)
      | "iszero", [a] => some (if a = 0 then 1 else 0)
      | "and", [a, b] => some (a &&& b)  -- Bitwise AND
      | "or", [a, b] => some (a ||| b)   -- Bitwise OR
      | "xor", [a, b] => some (Nat.xor a b)
      | "not", [a] => some (Nat.xor a (evmModulus - 1))
      | "shl", [shift, value] => some ((value * (2 ^ shift)) % evmModulus)
      | "shr", [shift, value] => some (value / (2 ^ shift))
      | "caller", [] => some state.sender
      | "calldataload", [offset] =>
          -- calldataload retrieves 32-byte word from calldata at given offset.
          -- We model calldata as 32-byte words aligned after the 4-byte selector.
          -- For offsets matching 4 + 32 * i, return args[i]; otherwise return 0.
          if offset < 4 then
            some 0
          else
            let wordOffset := offset - 4
            if wordOffset % 32 != 0 then
              some 0
            else
              let idx := wordOffset / 32
              some (state.calldata.getD idx 0 % evmModulus)
      | _, _ => none  -- Unknown or invalid function call
/-- Evaluate a Yul expression in the IR context -/
partial def evalIRExpr (state : IRState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none  -- Strings not supported in our IR subset
  | .ident name => state.getVar name
  | .call func args => evalIRCall state func args

end -- mutual

/-! ## IR Statement Execution -/

/-- Result of executing IR statements -/
inductive IRExecResult
  | continue (state : IRState)
  | return (value : Nat) (state : IRState)
  | stop (state : IRState)
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
      match slotExpr with
      | .call "mappingSlot" [baseExpr, keyExpr] =>
          match evalIRExpr state baseExpr, evalIRExpr state keyExpr, evalIRExpr state valExpr with
          | some baseSlot, some key, some val =>
              .continue {
                state with
                mappings := fun b k =>
                  if b = baseSlot ∧ k = key then val else state.mappings b k
              }
          | _, _, _ => .revert state
      | _ =>
          match evalIRExpr state slotExpr, evalIRExpr state valExpr with
          | some slot, some val =>
            match decodeMappingSlot slot with
            | some (baseSlot, key) =>
                .continue {
                  state with
                  mappings := fun b k =>
                    if b = baseSlot ∧ k = key then val else state.mappings b k
                }
            | none =>
                .continue { state with storage := fun s => if s = slot then val else state.storage s }
          | _, _ => .revert state
    | .call "mstore" [offsetExpr, valExpr] =>
      match evalIRExpr state offsetExpr, evalIRExpr state valExpr with
      | some offset, some val =>
        .continue { state with memory := fun o => if o = offset then val else state.memory o }
      | _, _ => .revert state
    | .call "stop" [] => .stop state
    | .call "revert" _ => .revert state
    | .call "return" [offsetExpr, sizeExpr] =>
      -- Yul return(offset, size) returns memory[offset:offset+size]
      -- For our IR subset focusing on single values, we interpret this as:
      -- return(0, 32) means return a 32-byte (256-bit) value stored at memory offset 0
      match evalIRExpr state offsetExpr, evalIRExpr state sizeExpr with
      | some offset, some size =>
        -- For return values, we expect size=32 (single 256-bit value)
        -- Return the word stored at the requested offset.
        if size = 32 then
          .return (state.memory offset) state
        else
          .return 0 state
      | _, _ => .revert state
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
  -- Execution sender must come from the transaction (matches SpecInterpreter)
  let initialState := { initialState with sender := tx.sender, calldata := tx.args }

  -- Find matching function by selector
  match contract.functions.find? (·.selector == tx.functionSelector) with
  | some fn => execIRFunction fn tx.args initialState
  | none =>
    { success := false
      returnValue := none
      finalStorage := initialState.storage
      finalMappings := initialState.mappings }

end Compiler.Proofs.IRGeneration
