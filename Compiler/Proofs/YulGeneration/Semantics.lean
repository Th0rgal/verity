import Compiler.Yul.Ast
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-! ## Yul Runtime Semantics (Layer 3 Foundation)

This module defines execution semantics for a Yul runtime program. It mirrors
IRInterpreter but models selector-aware calldata so `emitYul`'s runtime switch
behaves correctly.
-/

def evmModulus : Nat := 2 ^ 256

def selectorModulus : Nat := 2 ^ 32

def selectorShift : Nat := 224

def selectorWord (selector : Nat) : Nat :=
  (selector % selectorModulus) * (2 ^ selectorShift)

/-- Selector expression used by the runtime switch. -/
def selectorExpr : YulExpr :=
  YulExpr.call "shr" [
    YulExpr.lit selectorShift,
    YulExpr.call "calldataload" [YulExpr.lit 0]
  ]

/-!
Mapping slots in Yul are derived via keccak(baseSlot, key). For proofs, we model
them with a tagged encoding so `sload`/`sstore` can route to `mappings` rather
than flat `storage`. The tag is `2^256`, which is outside the EVM word range,
so it cannot collide with real storage slots produced by arithmetic.
-/

def mappingTag : Nat := evmModulus

def encodeMappingSlot (baseSlot key : Nat) : Nat :=
  mappingTag + (baseSlot % evmModulus) * evmModulus + (key % evmModulus)

def decodeMappingSlot (slot : Nat) : Option (Nat × Nat) :=
  if slot < mappingTag then
    none
  else
    let raw := slot - mappingTag
    some (raw / evmModulus, raw % evmModulus)

/-! ## Execution State -/

structure YulState where
  vars : List (String × Nat)
  storage : Nat → Nat
  mappings : Nat → Nat → Nat
  memory : Nat → Nat
  calldata : List Nat
  selector : Nat
  returnValue : Option Nat
  sender : Nat
  deriving Nonempty

structure YulTransaction where
  sender : Nat
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Initial state for Yul execution -/
def YulState.initial (tx : YulTransaction) (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : YulState :=
  { vars := []
    storage := storage
    mappings := mappings
    memory := fun _ => 0
    calldata := tx.args
    selector := tx.functionSelector
    returnValue := none
    sender := tx.sender }

/-- Lookup variable in state -/
def YulState.getVar (s : YulState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state -/
def YulState.setVar (s : YulState) (name : String) (value : Nat) : YulState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-! ## Yul Expression Evaluation -/

/-! Size measures for termination proofs. -/
mutual
def exprSize : YulExpr → Nat
  | .call _ args => exprsSize args + 2
  | _ => 1

def exprsSize : List YulExpr → Nat
  | [] => 0
  | e :: es => exprSize e + exprsSize es + 1
end

mutual

/-- Evaluate a list of Yul expressions -/
def evalYulExprs (state : YulState) : List YulExpr → Option (List Nat)
  | [] => some []
  | e :: es => do
    let v ← evalYulExpr state e
    let vs ← evalYulExprs state es
    pure (v :: vs)
termination_by es => exprsSize es
decreasing_by
  all_goals
    simp [exprsSize, exprSize]
    omega

def evalYulCall (state : YulState) (func : String) : List YulExpr → Option Nat
  | args => do
    let argVals ← evalYulExprs state args
    match func, argVals with
    | "mappingSlot", [base, key] => some (encodeMappingSlot base key)
    | "sload", [slot] =>
        match decodeMappingSlot slot with
        | some (baseSlot, key) => some (state.mappings baseSlot key)
        | none => some (state.storage slot)
    | "add", [a, b] => some ((a + b) % evmModulus)
    | "sub", [a, b] => some ((evmModulus + a - b) % evmModulus)
    | "mul", [a, b] => some ((a * b) % evmModulus)
    | "div", [a, b] => if b = 0 then some 0 else some (a / b)
    | "mod", [a, b] => if b = 0 then some 0 else some (a % b)
    | "lt", [a, b] => some (if a < b then 1 else 0)
    | "gt", [a, b] => some (if a > b then 1 else 0)
    | "eq", [a, b] => some (if a = b then 1 else 0)
    | "iszero", [a] => some (if a = 0 then 1 else 0)
    | "and", [a, b] => some (a &&& b)
    | "or", [a, b] => some (a ||| b)
    | "xor", [a, b] => some (Nat.xor a b)
    | "not", [a] => some (Nat.xor a (evmModulus - 1))
    | "shl", [shift, value] => some ((value * (2 ^ shift)) % evmModulus)
    | "shr", [shift, value] => some (value / (2 ^ shift))
    | "caller", [] => some state.sender
    | "calldataload", [offset] =>
        if offset = 0 then
          some (selectorWord state.selector)
        else if offset < 4 then
          some 0
        else
          let wordOffset := offset - 4
          if wordOffset % 32 != 0 then
            some 0
          else
            let idx := wordOffset / 32
            some (state.calldata.getD idx 0 % evmModulus)
    | _, _ => none
termination_by args => exprsSize args + 1
decreasing_by
  simp [exprsSize, exprSize]

/-- Evaluate a Yul expression -/
def evalYulExpr (state : YulState) : YulExpr → Option Nat
  | .lit n => some n
  | .hex n => some n
  | .str _ => none
  | .ident name => state.getVar name
  | .call func args => evalYulCall state func args
termination_by e => exprSize e
decreasing_by
  simp [exprsSize, exprSize]

end

/-! ## Yul Statement Execution -/

inductive YulExecResult
  | continue (state : YulState)
  | return (value : Nat) (state : YulState)
  | stop (state : YulState)
  | revert (state : YulState)
  deriving Nonempty

mutual

def execYulStmtFuel : Nat → YulState → YulStmt → YulExecResult
  | fuel, state, stmt =>
      match fuel with
      | 0 => .revert state
      | fuel + 1 =>
        match stmt with
          | .comment _ => .continue state
          | .let_ name value =>
              match evalYulExpr state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .assign name value =>
              match evalYulExpr state value with
              | some v => .continue (state.setVar name v)
              | none => .revert state
          | .expr e =>
              match e with
              | .call "sstore" [slotExpr, valExpr] =>
                  match slotExpr with
                  | .call "mappingSlot" [baseExpr, keyExpr] =>
                      match evalYulExpr state baseExpr, evalYulExpr state keyExpr, evalYulExpr state valExpr with
                      | some baseSlot, some key, some val =>
                          .continue {
                            state with
                            mappings := fun b k =>
                              if b = baseSlot ∧ k = key then val else state.mappings b k
                          }
                      | _, _, _ => .revert state
                  | _ =>
                      match evalYulExpr state slotExpr, evalYulExpr state valExpr with
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
                  match evalYulExpr state offsetExpr, evalYulExpr state valExpr with
                  | some offset, some val =>
                      .continue { state with memory := fun o => if o = offset then val else state.memory o }
                  | _, _ => .revert state
              | .call "stop" [] => .stop state
              | .call "return" [offsetExpr, sizeExpr] =>
                  match evalYulExpr state offsetExpr, evalYulExpr state sizeExpr with
                  | some offset, some size =>
                      if size = 32 then
                        .return (state.memory offset) state
                      else
                        .return 0 state
                  | _, _ => .revert state
              | .call "revert" [_, _] => .revert state
              | _ =>
                  match evalYulExpr state e with
                  | some _ => .continue state
                  | none => .revert state
          | .if_ cond body =>
              match evalYulExpr state cond with
              | some v =>
                  if v = 0 then
                    .continue state
                  else
                    execYulStmtsFuel fuel state body
              | none => .revert state
          | .switch expr cases default =>
              match evalYulExpr state expr with
              | some v =>
                  match cases.find? (fun (c, _) => c = v) with
                  | some (_, body) => execYulStmtsFuel fuel state body
                  | none =>
                      match default with
                      | some body => execYulStmtsFuel fuel state body
                      | none => .continue state
              | none => .revert state
          | .block stmts => execYulStmtsFuel fuel state stmts
          | .funcDef _ _ _ _ => .continue state
termination_by fuel => fuel

def execYulStmtsFuel : Nat → YulState → List YulStmt → YulExecResult
  | fuel, state, stmts =>
      match stmts with
      | [] => .continue state
      | stmt :: rest =>
          match fuel with
          | 0 => .revert state
          | fuel + 1 =>
              match execYulStmtFuel fuel state stmt with
              | .continue s' => execYulStmtsFuel fuel s' rest
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s
termination_by fuel => fuel

end

noncomputable def execYulStmt (state : YulState) (stmt : YulStmt) : YulExecResult :=
  execYulStmtFuel (sizeOf stmt + 1) state stmt

noncomputable def execYulStmts (state : YulState) (stmts : List YulStmt) : YulExecResult :=
  execYulStmtsFuel (sizeOf stmts + 1) state stmts

structure YulResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  finalMappings : Nat → Nat → Nat

/-- Execute a Yul runtime program with selector-aware calldata -/
noncomputable def interpretYulRuntime (runtimeCode : List YulStmt) (tx : YulTransaction)
    (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : YulResult :=
  let initialState := YulState.initial tx storage mappings
  match execYulStmts initialState runtimeCode with
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
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := mappings }

/-- Interpret a Yul object by executing its runtime code. -/
noncomputable def interpretYulObject (obj : YulObject) (tx : YulTransaction)
    (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : YulResult :=
  interpretYulRuntime obj.runtimeCode tx storage mappings

end Compiler.Proofs.YulGeneration
