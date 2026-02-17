/-
  Verity.Proofs.Stdlib.SpecInterpreter: Semantics for ContractSpec DSL

  This module defines what it *means* to execute a ContractSpec.
  It provides a reference implementation that can be proven equivalent to
  both the EDSL semantics (Layer 1) and the IR/Yul semantics (Layers 2-3).

  Philosophy:
  - Simple, direct interpretation of the ContractSpec DSL
  - No optimizations - correctness over performance
  - Easy to understand and verify

  Supports:
  - If/else branching (#179)
  - Double mappings and uint256-keyed mappings (#154)
  - Event emission recording (#153)
  - External function calls via externalFunctions parameter (#172)

  Known limitations (basic execStmts path):
  - forEach loops are no-ops — use execStmtsFuel for contracts with loops (#179)
  - Expr.internalCall always returns 0 — internal function lookup not yet implemented (#181)
  - Stmt.internalCall is a no-op — side effects of internal functions not modeled (#181)
  - arrayParams is never populated from Transaction — array element access returns 0 (#180)
  These limitations affect only the interpreter, not the compiled Yul output.
-/

import Compiler.ContractSpec
import Compiler.DiffTestTypes
import Compiler.Hex
import Verity.Core
import Verity.Core.Uint256

namespace Verity.Proofs.Stdlib.SpecInterpreter

open Compiler.ContractSpec
open Compiler.DiffTestTypes
open Compiler.Hex
open Verity
open Verity.Core.Uint256 (modulus)

def addressModulus : Nat := 2^160

/-!
## Evaluation Context

Context needed to evaluate ContractSpec expressions and statements.
-/

structure EvalContext where
  -- Execution environment
  sender : Address
  msgValue : Nat
  blockTimestamp : Nat
  -- Function parameters (by index)
  params : List Nat
  paramTypes : List ParamType
  -- Constructor parameters (by index, if in constructor)
  constructorArgs : List Nat
  constructorParamTypes : List ParamType
  -- Local variables (from letVar)
  localVars : List (String × Nat)
  -- Array parameters: name → (length, elements) (#180)
  arrayParams : List (String × (Nat × List Nat))
  deriving Repr

/-!
## Storage State

Abstract representation of contract storage.
Extended with double-mapping support (#154) and events (#153).
-/

structure SpecStorage where
  -- Simple storage slots (field index → value)
  slots : List (Nat × Nat)
  -- Mapping storage (field index → key → value)
  mappings : List (Nat × List (Nat × Nat))
  -- Double mapping storage (field index → (key1, key2) → value) (#154)
  mappings2 : List (Nat × List ((Nat × Nat) × Nat))
  -- Emitted events (#153)
  events : List (String × List Nat)
  deriving Repr

-- Create empty storage
def SpecStorage.empty : SpecStorage :=
  { slots := [], mappings := [], mappings2 := [], events := [] }

-- Read from simple storage slot
def SpecStorage.getSlot (s : SpecStorage) (slot : Nat) : Nat :=
  s.slots.lookup slot |>.getD 0

-- Write to simple storage slot
def SpecStorage.setSlot (s : SpecStorage) (slot : Nat) (value : Nat) : SpecStorage :=
  { s with slots := (slot, value) :: s.slots.filter (·.1 ≠ slot) }

-- Read from mapping
def SpecStorage.getMapping (s : SpecStorage) (baseSlot : Nat) (key : Nat) : Nat :=
  match s.mappings.lookup baseSlot with
  | none => 0
  | some m => m.lookup key |>.getD 0

-- Write to mapping
def SpecStorage.setMapping (s : SpecStorage) (baseSlot : Nat) (key : Nat) (value : Nat) : SpecStorage :=
  let oldMapping := s.mappings.lookup baseSlot |>.getD []
  let newMapping := (key, value) :: oldMapping.filter (·.1 ≠ key)
  let filteredMappings := s.mappings.filter (·.1 ≠ baseSlot)
  { s with mappings := (baseSlot, newMapping) :: filteredMappings }

-- Read from double mapping (#154)
def SpecStorage.getMapping2 (s : SpecStorage) (baseSlot : Nat) (key1 key2 : Nat) : Nat :=
  match s.mappings2.lookup baseSlot with
  | none => 0
  | some m =>
    match m.find? (fun ((k1, k2), _) => k1 == key1 && k2 == key2) with
    | none => 0
    | some (_, v) => v

-- Write to double mapping (#154)
def SpecStorage.setMapping2 (s : SpecStorage) (baseSlot : Nat) (key1 key2 : Nat) (value : Nat) : SpecStorage :=
  let oldMapping := s.mappings2.lookup baseSlot |>.getD []
  let newMapping := ((key1, key2), value) :: oldMapping.filter (fun ((k1, k2), _) => !(k1 == key1 && k2 == key2))
  let filteredMappings := s.mappings2.filter (·.1 ≠ baseSlot)
  { s with mappings2 := (baseSlot, newMapping) :: filteredMappings }

-- Add event to log (#153)
def SpecStorage.addEvent (s : SpecStorage) (name : String) (args : List Nat) : SpecStorage :=
  { s with events := s.events ++ [(name, args)] }

/-!
## Expression Evaluation

Evaluate ContractSpec expressions to natural numbers.
All arithmetic is modular (mod 2^256) to match EVM semantics.
-/

mutual
def evalExprs (ctx : EvalContext) (storage : SpecStorage) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) : List Expr → List Nat
  | [] => []
  | e :: es => evalExpr ctx storage fields paramNames externalFns e :: evalExprs ctx storage fields paramNames externalFns es

def evalExpr (ctx : EvalContext) (storage : SpecStorage) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) : Expr → Nat
  | Expr.literal n => n % modulus
  | Expr.param name =>
      match paramNames.findIdx? (· == name) with
      | some idx =>
          let raw := ctx.params.getD idx 0
          match ctx.paramTypes.get? idx with
          | some ParamType.address => raw % addressModulus
          | _ => raw % modulus
      | none => 0
  | Expr.constructorArg idx =>
      let raw := ctx.constructorArgs.getD idx 0
      match ctx.constructorParamTypes.get? idx with
      | some ParamType.address => raw % addressModulus
      | _ => raw % modulus
  | Expr.storage fieldName =>
      match fields.findIdx? (·.name == fieldName) with
      | some slot => storage.getSlot slot
      | none => 0
  | Expr.mapping fieldName key =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let keyVal := evalExpr ctx storage fields paramNames externalFns key
          storage.getMapping baseSlot keyVal
      | none => 0
  | Expr.mapping2 fieldName key1 key2 =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let key1Val := evalExpr ctx storage fields paramNames externalFns key1
          let key2Val := evalExpr ctx storage fields paramNames externalFns key2
          storage.getMapping2 baseSlot key1Val key2Val
      | none => 0
  | Expr.mappingUint fieldName key =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let keyVal := evalExpr ctx storage fields paramNames externalFns key
          storage.getMapping baseSlot keyVal
      | none => 0
  | Expr.caller => addressToNat ctx.sender
  | Expr.msgValue => ctx.msgValue % modulus
  | Expr.blockTimestamp => ctx.blockTimestamp % modulus
  | Expr.localVar name =>
      ctx.localVars.lookup name |>.getD 0
  | Expr.externalCall name args =>
      let argVals := evalExprs ctx storage fields paramNames externalFns args
      match externalFns.lookup name with
      | some fn => fn argVals % modulus
      | none => 0
  | Expr.internalCall _functionName _args => 0
  | Expr.arrayLength name =>
      match ctx.arrayParams.lookup name with
      | some (len, _) => len
      | none => 0
  | Expr.arrayElement name index =>
      let idx := evalExpr ctx storage fields paramNames externalFns index
      match ctx.arrayParams.lookup name with
      | some (_, elems) => elems.getD idx 0
      | none => 0
  | Expr.add a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      (va + vb) % modulus
  | Expr.sub a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if va >= vb then va - vb
      else modulus - (vb - va)
  | Expr.mul a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      (va * vb) % modulus
  | Expr.div a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if vb == 0 then 0 else va / vb
  | Expr.mod a b =>
      let va := evalExpr ctx storage fields paramNames externalFns a
      let vb := evalExpr ctx storage fields paramNames externalFns b
      if vb == 0 then 0 else va % vb
  | Expr.bitAnd a b =>
      Nat.land (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitOr a b =>
      Nat.lor (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitXor a b =>
      Nat.xor (evalExpr ctx storage fields paramNames externalFns a) (evalExpr ctx storage fields paramNames externalFns b)
  | Expr.bitNot a =>
      (modulus - 1 - evalExpr ctx storage fields paramNames externalFns a) % modulus
  | Expr.shl shift value =>
      (evalExpr ctx storage fields paramNames externalFns value <<< evalExpr ctx storage fields paramNames externalFns shift) % modulus
  | Expr.shr shift value =>
      evalExpr ctx storage fields paramNames externalFns value >>> evalExpr ctx storage fields paramNames externalFns shift
  | Expr.eq a b =>
      if evalExpr ctx storage fields paramNames externalFns a == evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.ge a b =>
      if evalExpr ctx storage fields paramNames externalFns a >= evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.gt a b =>
      if evalExpr ctx storage fields paramNames externalFns a > evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.lt a b =>
      if evalExpr ctx storage fields paramNames externalFns a < evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.le a b =>
      if evalExpr ctx storage fields paramNames externalFns a <= evalExpr ctx storage fields paramNames externalFns b then 1 else 0
  | Expr.logicalAnd a b =>
      if evalExpr ctx storage fields paramNames externalFns a ≠ 0 && evalExpr ctx storage fields paramNames externalFns b ≠ 0 then 1 else 0
  | Expr.logicalOr a b =>
      if evalExpr ctx storage fields paramNames externalFns a ≠ 0 || evalExpr ctx storage fields paramNames externalFns b ≠ 0 then 1 else 0
  | Expr.logicalNot a =>
      if evalExpr ctx storage fields paramNames externalFns a == 0 then 1 else 0
end

/-!
## Statement Execution

Execute ContractSpec statements, updating storage and context.
Returns None if execution reverts.

The basic `execStmt` / `execStmts` handle all constructs that don't introduce
unbounded recursion (everything except forEach). They are kept simple for
proof automation. For forEach, we provide `execStmtsFuel` with explicit fuel.
-/

-- Execution state
structure ExecState where
  storage : SpecStorage
  returnValue : Option Nat
  halted : Bool
  deriving Repr

-- Execute a single statement
-- Returns updated context and state
-- Note: execStmt and execStmts are mutually recursive because ite branches
-- need to execute a list of statements.
mutual
def execStmt (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) (state : ExecState) (stmt : Stmt) :
    Option (EvalContext × ExecState) :=
  match stmt with
  | Stmt.letVar name expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      let newVars := (name, value) :: ctx.localVars.filter (·.1 ≠ name)
      some ({ ctx with localVars := newVars }, state)

  | Stmt.assignVar name expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      let newVars := (name, value) :: ctx.localVars.filter (·.1 ≠ name)
      some ({ ctx with localVars := newVars }, state)

  | Stmt.setStorage fieldName expr =>
      match fields.findIdx? (·.name == fieldName) with
      | some slot =>
          let value := evalExpr ctx state.storage fields paramNames externalFns expr
          some (ctx, { state with storage := state.storage.setSlot slot value })
      | none => none

  | Stmt.setMapping fieldName keyExpr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let key := evalExpr ctx state.storage fields paramNames externalFns keyExpr
          let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
          some (ctx, { state with storage := state.storage.setMapping baseSlot key value })
      | none => none

  | Stmt.setMapping2 fieldName key1Expr key2Expr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let key1 := evalExpr ctx state.storage fields paramNames externalFns key1Expr
          let key2 := evalExpr ctx state.storage fields paramNames externalFns key2Expr
          let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
          some (ctx, { state with storage := state.storage.setMapping2 baseSlot key1 key2 value })
      | none => none

  | Stmt.setMappingUint fieldName keyExpr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let key := evalExpr ctx state.storage fields paramNames externalFns keyExpr
          let value := evalExpr ctx state.storage fields paramNames externalFns valueExpr
          some (ctx, { state with storage := state.storage.setMapping baseSlot key value })
      | none => none

  | Stmt.require condExpr _message =>
      let cond := evalExpr ctx state.storage fields paramNames externalFns condExpr
      if cond ≠ 0 then some (ctx, state) else none

  | Stmt.return expr =>
      let value := evalExpr ctx state.storage fields paramNames externalFns expr
      some (ctx, { state with returnValue := some value, halted := true })

  | Stmt.stop =>
      some (ctx, { state with halted := true })

  | Stmt.ite cond thenBranch elseBranch =>
      let condVal := evalExpr ctx state.storage fields paramNames externalFns cond
      if condVal ≠ 0 then
        execStmts ctx fields paramNames externalFns state thenBranch
      else
        execStmts ctx fields paramNames externalFns state elseBranch

  | Stmt.forEach _varName _count _body =>
      -- forEach requires fuel-based execution; use execStmtsFuel for contracts with loops
      -- For the basic interpreter, forEach is a no-op (returns unchanged state)
      some (ctx, state)

  | Stmt.emit eventName args =>
      let argVals := args.map (evalExpr ctx state.storage fields paramNames externalFns ·)
      some (ctx, { state with storage := state.storage.addEvent eventName argVals })

  | Stmt.internalCall _functionName _args =>
      -- Placeholder: internal calls are no-ops in the basic interpreter
      some (ctx, state)

-- Execute a list of statements sequentially
-- Thread both context and state through the computation
-- Stop early if return/stop is encountered (halted = true)
def execStmts (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat))) (state : ExecState) (stmts : List Stmt) :
    Option (EvalContext × ExecState) :=
  match stmts with
  | [] => some (ctx, state)
  | stmt :: rest =>
    if state.halted then some (ctx, state)
    else match execStmt ctx fields paramNames externalFns state stmt with
      | none => none
      | some (ctx', state') => execStmts ctx' fields paramNames externalFns state' rest
end

/-!
### Fuel-based execution for contracts with loops

For contracts that use `forEach`, we provide a fuel-based interpreter
that properly handles bounded loops. The fuel decreases at each recursive step.
-/

-- Helper: Expand a forEach into N copies of the loop body with let bindings
private def expandForEach (varName : String) (count : Nat) (body : List Stmt) : List Stmt :=
  let bound := min count 10000
  let rec go (i : Nat) (acc : List Stmt) : List Stmt :=
    if _h : i >= bound then acc
    else go (i + 1) (acc ++ [Stmt.letVar varName (Expr.literal i)] ++ body)
  termination_by bound - i
  go 0 []

def execStmtsFuel (fuel : Nat) (ctx : EvalContext) (fields : List Field) (paramNames : List String) (externalFns : List (String × (List Nat → Nat)))
    (state : ExecState) (stmts : List Stmt) : Option (EvalContext × ExecState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match stmts with
    | [] => some (ctx, state)
    | stmt :: rest =>
      if state.halted then some (ctx, state)
      else
        let result := match stmt with
          | Stmt.forEach varName count body =>
              -- Desugar forEach into expanded statements
              let countVal := evalExpr ctx state.storage fields paramNames externalFns count
              let expanded := expandForEach varName countVal body
              execStmtsFuel fuel' ctx fields paramNames externalFns state expanded
          | Stmt.ite cond thenBranch elseBranch =>
              let condVal := evalExpr ctx state.storage fields paramNames externalFns cond
              if condVal ≠ 0 then
                execStmtsFuel fuel' ctx fields paramNames externalFns state thenBranch
              else
                execStmtsFuel fuel' ctx fields paramNames externalFns state elseBranch
          | other => execStmt ctx fields paramNames externalFns state other
        match result with
        | none => none
        | some (ctx', state') => execStmtsFuel fuel' ctx' fields paramNames externalFns state' rest
termination_by fuel

/-!
## Function Execution

Execute a function from a ContractSpec.
-/

def execFunction (spec : ContractSpec) (funcName : String) (ctx : EvalContext) (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) : Option (EvalContext × ExecState) :=
  match spec.functions.find? (·.name == funcName) with
  | none => none
  | some func =>
      let ctx := { ctx with paramTypes := func.params.map (·.ty) }
      let initialState : ExecState := {
        storage := initialStorage
        returnValue := none
        halted := false
      }
      let paramNames := func.params.map (·.name)
      execStmts ctx spec.fields paramNames externalFns initialState func.body

def execConstructor (spec : ContractSpec) (ctx : EvalContext) (externalFns : List (String × (List Nat → Nat)))
    (initialStorage : SpecStorage) : Option (EvalContext × ExecState) :=
  match spec.constructor with
  | none => some (ctx, { storage := initialStorage, returnValue := none, halted := false })
  | some ctor =>
      let ctx := { ctx with constructorParamTypes := ctor.params.map (·.ty) }
      let initialState : ExecState := {
        storage := initialStorage
        returnValue := none
        halted := false
      }
      let paramNames := ctor.params.map (·.name)
      execStmts ctx spec.fields paramNames externalFns initialState ctor.body

/-!
## Top-Level Interpreter
-/

structure SpecResult where
  success : Bool
  returnValue : Option Nat
  revertReason : Option String
  finalStorage : SpecStorage
  deriving Repr

def interpretSpec (spec : ContractSpec) (initialStorage : SpecStorage) (tx : Transaction)
    (externalFns : List (String × (List Nat → Nat)) := []) : SpecResult :=
  if tx.functionName == "" then
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := tx.msgValue
      blockTimestamp := tx.blockTimestamp
      params := []
      paramTypes := []
      constructorArgs := tx.args
      constructorParamTypes := []
      localVars := []
      arrayParams := []
    }
    match execConstructor spec ctx externalFns initialStorage with
    | none =>
        { success := false, returnValue := none,
          revertReason := some "Constructor reverted", finalStorage := initialStorage }
    | some (_, finalState) =>
        { success := true, returnValue := finalState.returnValue,
          revertReason := none, finalStorage := finalState.storage }
  else
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := tx.msgValue
      blockTimestamp := tx.blockTimestamp
      params := tx.args
      paramTypes := []
      constructorArgs := []
      constructorParamTypes := []
      localVars := []
      arrayParams := []
    }
    match execFunction spec tx.functionName ctx externalFns initialStorage with
    | none =>
        { success := false, returnValue := none,
          revertReason := some s!"Function '{tx.functionName}' reverted",
          finalStorage := initialStorage }
    | some (_, finalState) =>
        { success := true, returnValue := finalState.returnValue,
          revertReason := none, finalStorage := finalState.storage }

end Verity.Proofs.Stdlib.SpecInterpreter
