/-
  Compiler.Proofs.SpecInterpreter: Semantics for ContractSpec DSL

  This module defines what it *means* to execute a ContractSpec.
  It provides a reference implementation that can be proven equivalent to
  both the EDSL semantics (Layer 1) and the IR/Yul semantics (Layers 2-3).

  Philosophy:
  - Simple, direct interpretation of the ContractSpec DSL
  - No optimizations - correctness over performance
  - Easy to understand and verify
-/

import Compiler.ContractSpec
import Compiler.DiffTestTypes
import Compiler.Hex
import DumbContracts.Core
import DumbContracts.Core.Uint256

namespace Compiler.Proofs

open Compiler.ContractSpec
open Compiler.DiffTestTypes
open Compiler.Hex
open DumbContracts
open DumbContracts.Core.Uint256 (modulus)

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
  deriving Repr

/-!
## Storage State

Abstract representation of contract storage.
Simpler than full ContractState - just what we need for specs.
-/

structure SpecStorage where
  -- Simple storage slots (field index → value)
  slots : List (Nat × Nat)
  -- Mapping storage (field index → key → value)
  mappings : List (Nat × List (Nat × Nat))
  deriving Repr

-- Create empty storage
def SpecStorage.empty : SpecStorage :=
  { slots := [], mappings := [] }

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

/-!
## Expression Evaluation

Evaluate ContractSpec expressions to natural numbers.
All arithmetic is modular (mod 2^256) to match EVM semantics.
We use the same modulus as Uint256 to ensure consistency.
-/

-- Evaluate expression
-- Takes parameter names from function spec to correctly resolve Expr.param
def evalExpr (ctx : EvalContext) (storage : SpecStorage) (fields : List Field) (paramNames : List String) : Expr → Nat
  | Expr.literal n => n % modulus
  | Expr.param name =>
      -- Look up parameter by name in function parameter list
      -- Parameters are Nat values that need modular arithmetic like literals
      match paramNames.findIdx? (· == name) with
      | some idx =>
          let raw := ctx.params.getD idx 0
          match ctx.paramTypes.get? idx with
          | some ParamType.address => raw % addressModulus
          | _ => raw % modulus
      | none => 0  -- Unknown param defaults to 0
  | Expr.constructorArg idx =>
      -- Constructor arguments are Nat values that need modular arithmetic
      let raw := ctx.constructorArgs.getD idx 0
      match ctx.constructorParamTypes.get? idx with
      | some ParamType.address => raw % addressModulus
      | _ => raw % modulus
  | Expr.storage fieldName =>
      match fields.findIdx? (·.name == fieldName) with
      | some slot => storage.getSlot slot
      | none => 0  -- Unknown field
  | Expr.mapping fieldName key =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let keyVal := evalExpr ctx storage fields paramNames key
          storage.getMapping baseSlot keyVal
      | none => 0  -- Unknown mapping
  | Expr.caller => addressToNat ctx.sender
  | Expr.msgValue => ctx.msgValue % modulus
  | Expr.blockTimestamp => ctx.blockTimestamp % modulus
  | Expr.localVar name =>
      ctx.localVars.lookup name |>.getD 0
  | Expr.add a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      (va + vb) % modulus
  | Expr.sub a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va >= vb then va - vb
      else modulus - (vb - va)  -- Two's complement wrapping
  | Expr.mul a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      (va * vb) % modulus
  | Expr.div a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if vb == 0 then 0  -- EVM: division by zero returns 0
      else va / vb
  | Expr.mod a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if vb == 0 then 0  -- EVM: mod by zero returns 0
      else va % vb
  | Expr.bitAnd a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      Nat.land va vb
  | Expr.bitOr a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      Nat.lor va vb
  | Expr.bitXor a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      Nat.xor va vb
  | Expr.bitNot a =>
      let va := evalExpr ctx storage fields paramNames a
      (modulus - 1 - va) % modulus  -- Bitwise NOT in 256-bit space
  | Expr.shl shift value =>
      let s := evalExpr ctx storage fields paramNames shift
      let v := evalExpr ctx storage fields paramNames value
      (v <<< s) % modulus
  | Expr.shr shift value =>
      let s := evalExpr ctx storage fields paramNames shift
      let v := evalExpr ctx storage fields paramNames value
      v >>> s
  | Expr.eq a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va == vb then 1 else 0
  | Expr.ge a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va >= vb then 1 else 0
  | Expr.gt a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va > vb then 1 else 0
  | Expr.lt a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va < vb then 1 else 0
  | Expr.le a b =>
      let va := evalExpr ctx storage fields paramNames a
      let vb := evalExpr ctx storage fields paramNames b
      if va <= vb then 1 else 0

/-!
## Statement Execution

Execute ContractSpec statements, updating storage and context.
Returns None if execution reverts.
-/

-- Execution state
structure ExecState where
  storage : SpecStorage
  returnValue : Option Nat
  halted : Bool  -- Track if execution should stop (return/stop encountered)
  deriving Repr

-- Execute a single statement
-- Returns updated context and state (context is updated for letVar to fix local variable bug)
def execStmt (ctx : EvalContext) (fields : List Field) (paramNames : List String) (state : ExecState) (stmt : Stmt) :
    Option (EvalContext × ExecState) :=
  match stmt with
  | Stmt.letVar name expr =>
      let value := evalExpr ctx state.storage fields paramNames expr
      -- BUG FIX: Update ctx.localVars instead of state.localVars
      let newVars := (name, value) :: ctx.localVars.filter (·.1 ≠ name)
      let newCtx := { ctx with localVars := newVars }
      some (newCtx, state)

  | Stmt.setStorage fieldName expr =>
      match fields.findIdx? (·.name == fieldName) with
      | some slot =>
          let value := evalExpr ctx state.storage fields paramNames expr
          let newStorage := state.storage.setSlot slot value
          some (ctx, { state with storage := newStorage })
      | none => none  -- Unknown field, revert

  | Stmt.setMapping fieldName keyExpr valueExpr =>
      match fields.findIdx? (·.name == fieldName) with
      | some baseSlot =>
          let key := evalExpr ctx state.storage fields paramNames keyExpr
          let value := evalExpr ctx state.storage fields paramNames valueExpr
          let newStorage := state.storage.setMapping baseSlot key value
          some (ctx, { state with storage := newStorage })
      | none => none  -- Unknown mapping, revert

  | Stmt.require condExpr _message =>
      let cond := evalExpr ctx state.storage fields paramNames condExpr
      if cond ≠ 0 then some (ctx, state)  -- Non-zero = true, continue
      else none  -- Zero = false, revert

  | Stmt.return expr =>
      let value := evalExpr ctx state.storage fields paramNames expr
      some (ctx, { state with returnValue := some value, halted := true })

  | Stmt.stop =>
      some (ctx, { state with halted := true })

-- Execute a list of statements sequentially
-- Thread both context and state through the computation
-- Stop early if return/stop is encountered (halted = true)
def execStmts (ctx : EvalContext) (fields : List Field) (paramNames : List String) (state : ExecState) (stmts : List Stmt) :
    Option (EvalContext × ExecState) :=
  stmts.foldlM (fun (ctx, state) stmt =>
    if state.halted then some (ctx, state)  -- Already halted, skip remaining statements
    else execStmt ctx fields paramNames state stmt
  ) (ctx, state)

/-!
## Function Execution

Execute a function from a ContractSpec.
-/

def execFunction (spec : ContractSpec) (funcName : String) (ctx : EvalContext)
    (initialStorage : SpecStorage) : Option (EvalContext × ExecState) :=
  -- Find function in spec
  match spec.functions.find? (·.name == funcName) with
  | none => none  -- Function not found, revert
  | some func =>
      -- Execute function body
      let ctx := { ctx with paramTypes := func.params.map (·.ty) }
      let initialState : ExecState := {
        storage := initialStorage
        returnValue := none
        halted := false
      }
      -- BUG FIX: Pass function parameter names to execStmts
      let paramNames := func.params.map (·.name)
      execStmts ctx spec.fields paramNames initialState func.body

-- Execute a constructor
def execConstructor (spec : ContractSpec) (ctx : EvalContext)
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
      -- Constructor parameters are accessed via Expr.constructorArg
      let paramNames := ctor.params.map (·.name)
      execStmts ctx spec.fields paramNames initialState ctor.body

/-!
## Top-Level Interpreter

Execute a ContractSpec with a given transaction.
-/

-- Execution result matching the differential testing format
structure SpecResult where
  success : Bool
  returnValue : Option Nat
  revertReason : Option String
  finalStorage : SpecStorage
  deriving Repr

def interpretSpec (spec : ContractSpec) (initialStorage : SpecStorage) (tx : Transaction) : SpecResult :=
  -- BUG FIX: Handle constructor execution when functionName is empty
  if tx.functionName == "" then
    -- Constructor execution
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := 0
      blockTimestamp := 0
      params := []
      paramTypes := []
      constructorArgs := tx.args  -- Constructor args go here
      constructorParamTypes := []
      localVars := []
    }
    match execConstructor spec ctx initialStorage with
    | none =>
        { success := false
          returnValue := none
          revertReason := some "Constructor reverted"
          finalStorage := initialStorage }
    | some (_finalCtx, finalState) =>
        { success := true
          returnValue := finalState.returnValue
          revertReason := none
          finalStorage := finalState.storage }
  else
    -- Regular function execution
    let ctx : EvalContext := {
      sender := tx.sender
      msgValue := 0  -- Not exposed in current specs
      blockTimestamp := 0  -- Not exposed in current specs
      params := tx.args
      paramTypes := []
      constructorArgs := []  -- Not used for regular functions
      constructorParamTypes := []
      localVars := []
    }
    match execFunction spec tx.functionName ctx initialStorage with
    | none =>
        -- Execution reverted
        { success := false
          returnValue := none
          revertReason := some s!"Function '{tx.functionName}' reverted"
          finalStorage := initialStorage }
    | some (_finalCtx, finalState) =>
        -- Execution succeeded
        { success := true
          returnValue := finalState.returnValue
          revertReason := none
          finalStorage := finalState.storage }

end Compiler.Proofs
