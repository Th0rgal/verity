import Compiler.Yul.Ast
import Compiler.Constants
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.Yul
open Compiler.Proofs.IRGeneration
export Compiler.Constants (evmModulus selectorModulus selectorShift)

/-!
Shared Yul runtime data structures.

This module intentionally contains only neutral transaction/result/state
plumbing used by both the historical reference oracle and the native
EVMYulLean harness. It does not define or import the legacy fuel interpreter.
-/

structure YulState where
  vars : List (String × Nat)
  storage : IRStorageSlot → IRStorageWord
  transientStorage : Nat → Nat := fun _ => 0
  memory : Nat → Nat
  calldata : List Nat
  selector : Nat
  returnValue : Option Nat
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  events : List (List Nat) := []
  deriving Nonempty

/-- Selector expression used by the runtime switch. -/
def selectorExpr : YulExpr :=
  YulExpr.call "shr" [
    YulExpr.lit selectorShift,
    YulExpr.call "calldataload" [YulExpr.lit 0]
  ]

structure YulTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Convert an IR transaction to a Yul transaction. -/
@[reducible] def YulTransaction.ofIR (tx : IRTransaction) : YulTransaction :=
  { sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    functionSelector := tx.functionSelector
    args := tx.args }

/-! ### Loop-free syntactic predicates

Decidable predicates checking that a Yul AST does not contain `for_` loops.
These are `Bool`-valued so compiler-generated fragments can discharge them
automatically via `rfl`. -/
mutual
def yulStmtLoopFree : YulStmt → Bool
  | .comment _ | .let_ _ _ | .letMany _ _ | .assign _ _ | .expr _ | .leave => true
  | .if_ _ body => yulStmtsLoopFree body
  | .for_ _ _ _ _ => false
  | .switch _ cases defaultCase =>
      yulSwitchCasesLoopFree cases && yulOptionStmtsLoopFree defaultCase
  | .block stmts => yulStmtsLoopFree stmts
  | .funcDef _ _ _ body => yulStmtsLoopFree body

def yulStmtsLoopFree : List YulStmt → Bool
  | [] => true
  | stmt :: stmts => yulStmtLoopFree stmt && yulStmtsLoopFree stmts

def yulSwitchCasesLoopFree : List (Nat × List YulStmt) → Bool
  | [] => true
  | (_, body) :: rest => yulStmtsLoopFree body && yulSwitchCasesLoopFree rest

def yulOptionStmtsLoopFree : Option (List YulStmt) → Bool
  | none => true
  | some body => yulStmtsLoopFree body
end

/-- Preconditions under which generated dispatch guards behave like the
    intended source-level checks for a selected function case. -/
def DispatchGuardsSafe (fn : IRFunction) (tx : IRTransaction) : Prop :=
  (fn.payable = true ∨ tx.msgValue % evmModulus = 0) ∧
  4 + fn.params.length * 32 < evmModulus

@[simp] theorem YulTransaction.ofIR_sender (tx : IRTransaction) :
    (YulTransaction.ofIR tx).sender = tx.sender := rfl

@[simp] theorem YulTransaction.ofIR_args (tx : IRTransaction) :
    (YulTransaction.ofIR tx).args = tx.args := rfl

/-- Initial state for Yul execution. -/
def YulState.initial (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (events : List (List Nat) := []) : YulState :=
  { vars := []
    storage := storage
    transientStorage := fun _ => 0
    memory := fun _ => 0
    calldata := tx.args
    selector := tx.functionSelector
    returnValue := none
    sender := tx.sender
    msgValue := tx.msgValue
    thisAddress := tx.thisAddress
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    events := events }

/-- Lookup variable in state. -/
def YulState.getVar (s : YulState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state. -/
def YulState.setVar (s : YulState) (name : String) (value : Nat) : YulState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

structure YulResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : IRStorageSlot → IRStorageWord
  finalMappings : Nat → Nat → IRStorageWord
  events : List (List Nat)

inductive YulExecResult
  | continue (state : YulState)
  | return (value : Nat) (state : YulState)
  | stop (state : YulState)
  | revert (state : YulState)
  deriving Nonempty

def yulResultOfExecWithRollback (rollback : YulState) : YulExecResult → YulResult
  | .continue s =>
      { success := true
        returnValue := s.returnValue
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .return v s =>
      { success := true
        returnValue := some v
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .stop s =>
      { success := true
        returnValue := none
        finalStorage := s.storage
        finalMappings := Compiler.Proofs.storageAsMappings s.storage
        events := s.events }
  | .revert _ =>
      { success := false
        returnValue := none
        finalStorage := rollback.storage
        finalMappings := Compiler.Proofs.storageAsMappings rollback.storage
        events := rollback.events }

end Compiler.Proofs.YulGeneration
