/-
  Layer 2: ContractSpec → IR Preservation for Counter

  Extends the SimpleStorage proof strategy to Counter by pinning down the
  generated IR and proving end-to-end preservation for each function.
-/

import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Proofs.IRGeneration.Expr
import DumbContracts.Proofs.Stdlib.SpecInterpreter
import Compiler.Specs
import Compiler.ContractSpec

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.Specs
open Compiler.ContractSpec
open Compiler.Yul
open DiffTestTypes
open DumbContracts.Proofs.Stdlib.SpecInterpreter

/-! ## Concrete IR for Counter -/

def counterIRContract : IRContract :=
  { name := "Counter"
    deploy := []
    functions := [
      { name := "increment"
        selector := 0xd09de08a
        params := []
        ret := IRType.unit
        body := [
          YulStmt.expr (YulExpr.call "sstore" [
            YulExpr.lit 0,
            YulExpr.call "add" [
              YulExpr.call "sload" [YulExpr.lit 0],
              YulExpr.lit 1
            ]
          ]),
          YulStmt.expr (YulExpr.call "stop" [])
        ]
      },
      { name := "decrement"
        selector := 0x2baeceb7
        params := []
        ret := IRType.unit
        body := [
          YulStmt.expr (YulExpr.call "sstore" [
            YulExpr.lit 0,
            YulExpr.call "sub" [
              YulExpr.call "sload" [YulExpr.lit 0],
              YulExpr.lit 1
            ]
          ]),
          YulStmt.expr (YulExpr.call "stop" [])
        ]
      },
      { name := "getCount"
        selector := 0xa87d942c
        params := []
        ret := IRType.uint256
        body := [
          YulStmt.expr (YulExpr.call "mstore" [
            YulExpr.lit 0,
            YulExpr.call "sload" [YulExpr.lit 0]
          ]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
      }
    ]
    usesMapping := false }

@[simp] lemma compile_counterSpec :
    compile counterSpec [0xd09de08a, 0x2baeceb7, 0xa87d942c] = .ok counterIRContract := by
  rfl

/-! ## Counter: Increment Correctness -/

theorem counter_increment_correct (storedValue : Nat) (sender : Address) :
  let spec := counterSpec
  let irContract := compile spec [0xd09de08a, 0x2baeceb7, 0xa87d942c]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 storedValue
  let tx : Transaction := {
    sender := sender
    functionName := "increment"
    args := []
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0xd09de08a
    args := []
  }
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState initialStorage sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
    interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
    counterIRContract, specStorageToIRState]
  · intro slot
    by_cases h : slot = 0
    · subst h
      simp
    · simp [h]

/-! ## Counter: Decrement Correctness -/

theorem counter_decrement_correct (storedValue : Nat) (sender : Address) :
  let spec := counterSpec
  let irContract := compile spec [0xd09de08a, 0x2baeceb7, 0xa87d942c]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 storedValue
  let tx : Transaction := {
    sender := sender
    functionName := "decrement"
    args := []
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x2baeceb7
    args := []
  }
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState initialStorage sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  by_cases h : storedValue >= 1
  · simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
      counterIRContract, specStorageToIRState, h]
    · intro slot
      by_cases hslot : slot = 0
      · subst hslot
        simp
      · simp [hslot]
  · have hlt : storedValue < 1 := Nat.lt_of_not_ge h
    simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
      counterIRContract, specStorageToIRState, h, hlt, Nat.not_le.mpr hlt]
    · intro slot
      by_cases hslot : slot = 0
      · subst hslot
        simp
      · simp [hslot]

/-! ## Counter: getCount Correctness -/

theorem counter_getCount_correct (storedValue : Nat) (sender : Address) :
  let spec := counterSpec
  let irContract := compile spec [0xd09de08a, 0x2baeceb7, 0xa87d942c]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 storedValue
  let tx : Transaction := {
    sender := sender
    functionName := "getCount"
    args := []
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0xa87d942c
    args := []
  }
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState initialStorage sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
    interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
    counterIRContract, specStorageToIRState]
  · intro slot
    by_cases hslot : slot = 0
    · subst hslot
      simp
    · simp [hslot]

/-! ## Contract-Level Preservation (Dispatch)

This theorem lifts the per-function proofs into a single dispatch lemma
that matches on function name and arity. Incorrect arities are treated
as out-of-scope for now (vacuously true).
-/

theorem counter_contract_preserves_semantics (storedValue : Nat) (tx : Transaction) :
  let spec := counterSpec
  let irContract := compile spec [0xd09de08a, 0x2baeceb7, 0xa87d942c]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 storedValue
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      match tx.functionName, tx.args with
      | "increment", [] =>
          let irTx := transactionToIRTransaction tx 0xd09de08a
          let irResult := interpretIR ir irTx (specStorageToIRState initialStorage tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | "decrement", [] =>
          let irTx := transactionToIRTransaction tx 0x2baeceb7
          let irResult := interpretIR ir irTx (specStorageToIRState initialStorage tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | "getCount", [] =>
          let irTx := transactionToIRTransaction tx 0xa87d942c
          let irResult := interpretIR ir irTx (specStorageToIRState initialStorage tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | _, _ => True
  | .error _ => False
  := by
  by_cases hinc : tx.functionName = "increment"
  · subst hinc
    cases hargs : tx.args with
    | nil =>
        simpa [hargs] using (counter_increment_correct storedValue tx.sender)
    | cons _ _ =>
        simp [hargs]
  · by_cases hdec : tx.functionName = "decrement"
    · subst hdec
      cases hargs : tx.args with
      | nil =>
          simpa [hargs] using (counter_decrement_correct storedValue tx.sender)
      | cons _ _ =>
          simp [hargs]
    · by_cases hget : tx.functionName = "getCount"
      · subst hget
        cases hargs : tx.args with
        | nil =>
            simpa [hargs] using (counter_getCount_correct storedValue tx.sender)
        | cons _ _ =>
            simp [hargs]
      · simp [hinc, hdec, hget]

end Compiler.Proofs.IRGeneration
