/-
  Layer 2: ContractSpec → IR Preservation for Owned

  Pins down the generated IR for Owned and proves per-function + dispatch
  preservation against the ContractSpec interpreter.
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

/-! ## Concrete IR for Owned -/

def ownedIRContract : IRContract :=
  { name := "Owned"
    deploy := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.lit 32]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit 32]),
      YulStmt.let_ "arg0" (YulExpr.call "and" [
        YulExpr.call "mload" [YulExpr.lit 0],
        YulExpr.hex 1461501637330902918203684832716283019655932542975
      ]),
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "arg0"])
    ]
    functions := [
      { name := "transferOwnership"
        selector := 0xf2fde38b
        params := [{ name := "newOwner", ty := IRType.address }]
        ret := IRType.unit
        body := [
          YulStmt.let_ "newOwner" (YulExpr.call "and" [
            YulExpr.call "calldataload" [YulExpr.lit 4],
            YulExpr.hex 1461501637330902918203684832716283019655932542975
          ]),
          YulStmt.if_ (YulExpr.call "iszero" [
            YulExpr.call "eq" [
              YulExpr.call "caller" [],
              YulExpr.call "sload" [YulExpr.lit 0]
            ]
          ]) [
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.lit 0,
              YulExpr.hex 3963877391197344453575983046348115674221700746820753546331534351508065746944
            ]),
            YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
            YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit 9]),
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.lit 68,
              YulExpr.hex 35477323690718495543680415611189027245839728464698287747313795670985400123392
            ]),
            YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 100])
          ],
          YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.ident "newOwner"]),
          YulStmt.expr (YulExpr.call "stop" [])
        ]
      },
      { name := "getOwner"
        selector := 0x893d20e8
        params := []
        ret := IRType.address
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

@[simp] lemma compile_ownedSpec :
    compile ownedSpec [0xf2fde38b, 0x893d20e8] = .ok ownedIRContract := by
  rfl

@[simp] lemma nat_mask_eq_mod (n : Nat) :
    n &&& (2^160 - 1) = n % (2^160) := by
  simpa using (Nat.and_two_pow_sub_one_eq_mod n 160)

/-! ## Owned: transferOwnership Correctness -/

theorem owned_transferOwnership_correct (ownerNat newOwner : Nat) (sender : Address) :
  let spec := ownedSpec
  let irContract := compile spec [0xf2fde38b, 0x893d20e8]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 ownerNat
  let tx : Transaction := {
    sender := sender
    functionName := "transferOwnership"
    args := [newOwner]
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0xf2fde38b
    args := [newOwner]
  }
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (specStorageToIRState initialStorage sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  by_cases howner : ownerNat = addressToNat sender
  · simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
      ownedIRContract, specStorageToIRState, SpecStorage.empty, howner]
    · intro slot
      by_cases hslot : slot = 0
      · subst hslot
        simp
      · simp [hslot]
  · simp [resultsMatch, interpretSpec, execFunction, execStmts, execStmt, evalExpr,
      interpretIR, execIRFunction, execIRStmts, execIRStmt, evalIRExpr, evalIRExprs,
      ownedIRContract, specStorageToIRState, SpecStorage.empty, howner]
    · intro slot
      by_cases hslot : slot = 0
      · subst hslot
        simp
      · simp [hslot]

/-! ## Owned: getOwner Correctness -/

theorem owned_getOwner_correct (ownerNat : Nat) (sender : Address) :
  let spec := ownedSpec
  let irContract := compile spec [0xf2fde38b, 0x893d20e8]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 ownerNat
  let tx : Transaction := {
    sender := sender
    functionName := "getOwner"
    args := []
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x893d20e8
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
    ownedIRContract, specStorageToIRState, SpecStorage.empty]
  · intro slot
    by_cases hslot : slot = 0
    · subst hslot
      simp
    · simp [hslot]

/-! ## Contract-Level Preservation (Dispatch) -/

theorem owned_contract_preserves_semantics (ownerNat : Nat) (tx : Transaction) :
  let spec := ownedSpec
  let irContract := compile spec [0xf2fde38b, 0x893d20e8]
  let initialStorage : SpecStorage := SpecStorage.empty.setSlot 0 ownerNat
  let specResult := interpretSpec spec initialStorage tx
  match irContract with
  | .ok ir =>
      match tx.functionName, tx.args with
      | "transferOwnership", [newOwner] =>
          let irTx := transactionToIRTransaction tx 0xf2fde38b
          let irResult := interpretIR ir irTx (specStorageToIRState initialStorage tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | "getOwner", [] =>
          let irTx := transactionToIRTransaction tx 0x893d20e8
          let irResult := interpretIR ir irTx (specStorageToIRState initialStorage tx.sender)
          resultsMatch ir.usesMapping [] irResult specResult
      | _, _ => True
  | .error _ => False
  := by
  by_cases htransfer : tx.functionName = "transferOwnership"
  · subst htransfer
    cases hargs : tx.args with
    | nil =>
        simp [hargs]
    | cons newOwner rest =>
        cases rest with
        | nil =>
            simpa [hargs] using (owned_transferOwnership_correct ownerNat newOwner tx.sender)
        | cons _ _ =>
            simp [hargs]
  · by_cases hget : tx.functionName = "getOwner"
    · subst hget
      cases hargs : tx.args with
      | nil =>
          simpa [hargs] using (owned_getOwner_correct ownerNat tx.sender)
      | cons _ _ =>
          simp [hargs]
    · simp [htransfer, hget]

end Compiler.Proofs.IRGeneration
