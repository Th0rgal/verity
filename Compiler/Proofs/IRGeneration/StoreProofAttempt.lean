/-
  Focused attempt to prove simpleStorage_store_correct

  This file explores the proof in detail to understand what needs to be shown.
-/

import Compiler.Proofs.IRGeneration.Expr
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.Conversions
import Compiler.Proofs.SpecInterpreter
import Compiler.ContractSpec
import Compiler.Specs
import DumbContracts.Core

namespace Compiler.Proofs.IRGeneration.StoreProof

open Compiler
open Compiler.Specs
open Compiler.ContractSpec
open DumbContracts
open DiffTestTypes

/-! ## Step 1: What does compile produce? -/

#eval compile simpleStorageSpec [0x6057361d, 0x2e64cec1]

/-! The output shows:
  - Contract name: "SimpleStorage"
  - store function (selector 0x6057361d):
      let value := calldataload(4)
      sstore(0, value)
      stop()
  - retrieve function (selector 0x2e64cec1):
      mstore(0, sload(0))
      return(0, 32)
-/

/-! ## Step 2: What does interpretSpec produce? -/

def testSpecExecution (value : Nat) : SpecResult :=
  let spec := simpleStorageSpec
  let tx : Transaction := {
    sender := "test_sender"
    functionName := "store"
    args := [value]
  }
  interpretSpec spec SpecStorage.empty tx

#eval testSpecExecution 42

/-! Expected output:
  { success := true,
    returnValue := none,
    revertReason := none,
    finalStorage := <storage with slot 0 = 42> }
-/

/-! ## Step 3: What does interpretIR produce? -/

-- First, we need the compiled IR
def compiledIR : Except String IRContract :=
  compile simpleStorageSpec [0x6057361d, 0x2e64cec1]

-- Extract the IR (we know compile succeeds from #eval above)
def getIR : IRContract :=
  match compiledIR with
  | .ok ir => ir
  | .error _ => { name := "Error", deploy := [], functions := [], usesMapping := false }

def testIRExecution (value : Nat) : IRResult :=
  let ir := getIR
  let irTx : IRTransaction := {
    sender := addressToNat "test_sender"
    functionSelector := 0x6057361d
    args := [value]
  }
  interpretIR ir irTx (IRState.initial irTx.sender)

-- Can't #eval because IRResult contains functions
-- But we can prove properties about it

/-! Expected: IR execution should produce:
  { success := true,
    returnValue := none,
    finalStorage := <function where slot 0 = value, others = 0> }
-/

/-! ## Step 4: Attempt the proof -/

-- Try a specific instance first to see if the proof is tractable
theorem store_correct_42 (initialState : ContractState) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let sender := "test_sender"
  let tx : Transaction := {
    sender := sender
    functionName := "store"
    args := [42]
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x6057361d
    args := [42]
  }
  let specResult := interpretSpec spec SpecStorage.empty tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (IRState.initial irTx.sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  simpa using (Compiler.Proofs.IRGeneration.simpleStorage_store_correct 42 initialState)

theorem store_correct_attempt (value : Nat) (initialState : ContractState) :
  let spec := simpleStorageSpec
  let irContract := compile spec [0x6057361d, 0x2e64cec1]
  let sender := "test_sender"
  let tx : Transaction := {
    sender := sender
    functionName := "store"
    args := [value]
  }
  let irTx : IRTransaction := {
    sender := addressToNat sender
    functionSelector := 0x6057361d
    args := [value]
  }
  let specResult := interpretSpec spec SpecStorage.empty tx
  match irContract with
  | .ok ir =>
      let irResult := interpretIR ir irTx (IRState.initial irTx.sender)
      resultsMatch ir.usesMapping [] irResult specResult
  | .error _ => False
  := by
  simpa using (Compiler.Proofs.IRGeneration.simpleStorage_store_correct value initialState)

end Compiler.Proofs.IRGeneration.StoreProof
