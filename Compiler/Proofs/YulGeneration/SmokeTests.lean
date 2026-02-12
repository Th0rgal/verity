import Compiler.ContractSpec
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Specs

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.ContractSpec
open Compiler.Proofs.IRGeneration
open Compiler.Specs
open Compiler.Yul

private def emptyStorage : Nat → Nat := fun _ => 0
private def emptyMappings : Nat → Nat → Nat := fun _ _ => 0

private def mkState (selector : Nat) (args : List Nat) : YulState :=
  YulState.initial { sender := 0, functionSelector := selector, args := args } emptyStorage emptyMappings

#eval evalYulExpr (mkState 7 []) (YulExpr.call "calldataload" [YulExpr.lit 0])

#eval evalYulExpr (mkState 7 [42]) (YulExpr.call "calldataload" [YulExpr.lit 4])

#eval evalYulExpr (mkState 7 [])
  (YulExpr.call "shr" [YulExpr.lit selectorShift, YulExpr.call "calldataload" [YulExpr.lit 0]])

/-! ## IR vs Yul Smoke Tests -/

private def storageWith (slot value : Nat) : Nat → Nat :=
  fun s => if s = slot then value else 0

private def mappingsWith (base key value : Nat) : Nat → Nat → Nat :=
  fun b k => if b = base ∧ k = key then value else 0

private def mkIRState (sender : Nat) (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : IRState :=
  { (IRState.initial sender) with storage := storage, mappings := mappings }

private def checkIRvsYul (ir : IRContract) (tx : IRTransaction) (state : IRState)
    (slots : List Nat) (mappingKeys : List (Nat × Nat)) : Bool :=
  let irResult := interpretIR ir tx state
  let yulResult := interpretYulFromIR ir tx state
  resultsMatchOn slots mappingKeys irResult yulResult

private def simpleStorageSelectors : List Nat := [0x6057361d, 0x2e64cec1]
private def counterSelectors : List Nat := [0xd09de08a, 0x2baeceb7, 0xa87d942c]
private def ledgerSelectors : List Nat := [0xb6b55f25, 0x2e1a7d4d, 0xa9059cbb, 0xf8b2cb4f]

-- SimpleStorage.store: storage[0] = 42
#guard
  match compile simpleStorageSpec simpleStorageSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 1, functionSelector := 0x6057361d, args := [42] }
      let state := mkIRState 1 emptyStorage emptyMappings
      checkIRvsYul ir tx state [0] []

-- SimpleStorage.retrieve: return storage[0] = 7
#guard
  match compile simpleStorageSpec simpleStorageSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 2, functionSelector := 0x2e64cec1, args := [] }
      let state := mkIRState 2 (storageWith 0 7) emptyMappings
      checkIRvsYul ir tx state [0] []

-- Counter.increment: storage[0] = 10 → 11
#guard
  match compile counterSpec counterSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 3, functionSelector := 0xd09de08a, args := [] }
      let state := mkIRState 3 (storageWith 0 10) emptyMappings
      checkIRvsYul ir tx state [0] []

-- Ledger.deposit: mapping[0][sender] = 5 → 12
#guard
  match compile ledgerSpec ledgerSelectors with
  | .error _ => false
  | .ok ir =>
      let sender := 0x1234
      let tx : IRTransaction := { sender := sender, functionSelector := 0xb6b55f25, args := [7] }
      let state := mkIRState sender emptyStorage (mappingsWith 0 sender 5)
      checkIRvsYul ir tx state [] [(0, sender)]

end Compiler.Proofs.YulGeneration
