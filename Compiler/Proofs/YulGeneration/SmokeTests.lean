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
private def safeCounterSelectors : List Nat := [0xd09de08a, 0x2baeceb7, 0xa87d942c]
private def ownedSelectors : List Nat := [0xf2fde38b, 0x893d20e8]
private def ownedCounterSelectors : List Nat :=
  [0xd09de08a, 0x2baeceb7, 0xa87d942c, 0x893d20e8, 0xf2fde38b]
private def ledgerSelectors : List Nat := [0xb6b55f25, 0x2e1a7d4d, 0xa9059cbb, 0xf8b2cb4f]
private def simpleTokenSelectors : List Nat :=
  [0x40c10f19, 0xa9059cbb, 0x70a08231, 0x18160ddd, 0x8da5cb5b]

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

-- Owned.getOwner: return storage[0] = 0xBEEF
#guard
  match compile ownedSpec ownedSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 10, functionSelector := 0x893d20e8, args := [] }
      let state := mkIRState 10 (storageWith 0 0xBEEF) emptyMappings
      checkIRvsYul ir tx state [0] []

-- Owned.transferOwnership: non-owner reverts, storage unchanged
#guard
  match compile ownedSpec ownedSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 123, functionSelector := 0xf2fde38b, args := [0xCAFE] }
      let state := mkIRState 123 (storageWith 0 0xBEEF) emptyMappings
      checkIRvsYul ir tx state [0] []

-- SafeCounter.decrement: underflow reverts, storage unchanged
#guard
  match compile safeCounterSpec safeCounterSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 5, functionSelector := 0x2baeceb7, args := [] }
      let state := mkIRState 5 (storageWith 0 0) emptyMappings
      checkIRvsYul ir tx state [0] []

-- OwnedCounter.increment: owner increments counter in slot 1
#guard
  match compile ownedCounterSpec ownedCounterSelectors with
  | .error _ => false
  | .ok ir =>
      let sender := 77
      let tx : IRTransaction := { sender := sender, functionSelector := 0xd09de08a, args := [] }
      let state := mkIRState sender (fun s => if s = 0 then sender else if s = 1 then 9 else 0) emptyMappings
      checkIRvsYul ir tx state [0, 1] []

-- SimpleToken.transfer: sender balance 10 -> 7, recipient 1 -> 4
#guard
  match compile simpleTokenSpec simpleTokenSelectors with
  | .error _ => false
  | .ok ir =>
      let sender := 1001
      let recipient := 2002
      let tx : IRTransaction := { sender := sender, functionSelector := 0xa9059cbb, args := [recipient, 3] }
      let state := mkIRState sender emptyStorage (fun b k =>
        if b = 1 ∧ k = sender then 10 else if b = 1 ∧ k = recipient then 1 else 0)
      checkIRvsYul ir tx state [] [(1, sender), (1, recipient)]

-- SimpleToken.balanceOf: returns mapping[1][addr] = 42
#guard
  match compile simpleTokenSpec simpleTokenSelectors with
  | .error _ => false
  | .ok ir =>
      let addr := 3333
      let tx : IRTransaction := { sender := 0, functionSelector := 0x70a08231, args := [addr] }
      let state := mkIRState 0 emptyStorage (mappingsWith 1 addr 42)
      checkIRvsYul ir tx state [] [(1, addr)]

-- SimpleToken.totalSupply: return storage[2] = 99
#guard
  match compile simpleTokenSpec simpleTokenSelectors with
  | .error _ => false
  | .ok ir =>
      let tx : IRTransaction := { sender := 0, functionSelector := 0x18160ddd, args := [] }
      let state := mkIRState 0 (storageWith 2 99) emptyMappings
      checkIRvsYul ir tx state [2] []

end Compiler.Proofs.YulGeneration
