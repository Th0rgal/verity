import Compiler.ContractSpec
import Compiler.Codegen
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.YulGeneration.Equivalence
import Compiler.Proofs.YulGeneration.Semantics
import Compiler.Specs
import Std.Tactic

namespace Compiler.Proofs.YulGeneration

open Compiler
open Compiler.ContractSpec
open Compiler.Proofs.IRGeneration
open Compiler.Proofs
open Compiler.Specs
open Compiler.Yul

private def emptyStorage : Nat → Nat := fun _ => 0
private def emptyMappings : Nat → Nat → Nat := fun _ _ => 0

private def storageWith (slot value : Nat) : Nat → Nat :=
  fun s => if s = slot then value else 0

private def mappingsWith (base key value : Nat) : Nat → Nat → Nat :=
  fun b k => if b = base ∧ k = key then value else 0

/-! ## Yul Runtime Semantics Smoke Tests -/

private def runYul (runtimeCode : List YulStmt) (tx : YulTransaction)
    (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : YulResult :=
  let initialState := YulState.initial tx storage mappings
  let fuel := 500
  match execYulStmtsFuel fuel initialState runtimeCode with
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

-- return(0,32) returns memory[0]
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 55]),
      YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, returnValue := some 55, .. } => true
    | _ => false) = true := by
  native_decide

-- return(0,16) returns 0 in our single-word model
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 99]),
      YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 16])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, returnValue := some 0, .. } => true
    | _ => false) = true := by
  native_decide

-- stop halts successfully without mutating storage/mappings
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.lit 777]),
      YulStmt.expr (YulExpr.call "stop" [])
    ]
    let storage0 := storageWith 0 123
    let mappings0 := mappingsWith 1 2 456
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } storage0 mappings0 with
    | { success := true, returnValue := none, finalStorage, finalMappings } =>
        decide (finalStorage 0 = 777 ∧ finalMappings 1 2 = 456)
    | _ => false) = true := by
  native_decide

-- revert restores original storage and mappings
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.lit 777]),
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.call "mappingSlot" [YulExpr.lit 1, YulExpr.lit 2],
        YulExpr.lit 888
      ]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let storage0 := storageWith 0 123
    let mappings0 := mappingsWith 1 2 456
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } storage0 mappings0 with
    | { success := false, finalStorage, finalMappings, .. } =>
        decide (finalStorage 0 = 123 ∧ finalMappings 1 2 = 456)
    | _ => false) = true := by
  native_decide

-- sstore on mappingSlot updates mappings on success
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.call "mappingSlot" [YulExpr.lit 4, YulExpr.lit 9],
        YulExpr.lit 321
      ])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, finalMappings, .. } => decide (finalMappings 4 9 = 321)
    | _ => false) = true := by
  native_decide

-- sstore on encoded mapping slot routes through decodeMappingSlot
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.lit (encodeMappingSlot 4 9),
        YulExpr.lit 555
      ])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, finalMappings, .. } => decide (finalMappings 4 9 = 555)
    | _ => false) = true := by
  native_decide

-- sload from a plain storage slot returns stored value
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit 0, YulExpr.lit 123]),
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "sload" [YulExpr.lit 0]
      ]),
      YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, returnValue := some 123, .. } => true
    | _ => false) = true := by
  native_decide

-- sload from an encoded mapping slot returns mapped value
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.lit (encodeMappingSlot 4 9),
        YulExpr.lit 321
      ]),
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.lit 0,
        YulExpr.call "sload" [YulExpr.lit (encodeMappingSlot 4 9)]
      ]),
      YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, returnValue := some 321, .. } => true
    | _ => false) = true := by
  native_decide

-- sstore on an encoded nested mapping slot routes through mapping-of-mapping base slot
example :
    (let runtime := [
      YulStmt.expr (YulExpr.call "sstore" [
        YulExpr.lit (encodeNestedMappingSlot 3 4 5),
        YulExpr.lit 777
      ])
    ]
    match runYul runtime { sender := 0, functionSelector := 0, args := [] } emptyStorage emptyMappings with
    | { success := true, finalMappings, .. } =>
        let base := encodeMappingSlot 3 4
        decide (finalMappings base 5 = 777)
    | _ => false) = true := by
  native_decide

/-! ## IR vs Yul Smoke Tests -/

private def mkIRState (sender : Nat) (storage : Nat → Nat) (mappings : Nat → Nat → Nat) : IRState :=
  { (IRState.initial sender) with storage := storage, mappings := mappings }

private def interpretYulFromIRFuel (contract : IRContract) (tx : IRTransaction) (state : IRState) : YulResult :=
  let yulTx : YulTransaction := { sender := tx.sender, functionSelector := tx.functionSelector, args := tx.args }
  runYul (Compiler.runtimeCode contract) yulTx state.storage state.mappings

private def checkIRvsYul (ir : IRContract) (tx : IRTransaction) (state : IRState)
    (slots : List Nat) (mappingKeys : List (Nat × Nat)) : Bool :=
  let irResult := interpretIR ir tx state
  let yulResult := interpretYulFromIRFuel ir tx state
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
example :
    (match compile simpleStorageSpec simpleStorageSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 1, functionSelector := 0x6057361d, args := [42] }
        let state := mkIRState 1 emptyStorage emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- SimpleStorage.retrieve: return storage[0] = 7
example :
    (match compile simpleStorageSpec simpleStorageSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 2, functionSelector := 0x2e64cec1, args := [] }
        let state := mkIRState 2 (storageWith 0 7) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- Counter.increment: storage[0] = 10 → 11
example :
    (match compile counterSpec counterSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 3, functionSelector := 0xd09de08a, args := [] }
        let state := mkIRState 3 (storageWith 0 10) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- Ledger.deposit: mapping[0][sender] = 5 → 12
example :
    (match compile ledgerSpec ledgerSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 0x1234
        let tx : IRTransaction := { sender := sender, functionSelector := 0xb6b55f25, args := [7] }
        let state := mkIRState sender emptyStorage (mappingsWith 0 sender 5)
        checkIRvsYul ir tx state [] [(0, sender)]) = true := by
  native_decide

-- Owned.getOwner: return storage[0] = 0xBEEF
example :
    (match compile ownedSpec ownedSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 10, functionSelector := 0x893d20e8, args := [] }
        let state := mkIRState 10 (storageWith 0 0xBEEF) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- Owned.transferOwnership: non-owner reverts, storage unchanged
example :
    (match compile ownedSpec ownedSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 123, functionSelector := 0xf2fde38b, args := [0xCAFE] }
        let state := mkIRState 123 (storageWith 0 0xBEEF) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- Owned.transferOwnership: owner succeeds, storage updated
example :
    (match compile ownedSpec ownedSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 0xBEEF
        let newOwner := 0xCAFE
        let tx : IRTransaction := { sender := sender, functionSelector := 0xf2fde38b, args := [newOwner] }
        let state := mkIRState sender (storageWith 0 sender) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- SafeCounter.decrement: underflow reverts, storage unchanged
example :
    (match compile safeCounterSpec safeCounterSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 5, functionSelector := 0x2baeceb7, args := [] }
        let state := mkIRState 5 (storageWith 0 0) emptyMappings
        checkIRvsYul ir tx state [0] []) = true := by
  native_decide

-- OwnedCounter.increment: owner increments counter in slot 1
example :
    (match compile ownedCounterSpec ownedCounterSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 77
        let tx : IRTransaction := { sender := sender, functionSelector := 0xd09de08a, args := [] }
        let state := mkIRState sender (fun s => if s = 0 then sender else if s = 1 then 9 else 0) emptyMappings
        checkIRvsYul ir tx state [0, 1] []) = true := by
  native_decide

-- SimpleToken.transfer: sender balance 10 -> 7, recipient 1 -> 4
example :
    (match compile simpleTokenSpec simpleTokenSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 1001
        let recipient := 2002
        let tx : IRTransaction := { sender := sender, functionSelector := 0xa9059cbb, args := [recipient, 3] }
        let state := mkIRState sender emptyStorage (fun b k =>
          if b = 1 ∧ k = sender then 10 else if b = 1 ∧ k = recipient then 1 else 0)
        checkIRvsYul ir tx state [] [(1, sender), (1, recipient)]) = true := by
  native_decide

-- SimpleToken.transfer: insufficient balance reverts, mappings unchanged
example :
    (match compile simpleTokenSpec simpleTokenSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 1111
        let recipient := 2222
        let tx : IRTransaction := { sender := sender, functionSelector := 0xa9059cbb, args := [recipient, 5] }
        let state := mkIRState sender emptyStorage (fun b k =>
          if b = 1 ∧ k = sender then 2 else if b = 1 ∧ k = recipient then 7 else 0)
        checkIRvsYul ir tx state [] [(1, sender), (1, recipient)]) = true := by
  native_decide

-- SimpleToken.balanceOf: returns mapping[1][addr] = 42
example :
    (match compile simpleTokenSpec simpleTokenSelectors with
    | .error _ => false
    | .ok ir =>
        let addr := 3333
        let tx : IRTransaction := { sender := 0, functionSelector := 0x70a08231, args := [addr] }
        let state := mkIRState 0 emptyStorage (mappingsWith 1 addr 42)
        checkIRvsYul ir tx state [] [(1, addr)]) = true := by
  native_decide

-- SimpleToken.totalSupply: return storage[2] = 99
example :
    (match compile simpleTokenSpec simpleTokenSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 0, functionSelector := 0x18160ddd, args := [] }
        let state := mkIRState 0 (storageWith 2 99) emptyMappings
        checkIRvsYul ir tx state [2] []) = true := by
  native_decide

-- Unknown selector: dispatch should revert, storage/mappings unchanged
example :
    (match compile simpleStorageSpec simpleStorageSelectors with
    | .error _ => false
    | .ok ir =>
        let tx : IRTransaction := { sender := 9, functionSelector := 0xDEADBEEF, args := [] }
        let state := mkIRState 9 (storageWith 0 123) (mappingsWith 0 7 42)
        checkIRvsYul ir tx state [0] [(0, 7)]) = true := by
  native_decide

-- Unknown selector with mappings: revert, mappings unchanged
example :
    (match compile ledgerSpec ledgerSelectors with
    | .error _ => false
    | .ok ir =>
        let sender := 0xABCD
        let tx : IRTransaction := { sender := sender, functionSelector := 0xDEADBEEF, args := [1, 2] }
        let state := mkIRState sender emptyStorage (mappingsWith 0 sender 5)
        checkIRvsYul ir tx state [] [(0, sender)]) = true := by
  native_decide

/-! ## interpretYulRuntime Smoke Tests (enabled by making it computable, #270)

These tests exercise `interpretYulRuntime` directly (previously impossible
because it was noncomputable). They validate multi-step contract execution:
compile → execute → check result, all through the same interpreter used by proofs.
-/

-- SimpleStorage: store(42) then retrieve → 42 via interpretYulRuntime
example :
    (match compile simpleStorageSpec simpleStorageSelectors with
    | .error _ => false
    | .ok ir =>
        let yulCode := Compiler.runtimeCode ir
        let storeTx : YulTransaction := { sender := 1, functionSelector := 0x6057361d, args := [42] }
        let storeResult := interpretYulRuntime yulCode storeTx emptyStorage emptyMappings
        let retrieveTx : YulTransaction := { sender := 1, functionSelector := 0x2e64cec1, args := [] }
        let retrieveResult := interpretYulRuntime yulCode retrieveTx storeResult.finalStorage storeResult.finalMappings
        retrieveResult.success && retrieveResult.returnValue == some 42) = true := by
  native_decide

-- Counter: increment from 0 → getCount returns 1 via interpretYulRuntime
example :
    (match compile counterSpec counterSelectors with
    | .error _ => false
    | .ok ir =>
        let yulCode := Compiler.runtimeCode ir
        let incTx : YulTransaction := { sender := 1, functionSelector := 0xd09de08a, args := [] }
        let incResult := interpretYulRuntime yulCode incTx emptyStorage emptyMappings
        let getTx : YulTransaction := { sender := 1, functionSelector := 0xa87d942c, args := [] }
        let getResult := interpretYulRuntime yulCode getTx incResult.finalStorage incResult.finalMappings
        getResult.success && getResult.returnValue == some 1) = true := by
  native_decide

end Compiler.Proofs.YulGeneration
