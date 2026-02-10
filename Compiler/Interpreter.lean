/-
  Compiler.Interpreter: EDSL Interpreter for Differential Testing

  This module provides an interpreter that executes EDSL contracts on abstract state,
  enabling comparison with compiled EVM execution for differential testing.

  Goal: Run the same transactions on:
  1. EDSL interpreter (this module) - trusted reference implementation
  2. Compiled Yul on EVM - what we're validating

  Success: Identical results → high confidence in compiler correctness
-/

import DumbContracts.Core
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Examples.Counter
import DumbContracts.Examples.SafeCounter
import Compiler.DiffTestTypes

namespace Compiler.Interpreter

open DumbContracts
open DumbContracts.Examples
open Compiler.DiffTestTypes

/-!
## Execution Result

Unified result type that captures what we need to compare between EDSL and EVM.
-/

structure ExecutionResult where
  success : Bool              -- true if succeeded, false if reverted
  returnValue : Option Nat    -- Return value for successful calls
  revertReason : Option String  -- Revert message if failed
  storageChanges : List (Nat × Nat)  -- Changed slots: (slot, newValue)
  storageAddrChanges : List (Nat × Nat)  -- Changed address slots: (slot, newValue as Nat)
  mappingChanges : List (Nat × Address × Nat)  -- Changed mapping entries: (base slot, key, newValue)

/-!
## EDSL Interpreter

Execute contracts using their verified EDSL definitions.
-/

-- Helper: Extract storage changes from before/after states
def extractStorageChanges (before after : ContractState) (slots : List Nat) : List (Nat × Nat) :=
  slots.filterMap fun slot =>
    let oldVal := before.storage slot
    let newVal := after.storage slot
    if oldVal ≠ newVal then some (slot, newVal) else none

-- Helper: Extract address storage changes from before/after states
def extractStorageAddrChanges (before after : ContractState) (slots : List Nat) : List (Nat × Address) :=
  slots.filterMap fun slot =>
    let oldVal := before.storageAddr slot
    let newVal := after.storageAddr slot
    if oldVal ≠ newVal then some (slot, newVal) else none

-- Helper: Extract mapping changes from before/after states
def extractMappingChanges (before after : ContractState) (keys : List (Nat × Address)) : List (Nat × Address × Nat) :=
  keys.filterMap fun (slot, key) =>
    let oldVal := before.storageMap slot key
    let newVal := after.storageMap slot key
    if oldVal ≠ newVal then some (slot, key, newVal) else none

-- Convert a hex address string (0x...) to Nat for JSON output
private def hexCharToNat? (c : Char) : Option Nat :=
  if c.isDigit then
    some (c.toNat - '0'.toNat)
  else if ('a' ≤ c ∧ c ≤ 'f') then
    some (10 + c.toNat - 'a'.toNat)
  else if ('A' ≤ c ∧ c ≤ 'F') then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

private def parseHexNat? (s : String) : Option Nat :=
  let s := if s.startsWith "0x" then s.drop 2 else s
  s.data.foldl (fun acc c =>
    match acc, hexCharToNat? c with
    | some n, some d => some (n * 16 + d)
    | _, _ => none
  ) (some 0)

private def addressToNat (addr : Address) : Nat :=
  (parseHexNat? addr).getD 0

-- Helper: Convert ContractResult to ExecutionResult
def resultToExecutionResult
    (result : ContractResult Nat)
    (initialState : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address)) : ExecutionResult :=
  match result with
  | ContractResult.success returnVal finalState =>
    let addrChanges := extractStorageAddrChanges initialState finalState addrSlotsToCheck
    { success := true
      returnValue := some returnVal
      revertReason := none
      storageChanges := extractStorageChanges initialState finalState slotsToCheck
      storageAddrChanges := addrChanges.map (fun (slot, addr) => (slot, addressToNat addr))
      mappingChanges := extractMappingChanges initialState finalState mappingKeysToCheck
    }
  | ContractResult.revert msg finalState =>
    { success := false
      returnValue := none
      revertReason := some msg
      storageChanges := []  -- No changes on revert
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## Example: SimpleStorage Interpreter

Demonstrate how to wrap EDSL contract for differential testing.
-/

-- Import SimpleStorage EDSL
private def exampleSimpleStorageStore (value : Nat) : Contract Unit :=
  store value

private def exampleSimpleStorageRetrieve : Contract Nat :=
  retrieve

-- Interpret SimpleStorage transactions
def interpretSimpleStorage (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "store" =>
    match tx.args with
    | [value] =>
      let result := (exampleSimpleStorageStore value).run state
      -- Convert Unit result to Nat (0 for success)
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      resultToExecutionResult natResult state [0] [] []  -- Check slot 0
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "retrieve" =>
    let result := exampleSimpleStorageRetrieve.run state
    resultToExecutionResult result state [0] [] []
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## Counter Interpreter
-/

private def exampleCounterIncrement : Contract Unit :=
  Counter.increment

private def exampleCounterDecrement : Contract Unit :=
  Counter.decrement

private def exampleCounterGetCount : Contract Nat :=
  Counter.getCount

def interpretCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "increment" =>
    let result := exampleCounterIncrement.run state
    let natResult : ContractResult Nat := match result with
      | ContractResult.success _ s => ContractResult.success 0 s
      | ContractResult.revert msg s => ContractResult.revert msg s
    resultToExecutionResult natResult state [0] [] []
  | "decrement" =>
    let result := exampleCounterDecrement.run state
    let natResult : ContractResult Nat := match result with
      | ContractResult.success _ s => ContractResult.success 0 s
      | ContractResult.revert msg s => ContractResult.revert msg s
    resultToExecutionResult natResult state [0] [] []
  | "getCount" =>
    let result := exampleCounterGetCount.run state
    resultToExecutionResult result state [0] [] []
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## SafeCounter Interpreter
-/

private def exampleSafeCounterIncrement : Contract Unit :=
  SafeCounter.increment

private def exampleSafeCounterDecrement : Contract Unit :=
  SafeCounter.decrement

private def exampleSafeCounterGetCount : Contract Nat :=
  SafeCounter.getCount

def interpretSafeCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "increment" =>
    let result := exampleSafeCounterIncrement.run state
    let natResult : ContractResult Nat := match result with
      | ContractResult.success _ s => ContractResult.success 0 s
      | ContractResult.revert msg s => ContractResult.revert msg s
    resultToExecutionResult natResult state [0] [] []
  | "decrement" =>
    let result := exampleSafeCounterDecrement.run state
    let natResult : ContractResult Nat := match result with
      | ContractResult.success _ s => ContractResult.success 0 s
      | ContractResult.revert msg s => ContractResult.revert msg s
    resultToExecutionResult natResult state [0] [] []
  | "getCount" =>
    let result := exampleSafeCounterGetCount.run state
    resultToExecutionResult result state [0] [] []
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## Generic Interpreter Interface

For use by the differential testing harness.
-/

def interpret (contractType : ContractType) (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match contractType with
  | ContractType.simpleStorage => interpretSimpleStorage tx state
  | ContractType.counter => interpretCounter tx state
  | ContractType.safeCounter => interpretSafeCounter tx state
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Not implemented"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## JSON Serialization

For communication with Foundry via vm.ffi.
-/

-- Simple JSON serialization (could be improved with proper JSON library)
def ExecutionResult.toJSON (r : ExecutionResult) : String :=
  let successStr := if r.success then "true" else "false"
  let returnStr := match r.returnValue with
    | some v => "\"" ++ toString v ++ "\""
    | none => "null"
  let revertStr := match r.revertReason with
    | some msg => "\"" ++ msg ++ "\""
    | none => "null"
  let changesStr := r.storageChanges.foldl (fun acc (slot, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slot ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let changesStr := changesStr ++ "]"
  let addrChangesStr := r.storageAddrChanges.foldl (fun acc (slot, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slot ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let addrChangesStr := addrChangesStr ++ "]"
  let mappingChangesStr := r.mappingChanges.foldl (fun acc (slot, key, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slot ++ ",\"key\":\"" ++ key ++ "\",\"value\":" ++ toString val ++ "}"
  ) "["
  let mappingChangesStr := mappingChangesStr ++ "]"
  "{\"success\":" ++ successStr
    ++ ",\"returnValue\":" ++ returnStr
    ++ ",\"revertReason\":" ++ revertStr
    ++ ",\"storageChanges\":" ++ changesStr
    ++ ",\"storageAddrChanges\":" ++ addrChangesStr
    ++ ",\"mappingChanges\":" ++ mappingChangesStr
    ++ "}"

end Compiler.Interpreter

/-!
## CLI Entry Point

For use via `lake exe difftest-interpreter`
-/

open Compiler.Interpreter
open Compiler.DiffTestTypes
open DumbContracts

-- Parse storage state from command line args
-- Format: "slot0:value0,slot1:value1,..."
def parseStorage (storageStr : String) : Nat → Nat :=
  let pairs := storageStr.splitOn ","
  let storageMap := pairs.foldl (fun acc pair =>
    match pair.splitOn ":" with
    | [slotStr, valStr] =>
      match slotStr.toNat?, valStr.toNat? with
      | some slot, some val => acc ++ [(slot, val)]
      | _, _ => acc
    | _ => acc
  ) []
  fun slot => (storageMap.find? (fun (s, _) => s == slot)).map Prod.snd |>.getD 0

def main (args : List String) : IO Unit := do
  match args with
  | contractType :: functionName :: senderAddr :: arg0 :: storageArgs =>
    let tx : Transaction := {
      sender := senderAddr
      functionName := functionName
      args := [arg0.toNat!]
    }
    -- Parse storage from remaining args (format: "slot:value,...")
    let storageState := match storageArgs with
      | [s] => parseStorage s
      | _ => fun _ => 0  -- Default: empty storage

    let initialState : ContractState := {
      storage := storageState
      storageAddr := fun _ => ""
      storageMap := fun _ _ => 0
      sender := senderAddr
      thisAddress := "0xContract"
    }
    let contractTypeEnum := match contractType with
      | "SimpleStorage" => ContractType.simpleStorage
      | "Counter" => ContractType.counter
      | "SafeCounter" => ContractType.safeCounter
      | _ => ContractType.simpleStorage  -- Default
    let result := interpret contractTypeEnum tx initialState
    IO.println result.toJSON
  | _ =>
    IO.println "Usage: difftest-interpreter <contract> <function> <sender> <arg0> [storage]"
    IO.println "Example: difftest-interpreter SimpleStorage store 0xAlice 42"
    IO.println "With storage: difftest-interpreter SimpleStorage retrieve 0xAlice 0 \"0:42\""
