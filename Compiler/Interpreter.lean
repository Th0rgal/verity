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
import DumbContracts.Examples.Owned
import DumbContracts.Examples.Ledger
import DumbContracts.Examples.OwnedCounter
import DumbContracts.Examples.SimpleToken
import Compiler.DiffTestTypes
import Compiler.Hex

namespace Compiler.Interpreter

open DumbContracts
open DumbContracts.Examples
open Compiler.DiffTestTypes
open Compiler.Hex

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

-- Helper: Normalize address to lowercase for consistent comparison
private def normalizeAddress (addr : Address) : Address :=
  addr.map Char.toLower

-- Helper: 160-bit address modulus (EVM address size)
private def addressModulus : Nat :=
  2 ^ 160

-- Helper: Convert Nat to properly formatted address (0x + 40 hex digits, lowercase)
private def natToAddress (n : Nat) : Address :=
  let masked := n % addressModulus
  let hexDigits := Nat.toDigits 16 masked
  let hexStr := hexDigits.asString
  -- Pad to 40 characters (20 bytes = 40 hex digits)
  let padded := String.mk (List.replicate (40 - hexStr.length) '0') ++ hexStr
  normalizeAddress ("0x" ++ padded)

-- Helper: Convert hex address string (0x...) to Nat for JSON output
private def addressToNat (addr : Address) : Nat :=
  Compiler.Hex.addressToNat (normalizeAddress addr) % addressModulus

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
## Owned Interpreter
-/

private def exampleOwnedTransferOwnership (newOwner : Address) : Contract Unit :=
  Owned.transferOwnership newOwner

private def exampleOwnedGetOwner : Contract Address :=
  Owned.getOwner

def interpretOwned (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "transferOwnership" =>
    match tx.args with
    | [newOwnerNat] =>
      -- Convert Nat to Address (properly formatted 40-digit hex string)
      let newOwnerAddr := natToAddress newOwnerNat
      let result := exampleOwnedTransferOwnership newOwnerAddr |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      resultToExecutionResult natResult state [] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "getOwner" =>
    let result := exampleOwnedGetOwner.run state
    -- Convert Address result to Nat for JSON output
    let natResult : ContractResult Nat := match result with
      | ContractResult.success addr s => ContractResult.success (addressToNat addr) s
      | ContractResult.revert msg s => ContractResult.revert msg s
    resultToExecutionResult natResult state [] [0] []
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## Ledger Interpreter
-/

private def exampleLedgerDeposit (amount : Nat) : Contract Unit :=
  Ledger.deposit amount

private def exampleLedgerWithdraw (amount : Nat) : Contract Unit :=
  Ledger.withdraw amount

private def exampleLedgerTransfer (to : Address) (amount : Nat) : Contract Unit :=
  Ledger.transfer to amount

private def exampleLedgerGetBalance (addr : Address) : Contract Nat :=
  Ledger.getBalance addr

def interpretLedger (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "deposit" =>
    match tx.args with
    | [amount] =>
      let result := exampleLedgerDeposit amount |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track mapping changes for sender's balance
      let senderKey := (0, tx.sender)
      resultToExecutionResult natResult state [] [] [senderKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "withdraw" =>
    match tx.args with
    | [amount] =>
      let result := exampleLedgerWithdraw amount |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track mapping changes for sender's balance
      let senderKey := (0, tx.sender)
      resultToExecutionResult natResult state [] [] [senderKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "transfer" =>
    match tx.args with
    | [toNat, amount] =>
      -- Convert Nat to Address (properly formatted 40-digit hex string)
      let toAddr := natToAddress toNat
      let result := exampleLedgerTransfer toAddr amount |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track mapping changes for both sender and recipient
      let senderKey := (0, tx.sender)
      let recipientKey := (0, toAddr)
      resultToExecutionResult natResult state [] [] [senderKey, recipientKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "getBalance" =>
    match tx.args with
    | [addrNat] =>
      -- Convert Nat to Address (properly formatted 40-digit hex string)
      let addr := natToAddress addrNat
      let result := exampleLedgerGetBalance addr |>.run state
      -- Track mapping for the queried address
      let addrKey := (0, addr)
      resultToExecutionResult result state [] [] [addrKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## OwnedCounter Interpreter
-/

private def exampleOwnedCounterIncrement : Contract Unit :=
  OwnedCounter.increment

private def exampleOwnedCounterDecrement : Contract Unit :=
  OwnedCounter.decrement

private def exampleOwnedCounterGetCount : Contract Nat :=
  OwnedCounter.getCount

private def exampleOwnedCounterGetOwner : Contract Address :=
  OwnedCounter.getOwner

private def exampleOwnedCounterTransferOwnership (newOwner : Address) : Contract Unit :=
  OwnedCounter.transferOwnership newOwner

def interpretOwnedCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "increment" =>
    match tx.args with
    | [] =>
      let result := exampleOwnedCounterIncrement |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track both storage slots: 0 (owner address) and 1 (count)
      resultToExecutionResult natResult state [1] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "decrement" =>
    match tx.args with
    | [] =>
      let result := exampleOwnedCounterDecrement |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track both storage slots: 0 (owner address) and 1 (count)
      resultToExecutionResult natResult state [1] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "getCount" =>
    match tx.args with
    | [] =>
      let result := exampleOwnedCounterGetCount |>.run state
      resultToExecutionResult result state [1] [] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "getOwner" =>
    match tx.args with
    | [] =>
      let result := exampleOwnedCounterGetOwner |>.run state
      -- Convert Address result to Nat for JSON output
      let natResult : ContractResult Nat := match result with
        | ContractResult.success addr s =>
          ContractResult.success (addressToNat addr) s
        | ContractResult.revert msg s => ContractResult.revert msg s
      resultToExecutionResult natResult state [] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "transferOwnership" =>
    match tx.args with
    | [newOwnerNat] =>
      -- Convert Nat to Address (properly formatted 40-digit hex string)
      let newOwnerAddr := natToAddress newOwnerNat
      let result := exampleOwnedCounterTransferOwnership newOwnerAddr |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track owner address storage slot 0
      resultToExecutionResult natResult state [] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | _ =>
    { success := false
      returnValue := none
      revertReason := some "Unknown function"
      storageChanges := []
      storageAddrChanges := []
      mappingChanges := []
    }

/-!
## SimpleToken Interpreter
-/

private def exampleSimpleTokenMint (to : Address) (amount : Nat) : Contract Unit :=
  SimpleToken.mint to amount

private def exampleSimpleTokenTransfer (to : Address) (amount : Nat) : Contract Unit :=
  SimpleToken.transfer to amount

private def exampleSimpleTokenBalanceOf (addr : Address) : Contract Nat :=
  SimpleToken.balanceOf addr

private def exampleSimpleTokenGetTotalSupply : Contract Nat :=
  SimpleToken.getTotalSupply

private def exampleSimpleTokenGetOwner : Contract Address :=
  SimpleToken.getOwner

def interpretSimpleToken (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match tx.functionName with
  | "mint" =>
    match tx.args with
    | [toNat, amount] =>
      -- Convert Nat to Address
      let toAddr := natToAddress toNat
      let result := exampleSimpleTokenMint toAddr amount |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track: storage slot 2 (totalSupply), owner slot 0, mapping for recipient
      let recipientKey := (1, toAddr)
      resultToExecutionResult natResult state [2] [0] [recipientKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "transfer" =>
    match tx.args with
    | [toNat, amount] =>
      -- Convert Nat to Address
      let toAddr := natToAddress toNat
      let result := exampleSimpleTokenTransfer toAddr amount |>.run state
      let natResult : ContractResult Nat := match result with
        | ContractResult.success _ s => ContractResult.success 0 s
        | ContractResult.revert msg s => ContractResult.revert msg s
      -- Track mapping changes for both sender and recipient
      let senderKey := (1, tx.sender)
      let recipientKey := (1, toAddr)
      resultToExecutionResult natResult state [] [] [senderKey, recipientKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "balanceOf" =>
    match tx.args with
    | [addrNat] =>
      -- Convert Nat to Address
      let addr := natToAddress addrNat
      let result := exampleSimpleTokenBalanceOf addr |>.run state
      -- Track mapping for the queried address
      let addrKey := (1, addr)
      resultToExecutionResult result state [] [] [addrKey]
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "totalSupply" =>
    match tx.args with
    | [] =>
      let result := exampleSimpleTokenGetTotalSupply |>.run state
      resultToExecutionResult result state [2] [] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
  | "getOwner" =>
    match tx.args with
    | [] =>
      let result := exampleSimpleTokenGetOwner |>.run state
      -- Convert Address result to Nat for JSON output
      let natResult : ContractResult Nat := match result with
        | ContractResult.success addr s =>
          ContractResult.success (addressToNat addr) s
        | ContractResult.revert msg s => ContractResult.revert msg s
      resultToExecutionResult natResult state [] [0] []
    | _ =>
      { success := false
        returnValue := none
        revertReason := some "Invalid args"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := []
      }
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
  | ContractType.owned => interpretOwned tx state
  | ContractType.ledger => interpretLedger tx state
  | ContractType.ownedCounter => interpretOwnedCounter tx state
  | ContractType.simpleToken => interpretSimpleToken tx state

/-!
## JSON Serialization

For communication with Foundry via vm.ffi.
-/

-- Simple JSON serialization (could be improved with proper JSON library)
private def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('a'.toNat + (n - 10))

private def toHex2 (n : Nat) : String :=
  let hi := (n / 16) % 16
  let lo := n % 16
  String.mk [hexDigit hi, hexDigit lo]

private def escapeJsonChar (c : Char) : String :=
  match c with
  | '\"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | '\u0008' => "\\b"
  | '\u000c' => "\\f"
  | _ =>
      if c.toNat < 0x20 then
        "\\u00" ++ toHex2 c.toNat
      else
        String.singleton c

private def escapeJsonString (s : String) : String :=
  s.data.foldl (fun acc c => acc ++ escapeJsonChar c) ""

def ExecutionResult.toJSON (r : ExecutionResult) : String :=
  let successStr := if r.success then "true" else "false"
  let returnStr := match r.returnValue with
    | some v => "\"" ++ toString v ++ "\""
    | none => "null"
  let revertStr := match r.revertReason with
    | some msg => "\"" ++ escapeJsonString msg ++ "\""
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
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slot ++ ",\"key\":\"" ++ escapeJsonString key ++ "\",\"value\":" ++ toString val ++ "}"
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
open Compiler.Hex
open DumbContracts

private def parseArgNat? (s : String) : Option Nat :=
  match parseHexNat? s with
  | some n => some n
  | none => s.toNat?

-- Parse storage state from command line args
-- Format: "slot0:value0,slot1:value1,..."
def parseStorage (storageStr : String) : Nat → Nat :=
  let pairs := storageStr.splitOn ","
  let storageMap := pairs.foldl (fun acc pair =>
    if pair.isEmpty then
      acc
    else
      match pair.splitOn ":" with
      | [slotStr, valStr] =>
        match parseArgNat? slotStr, parseArgNat? valStr with
        | some slot, some val => acc ++ [(slot, val)]
        | _, _ => acc
      | _ => acc
  ) []
  fun slot => (storageMap.find? (fun (s, _) => s == slot)).map Prod.snd |>.getD 0

private def looksLikeStorage (s : String) : Bool :=
  s.data.any (fun c => c == ':' || c == ',')

private def storageConfigPrefix (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | [pfx, value] =>
      let normalized := pfx.toLower
      if normalized == "storage" then
        some ("storage", value)
      else if normalized == "addr" || normalized == "address" || normalized == "storageaddr" then
        some ("addr", value)
      else if normalized == "map" || normalized == "mapping" || normalized == "storagemap" then
        some ("map", value)
      else
        none
  | _ => none

private def isStorageConfigArg (s : String) : Bool :=
  match storageConfigPrefix s with
  | some _ => true
  | none => looksLikeStorage s

private def parseStorageConfig (s : String) : (String × String) :=
  match storageConfigPrefix s with
  | some (kind, value) => (kind, value)
  | none => ("storage", s)

-- Parse address storage from command line args
-- Format: "slot0:addr0,slot1:addr1,..."
def parseStorageAddr (storageStr : String) : Nat → String :=
  let pairs := storageStr.splitOn ","
  let storageMap := pairs.foldl (fun acc pair =>
    if pair.isEmpty then
      acc
    else
      match pair.splitOn ":" with
      | [slotStr, addrStr] =>
        match parseArgNat? slotStr with
        | some slot => acc ++ [(slot, normalizeAddress addrStr)]
        | none => acc
      | _ => acc
  ) []
  fun slot => (storageMap.find? (fun (s, _) => s == slot)).map Prod.snd |>.getD ""

-- Parse mapping storage from command line args
-- Format: "slot0:key0:val0,slot1:key1=val1,..."
def parseStorageMap (storageStr : String) : Nat → String → Nat :=
  let entries := storageStr.splitOn ","
  let mapping := entries.foldl (fun acc entry =>
    if entry.isEmpty then
      acc
    else
      match entry.splitOn ":" with
      | [slotStr, key, valStr] =>
        match parseArgNat? slotStr, parseArgNat? valStr with
        | some slot, some val => acc ++ [(slot, normalizeAddress key, val)]
        | _, _ => acc
      | [slotStr, rest] =>
        match rest.splitOn "=" with
        | [key, valStr] =>
          match parseArgNat? slotStr, parseArgNat? valStr with
          | some slot, some val => acc ++ [(slot, normalizeAddress key, val)]
          | _, _ => acc
        | _ => acc
      | _ => acc
  ) []
  fun slot key =>
    let keyNorm := normalizeAddress key
    (mapping.find? (fun (s, k, _) => s == slot && k == keyNorm)).map (fun (_, _, v) => v) |>.getD 0

private def parseArgs (args : List String) : Except String (List Nat) :=
  let parsed := args.foldl (fun acc s =>
    match acc, parseArgNat? s with
    | some acc', some n => some (acc' ++ [n])
    | _, _ => none
  ) (some [])
  match parsed with
  | some vals => Except.ok vals
  | none => Except.error "Invalid args: expected decimal or 0x-prefixed hex integers"

private def splitTrailingStorageArgs (args : List String) : Except String (List String × List String) :=
  let rec takeConfigs (rev : List String) (configs : List String) : List String × List String :=
    match rev with
    | [] => (configs, [])
    | x :: xs =>
      if isStorageConfigArg x then
        takeConfigs xs (x :: configs)
      else
        (configs, rev)
  let rev := args.reverse
  let (configRev, argRev) := takeConfigs rev []
  let configArgs := configRev.reverse
  let argStrs := argRev.reverse
  if argStrs.any isStorageConfigArg then
    Except.error "Invalid args: storage config args must come last"
  else
    Except.ok (argStrs, configArgs)

private def parseConfigArgs (configArgs : List String) :
    Except String (Option String × Option String × Option String) :=
  let rec go (args : List String) (storageOpt addrOpt mapOpt : Option String) :
      Except String (Option String × Option String × Option String) :=
    match args with
    | [] => Except.ok (storageOpt, addrOpt, mapOpt)
    | s :: rest =>
      let (kind, value) := parseStorageConfig s
      match kind with
      | "storage" =>
        if storageOpt.isSome then
          Except.error "Multiple storage args provided"
        else
          go rest (some value) addrOpt mapOpt
      | "addr" =>
        if addrOpt.isSome then
          Except.error "Multiple address storage args provided"
        else
          go rest storageOpt (some value) mapOpt
      | "map" =>
        if mapOpt.isSome then
          Except.error "Multiple mapping storage args provided"
        else
          go rest storageOpt addrOpt (some value)
      | _ => Except.error "Invalid storage config prefix"
  go configArgs none none none

def main (args : List String) : IO Unit := do
  match args with
  | contractType :: functionName :: senderAddr :: rest =>
    let (argStrs, configArgs) ← match splitTrailingStorageArgs rest with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    let (storageOpt, addrOpt, mapOpt) ← match parseConfigArgs configArgs with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    -- Filter out empty strings from args (can happen when storage is empty)
    let nonEmptyArgStrs := argStrs.filter (fun s => !s.isEmpty)
    let argsNat ← match parseArgs nonEmptyArgStrs with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    let tx : Transaction := {
      sender := normalizeAddress senderAddr
      functionName := functionName
      args := argsNat
    }
    -- Parse storage from optional arg (format: "slot:value,...")
    let storageState := match storageOpt with
      | some s => parseStorage s
      | none => fun _ => 0  -- Default: empty storage
    let storageAddrState := match addrOpt with
      | some s => parseStorageAddr s
      | none => fun _ => "" -- Default: empty address storage
    let storageMapState := match mapOpt with
      | some s => parseStorageMap s
      | none => fun _ _ => 0 -- Default: empty mapping storage

    let initialState : ContractState := {
      storage := storageState
      storageAddr := storageAddrState
      storageMap := storageMapState
      sender := normalizeAddress senderAddr
      thisAddress := "0xContract"
      msgValue := 0
      blockTimestamp := 0
    }
    let contractTypeEnum? : Option ContractType := match contractType with
      | "SimpleStorage" => some ContractType.simpleStorage
      | "Counter" => some ContractType.counter
      | "Owned" => some ContractType.owned
      | "Ledger" => some ContractType.ledger
      | "OwnedCounter" => some ContractType.ownedCounter
      | "SimpleToken" => some ContractType.simpleToken
      | "SafeCounter" => some ContractType.safeCounter
      | _ => none
    match contractTypeEnum? with
    | some contractTypeEnum =>
      let result := interpret contractTypeEnum tx initialState
      IO.println result.toJSON
    | none =>
      throw <| IO.userError
        s!"Unknown contract type: {contractType}. Supported: SimpleStorage, Counter, Owned, Ledger, OwnedCounter, SimpleToken, SafeCounter"
  | _ =>
    IO.println "Usage: difftest-interpreter <contract> <function> <sender> [arg0] [storage] [addr=...] [map=...]"
    IO.println "Example: difftest-interpreter SimpleStorage store 0xAlice 42"
    IO.println "No-arg example: difftest-interpreter SimpleStorage retrieve 0xAlice"
    IO.println "With storage: difftest-interpreter SimpleStorage retrieve 0xAlice \"0:42\""
    IO.println "With address storage: difftest-interpreter Owned transferOwnership 0xAlice 0xBob addr=\"0:0xAlice\""
    IO.println "With mapping: difftest-interpreter Ledger deposit 0xAlice 10 map=\"0:0xAlice=10\""
