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
private def dedupeMappingKeys (keys : List (Nat × Address)) : List (Nat × Address) :=
  let deduped := keys.foldl (fun acc key =>
    if acc.contains key then acc else key :: acc
  ) []
  deduped.reverse

def extractMappingChanges (before after : ContractState) (keys : List (Nat × Address)) : List (Nat × Address × Nat) :=
  let deduped := dedupeMappingKeys keys
  deduped.filterMap fun (slot, key) =>
    let oldVal := before.storageMap slot key
    let newVal := after.storageMap slot key
    if oldVal ≠ newVal then some (slot, key, newVal) else none

-- EVM revert data for Error(string) uses selector 0x08c379a0 in the first 32 bytes.
private def revertSelectorWord : Nat :=
  3963877391197344453575983046348115674221700746820753546331534351508065746944

private def revertReturnValue (msg : String) : Nat :=
  if msg.isEmpty then 0 else revertSelectorWord

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
  | ContractResult.revert msg _finalState =>
    { success := false
      returnValue := some (revertReturnValue msg)
      revertReason := some msg
      storageChanges := []  -- No changes on revert
      storageAddrChanges := []
      mappingChanges := []
    }

-- Helper: Convert ContractResult Uint256 to ContractResult Nat
private def resultToNat (result : ContractResult Uint256) : ContractResult Nat :=
  match result with
  | ContractResult.success returnVal finalState =>
    ContractResult.success returnVal.val finalState
  | ContractResult.revert msg finalState =>
    ContractResult.revert msg finalState

private def unitResultToNat (result : ContractResult Unit) : ContractResult Nat :=
  match result with
  | ContractResult.success _ finalState =>
    ContractResult.success 0 finalState
  | ContractResult.revert msg finalState =>
    ContractResult.revert msg finalState

private def runUnit
    (contract : Contract Unit)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address)) : ExecutionResult :=
  let result := contract.run state
  resultToExecutionResult (unitResultToNat result) state slotsToCheck addrSlotsToCheck mappingKeysToCheck

private def runUint
    (contract : Contract Uint256)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address)) : ExecutionResult :=
  let result := contract.run state
  resultToExecutionResult (resultToNat result) state slotsToCheck addrSlotsToCheck mappingKeysToCheck

private def runAddress
    (contract : Contract Address)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address)) : ExecutionResult :=
  let result := contract.run state
  let natResult : ContractResult Nat := match result with
    | ContractResult.success addr s => ContractResult.success (addressToNat addr) s
    | ContractResult.revert msg s => ContractResult.revert msg s
  resultToExecutionResult natResult state slotsToCheck addrSlotsToCheck mappingKeysToCheck

private def failureResult (msg : String) : ExecutionResult :=
  { success := false
    returnValue := none
    revertReason := some msg
    storageChanges := []
    storageAddrChanges := []
    mappingChanges := []
  }

private def invalidArgsResult : ExecutionResult :=
  failureResult "Invalid args"

private def unknownFunctionResult : ExecutionResult :=
  failureResult "Unknown function"

private def withArgs1 (tx : Transaction) (f : Nat → ExecutionResult) : ExecutionResult :=
  match tx.args with
  | [arg] => f arg
  | _ => invalidArgsResult

private def withArgs2 (tx : Transaction) (f : Nat → Nat → ExecutionResult) : ExecutionResult :=
  match tx.args with
  | [arg1, arg2] => f arg1 arg2
  | _ => invalidArgsResult

private def withNoArgs (tx : Transaction) (f : Unit → ExecutionResult) : ExecutionResult :=
  match tx.args with
  | [] => f ()
  | _ => invalidArgsResult

private def case0 (name : String) (tx : Transaction) (body : Unit → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  (name, fun _ => withNoArgs tx body)

private def case1 (name : String) (tx : Transaction) (f : Nat → ExecutionResult) : (String × (Unit → ExecutionResult)) :=
  (name, fun _ => withArgs1 tx f)

private def case2 (name : String) (tx : Transaction) (f : Nat → Nat → ExecutionResult) : (String × (Unit → ExecutionResult)) :=
  (name, fun _ => withArgs2 tx f)

private def case1Address (name : String) (tx : Transaction) (f : Address → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  case1 name tx (fun addrNat =>
    let addr := natToAddress addrNat
    f addr
  )

private def case2AddressNat (name : String) (tx : Transaction) (f : Address → Nat → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  case2 name tx (fun addrNat amount =>
    let addr := natToAddress addrNat
    f addr amount
  )

private def dispatch (tx : Transaction) (cases : List (String × (Unit → ExecutionResult))) : ExecutionResult :=
  match cases.find? (fun (name, _) => name == tx.functionName) with
  | some (_, f) => f ()
  | none => unknownFunctionResult

/-!
## Example: SimpleStorage Interpreter

Demonstrate how to wrap EDSL contract for differential testing.
-/

-- Interpret SimpleStorage transactions
def interpretSimpleStorage (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case1 "store" tx (fun value =>
      runUnit (store value) state [0] [] []  -- Check slot 0
    ),
    case0 "retrieve" tx (fun _ => runUint retrieve state [0] [] [])
  ]

/-!
## Counter Interpreter
-/

def interpretCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case0 "increment" tx (fun _ => runUnit Counter.increment state [0] [] []),
    case0 "decrement" tx (fun _ => runUnit Counter.decrement state [0] [] []),
    case0 "getCount" tx (fun _ => runUint Counter.getCount state [0] [] [])
  ]

/-!
## SafeCounter Interpreter
-/

def interpretSafeCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case0 "increment" tx (fun _ => runUnit SafeCounter.increment state [0] [] []),
    case0 "decrement" tx (fun _ => runUnit SafeCounter.decrement state [0] [] []),
    case0 "getCount" tx (fun _ => runUint SafeCounter.getCount state [0] [] [])
  ]

/-!
## Owned Interpreter
-/

def interpretOwned (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case1Address "transferOwnership" tx (fun newOwnerAddr =>
      runUnit (Owned.transferOwnership newOwnerAddr) state [] [0] []
    ),
    case0 "getOwner" tx (fun _ => runAddress Owned.getOwner state [] [0] [])
  ]

/-!
## Ledger Interpreter
-/

def interpretLedger (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case1 "deposit" tx (fun amount =>
      -- Track mapping changes for sender's balance
      let senderKey := (0, tx.sender)
      runUnit (Ledger.deposit amount) state [] [] [senderKey]
    ),
    case1 "withdraw" tx (fun amount =>
      -- Track mapping changes for sender's balance
      let senderKey := (0, tx.sender)
      runUnit (Ledger.withdraw amount) state [] [] [senderKey]
    ),
    case2AddressNat "transfer" tx (fun toAddr amount =>
      -- Track mapping changes for both sender and recipient
      let senderKey := (0, tx.sender)
      let recipientKey := (0, toAddr)
      runUnit (Ledger.transfer toAddr amount) state [] [] [senderKey, recipientKey]
    ),
    case1Address "getBalance" tx (fun addr =>
      -- Track mapping for the queried address
      let addrKey := (0, addr)
      runUint (Ledger.getBalance addr) state [] [] [addrKey]
    )
  ]

/-!
## OwnedCounter Interpreter
-/

def interpretOwnedCounter (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case0 "increment" tx (fun _ =>
      -- Track both storage slots: 0 (owner address) and 1 (count)
      runUnit OwnedCounter.increment state [1] [0] []
    ),
    case0 "decrement" tx (fun _ =>
      -- Track both storage slots: 0 (owner address) and 1 (count)
      runUnit OwnedCounter.decrement state [1] [0] []
    ),
    case0 "getCount" tx (fun _ => runUint OwnedCounter.getCount state [1] [] []),
    case0 "getOwner" tx (fun _ => runAddress OwnedCounter.getOwner state [] [0] []),
    case1Address "transferOwnership" tx (fun newOwnerAddr =>
      -- Track owner address storage slot 0
      runUnit (OwnedCounter.transferOwnership newOwnerAddr) state [] [0] []
    )
  ]

/-!
## SimpleToken Interpreter
-/

def interpretSimpleToken (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case2AddressNat "mint" tx (fun toAddr amount =>
      -- Track: storage slot 2 (totalSupply), owner slot 0, mapping for recipient
      let recipientKey := (1, toAddr)
      runUnit (SimpleToken.mint toAddr amount) state [2] [0] [recipientKey]
    ),
    case2AddressNat "transfer" tx (fun toAddr amount =>
      -- Track mapping changes for both sender and recipient
      let senderKey := (1, tx.sender)
      let recipientKey := (1, toAddr)
      runUnit (SimpleToken.transfer toAddr amount) state [] [] [senderKey, recipientKey]
    ),
    case1Address "balanceOf" tx (fun addr =>
      -- Track mapping for the queried address
      let addrKey := (1, addr)
      runUint (SimpleToken.balanceOf addr) state [] [] [addrKey]
    ),
    case0 "totalSupply" tx (fun _ => runUint SimpleToken.getTotalSupply state [2] [] []),
    case0 "owner" tx (fun _ => runAddress SimpleToken.getOwner state [] [0] [])
  ]

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
def parseStorage (storageStr : String) : Nat → Uint256 :=
  let pairs := storageStr.splitOn ","
  let storageMap := pairs.foldl (fun acc pair =>
    if pair.isEmpty then
      acc
    else
      match pair.splitOn ":" with
      | [slotStr, valStr] =>
        match parseArgNat? slotStr, parseArgNat? valStr with
        | some slot, some val =>
          let valU : Uint256 := val
          acc ++ [(slot, valU)]
        | _, _ => acc
      | _ => acc
  ) []
  fun slot => (storageMap.find? (fun (s, _) => s == slot)).map Prod.snd |>.getD 0

private def looksLikeStorage (s : String) : Bool :=
  s.data.any (fun c => c == ':' || c == ',')

private def looksLikeConfig (s : String) : Bool :=
  s.data.any (fun c => c == '=')

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
      else if normalized == "value" || normalized == "msgvalue" || normalized == "msg.value" then
        some ("value", value)
      else if normalized == "timestamp" || normalized == "blocktimestamp" || normalized == "block.timestamp" then
        some ("timestamp", value)
      else
        none
  | _ => none

private def isStorageConfigArg (s : String) : Bool :=
  match storageConfigPrefix s with
  | some _ => true
  | none => looksLikeStorage s || looksLikeConfig s

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
def parseStorageMap (storageStr : String) : Nat → Address → Uint256 :=
  let entries := storageStr.splitOn ","
  let mapping := entries.foldl (fun acc entry =>
    if entry.isEmpty then
      acc
    else
      match entry.splitOn ":" with
      | [slotStr, key, valStr] =>
        match parseArgNat? slotStr, parseArgNat? valStr with
        | some slot, some val =>
          let valU : Uint256 := val
          acc ++ [(slot, normalizeAddress key, valU)]
        | _, _ => acc
      | [slotStr, rest] =>
        match rest.splitOn "=" with
        | [key, valStr] =>
          match parseArgNat? slotStr, parseArgNat? valStr with
          | some slot, some val =>
            let valU : Uint256 := val
            acc ++ [(slot, normalizeAddress key, valU)]
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
    Except String (Option String × Option String × Option String × Option Nat × Option Nat) :=
  let rec go (args : List String)
      (storageOpt addrOpt mapOpt : Option String)
      (valueOpt timestampOpt : Option Nat) :
      Except String (Option String × Option String × Option String × Option Nat × Option Nat) :=
    match args with
    | [] => Except.ok (storageOpt, addrOpt, mapOpt, valueOpt, timestampOpt)
    | s :: rest =>
      let (kind, value) := parseStorageConfig s
      match kind with
      | "storage" =>
        if storageOpt.isSome then
          Except.error "Multiple storage args provided"
        else
          go rest (some value) addrOpt mapOpt valueOpt timestampOpt
      | "addr" =>
        if addrOpt.isSome then
          Except.error "Multiple address storage args provided"
        else
          go rest storageOpt (some value) mapOpt valueOpt timestampOpt
      | "map" =>
        if mapOpt.isSome then
          Except.error "Multiple mapping storage args provided"
        else
          go rest storageOpt addrOpt (some value) valueOpt timestampOpt
      | "value" =>
        if valueOpt.isSome then
          Except.error "Multiple msg.value args provided"
        else
          match parseArgNat? value with
          | some n => go rest storageOpt addrOpt mapOpt (some n) timestampOpt
          | none => Except.error "Invalid msg.value: expected decimal or 0x-prefixed hex integer"
      | "timestamp" =>
        if timestampOpt.isSome then
          Except.error "Multiple block.timestamp args provided"
        else
          match parseArgNat? value with
          | some n => go rest storageOpt addrOpt mapOpt valueOpt (some n)
          | none => Except.error "Invalid block.timestamp: expected decimal or 0x-prefixed hex integer"
      | _ => Except.error "Invalid config prefix"
  go configArgs none none none none none

def main (args : List String) : IO Unit := do
  match args with
  | contractType :: functionName :: senderAddr :: rest =>
    let (argStrs, configArgs) ← match splitTrailingStorageArgs rest with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    let (storageOpt, addrOpt, mapOpt, valueOpt, timestampOpt) ← match parseConfigArgs configArgs with
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
      msgValue := valueOpt.getD 0
      blockTimestamp := timestampOpt.getD 0
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
    IO.println "Usage: difftest-interpreter <contract> <function> <sender> [arg0] [storage] [addr=...] [map=...] [value=...] [timestamp=...]"
    IO.println "Example: difftest-interpreter SimpleStorage store 0xAlice 42"
    IO.println "No-arg example: difftest-interpreter SimpleStorage retrieve 0xAlice"
    IO.println "With storage: difftest-interpreter SimpleStorage retrieve 0xAlice \"0:42\""
    IO.println "With address storage: difftest-interpreter Owned transferOwnership 0xAlice 0xBob addr=\"0:0xAlice\""
    IO.println "With mapping: difftest-interpreter Ledger deposit 0xAlice 10 map=\"0:0xAlice=10\""
    IO.println "With context: difftest-interpreter Counter increment 0xAlice value=100 timestamp=1700000000"
