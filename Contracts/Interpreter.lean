/- 
  Contracts.Interpreter: EDSL Interpreter for Differential Testing

  This module provides an interpreter that executes EDSL contracts on abstract state,
  enabling comparison with compiled EVM execution for differential testing.

  Goal: Run the same transactions on:
  1. EDSL interpreter (this module) - trusted reference implementation
  2. Compiled Yul on EVM - what we're validating

  Success: Identical results → high confidence in compiler correctness
-/

import Compiler.Constants
import Contracts
import Contracts.CryptoHash
import Compiler.DiffTestTypes
import Compiler.Hex
import Compiler.Json

namespace Compiler.Interpreter

open Compiler.Constants (errorStringSelectorWord addressModulus)

open Verity
open Contracts
open Compiler.DiffTestTypes
open Compiler.Hex
open Compiler.Json

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
  mappingUintChanges : List (Nat × Nat × Nat)  -- Changed uint-key mapping entries: (slot, key, value)
  mapping2Changes : List (Nat × Address × Address × Nat)  -- Changed 2-key mapping entries

/-!
## EDSL Interpreter

Execute contracts using their verified EDSL definitions.
-/

-- Helper: Extract storage changes from before/after states
def extractStorageChanges (before after : ContractState) (slots : List Nat) : List (Nat × Nat) :=
  slots.filterMap fun slotIdx =>
    let oldVal := before.storage slotIdx
    let newVal := after.storage slotIdx
    if oldVal ≠ newVal then some (slotIdx, newVal) else none

-- Helper: Extract address storage changes from before/after states
def extractStorageAddrChanges (before after : ContractState) (slots : List Nat) : List (Nat × Address) :=
  slots.filterMap fun slotIdx =>
    let oldVal := before.storageAddr slotIdx
    let newVal := after.storageAddr slotIdx
    if oldVal ≠ newVal then some (slotIdx, newVal) else none

-- Helper: Extract mapping changes from before/after states
private def dedupeMappingKeys (keys : List (Nat × Address)) : List (Nat × Address) :=
  let deduped := keys.foldl (fun acc key =>
    if acc.contains key then acc else key :: acc
  ) []
  deduped.reverse

def extractMappingChanges (before after : ContractState) (keys : List (Nat × Address)) : List (Nat × Address × Nat) :=
  let deduped := dedupeMappingKeys keys
  deduped.filterMap fun (slotIdx, key) =>
    let oldVal := before.storageMap slotIdx key
    let newVal := after.storageMap slotIdx key
    if oldVal ≠ newVal then some (slotIdx, key, newVal) else none

private def dedupeMappingUintKeys (keys : List (Nat × Uint256)) : List (Nat × Uint256) :=
  let deduped := keys.foldl (fun acc key =>
    if acc.contains key then acc else key :: acc
  ) []
  deduped.reverse

def extractMappingUintChanges (before after : ContractState) (keys : List (Nat × Uint256)) :
    List (Nat × Nat × Nat) :=
  let deduped := dedupeMappingUintKeys keys
  deduped.filterMap fun (slotIdx, key) =>
    let oldVal := before.storageMapUint slotIdx key
    let newVal := after.storageMapUint slotIdx key
    if oldVal ≠ newVal then some (slotIdx, key.val, newVal.val) else none

private def dedupeMapping2Keys (keys : List (Nat × Address × Address)) : List (Nat × Address × Address) :=
  let deduped := keys.foldl (fun acc key =>
    if acc.contains key then acc else key :: acc
  ) []
  deduped.reverse

def extractMapping2Changes (before after : ContractState) (keys : List (Nat × Address × Address)) :
    List (Nat × Address × Address × Nat) :=
  let deduped := dedupeMapping2Keys keys
  deduped.filterMap fun (slotIdx, key1, key2) =>
    let oldVal := before.storageMap2 slotIdx key1 key2
    let newVal := after.storageMap2 slotIdx key1 key2
    if oldVal ≠ newVal then some (slotIdx, key1, key2, newVal.val) else none

private def revertReturnValue (msg : String) : Nat :=
  if msg.isEmpty then 0 else errorStringSelectorWord

-- Helper: Convert Nat to Address (bounded to 160 bits)
private def natToAddress (n : Nat) : Address :=
  Verity.Core.Address.ofNat (n % addressModulus)

-- Helper: Convert Address to Nat for JSON output
private def addressToNat (addr : Address) : Nat :=
  addr.val

-- Helper: Convert Address to hex string for JSON output (matches Foundry's vm.toString(address))
private def addressToHexString (addr : Address) : String :=
  Compiler.Hex.natToHex addr.val 40

-- Helper: Convert ContractResult to ExecutionResult
def resultToExecutionResult
    (result : ContractResult Nat)
    (initialState : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address))
    (mappingUintKeysToCheck : List (Nat × Uint256))
    (mapping2KeysToCheck : List (Nat × Address × Address)) : ExecutionResult :=
  match result with
  | ContractResult.success returnVal finalState =>
    let addrChanges := extractStorageAddrChanges initialState finalState addrSlotsToCheck
    { success := true
      returnValue := some returnVal
      revertReason := none
      storageChanges := extractStorageChanges initialState finalState slotsToCheck
      storageAddrChanges := addrChanges.map (fun (slotIdx, addr) => (slotIdx, addressToNat addr))
      mappingChanges := extractMappingChanges initialState finalState mappingKeysToCheck
      mappingUintChanges := extractMappingUintChanges initialState finalState mappingUintKeysToCheck
      mapping2Changes := extractMapping2Changes initialState finalState mapping2KeysToCheck
    }
  | ContractResult.revert msg _finalState =>
    { success := false
      returnValue := some (revertReturnValue msg)
      revertReason := some msg
      storageChanges := []  -- No changes on revert
      storageAddrChanges := []
      mappingChanges := []
      mappingUintChanges := []
      mapping2Changes := []
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
    (mappingKeysToCheck : List (Nat × Address))
    (mappingUintKeysToCheck : List (Nat × Uint256) := [])
    (mapping2KeysToCheck : List (Nat × Address × Address) := []) : ExecutionResult :=
  let result := contract.run state
  resultToExecutionResult
    (unitResultToNat result)
    state
    slotsToCheck
    addrSlotsToCheck
    mappingKeysToCheck
    mappingUintKeysToCheck
    mapping2KeysToCheck

private def runUint
    (contract : Contract Uint256)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address))
    (mappingUintKeysToCheck : List (Nat × Uint256) := [])
    (mapping2KeysToCheck : List (Nat × Address × Address) := []) : ExecutionResult :=
  let result := contract.run state
  resultToExecutionResult
    (resultToNat result)
    state
    slotsToCheck
    addrSlotsToCheck
    mappingKeysToCheck
    mappingUintKeysToCheck
    mapping2KeysToCheck

private def runBool
    (contract : Contract Bool)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address))
    (mappingUintKeysToCheck : List (Nat × Uint256) := [])
    (mapping2KeysToCheck : List (Nat × Address × Address) := []) : ExecutionResult :=
  let result : ContractResult Nat := match contract.run state with
    | ContractResult.success value finalState => ContractResult.success (if value then 1 else 0) finalState
    | ContractResult.revert msg finalState => ContractResult.revert msg finalState
  resultToExecutionResult
    result
    state
    slotsToCheck
    addrSlotsToCheck
    mappingKeysToCheck
    mappingUintKeysToCheck
    mapping2KeysToCheck

private def runAddress
    (contract : Contract Address)
    (state : ContractState)
    (slotsToCheck : List Nat)
    (addrSlotsToCheck : List Nat)
    (mappingKeysToCheck : List (Nat × Address))
    (mappingUintKeysToCheck : List (Nat × Uint256) := [])
    (mapping2KeysToCheck : List (Nat × Address × Address) := []) : ExecutionResult :=
  let result := contract.run state
  let natResult : ContractResult Nat := match result with
    | ContractResult.success addr s => ContractResult.success (addressToNat addr) s
    | ContractResult.revert msg s => ContractResult.revert msg s
  resultToExecutionResult
    natResult
    state
    slotsToCheck
    addrSlotsToCheck
    mappingKeysToCheck
    mappingUintKeysToCheck
    mapping2KeysToCheck

private def failureResult (msg : String) : ExecutionResult :=
  { success := false
    returnValue := none
    revertReason := some msg
    storageChanges := []
    storageAddrChanges := []
    mappingChanges := []
    mappingUintChanges := []
    mapping2Changes := []
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

private def withArgs3 (tx : Transaction) (f : Nat → Nat → Nat → ExecutionResult) : ExecutionResult :=
  match tx.args with
  | [arg1, arg2, arg3] => f arg1 arg2 arg3
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

private def case3 (name : String) (tx : Transaction) (f : Nat → Nat → Nat → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  (name, fun _ => withArgs3 tx f)

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

private def case2AddressAddress (name : String) (tx : Transaction) (f : Address → Address → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  case2 name tx (fun addr1Nat addr2Nat =>
    f (natToAddress addr1Nat) (natToAddress addr2Nat)
  )

private def case3AddressAddressNat (name : String) (tx : Transaction) (f : Address → Address → Nat → ExecutionResult) :
    (String × (Unit → ExecutionResult)) :=
  case3 name tx (fun addr1Nat addr2Nat amount =>
    f (natToAddress addr1Nat) (natToAddress addr2Nat) amount
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
      runUnit (SimpleStorage.store value) state [0] [] []  -- Check slot 0
    ),
    case0 "retrieve" tx (fun _ => runUint SimpleStorage.retrieve state [0] [] [])
  ]

def interpretLocalObligationMacroSmoke (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case0 "unsafeEdge" tx (fun _ =>
      runUnit LocalObligationMacroSmoke.unsafeEdge state [0, 1] [] []
    ),
    case1 "dischargedEdge" tx (fun value =>
      runUint (LocalObligationMacroSmoke.dischargedEdge value) state [0, 1] [] []
    )
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
## Vault Interpreter
-/

def interpretVault (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case1 "deposit" tx (fun assets =>
      let senderKey := (2, tx.sender)
      runUnit (Vault.deposit assets) state [0, 1] [] [senderKey]
    ),
    case1 "withdraw" tx (fun shares =>
      let senderKey := (2, tx.sender)
      runUnit (Vault.withdraw shares) state [0, 1] [] [senderKey]
    ),
    case1Address "balanceOf" tx (fun addr =>
      let addrKey := (2, addr)
      runUint (Vault.balanceOf addr) state [] [] [addrKey]
    ),
    case0 "totalAssets" tx (fun _ => runUint Vault.getTotalAssets state [0] [] []),
    case0 "totalSupply" tx (fun _ => runUint Vault.getTotalSupply state [1] [] [])
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
## ERC20 Interpreter
-/

def interpretERC20 (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case2AddressNat "mint" tx (fun toAddr amount =>
      -- Track owner slot 0, totalSupply slot 1, and recipient balance in slot-2 mapping.
      let recipientKey := (2, toAddr)
      runUnit (ERC20.mint toAddr amount) state [1] [0] [recipientKey]
    ),
    case2AddressNat "transfer" tx (fun toAddr amount =>
      -- Track sender/recipient balances in slot-2 mapping.
      let senderKey := (2, tx.sender)
      let recipientKey := (2, toAddr)
      runUnit (ERC20.transfer toAddr amount) state [] [] [senderKey, recipientKey]
    ),
    case2AddressNat "approve" tx (fun spender amount =>
      let allowanceKey := (3, tx.sender, spender)
      runUnit (ERC20.approve spender amount) state [] [] [] [] [allowanceKey]
    ),
    case3AddressAddressNat "transferFrom" tx (fun fromAddr toAddr amount =>
      let fromKey := (2, fromAddr)
      let toKey := (2, toAddr)
      let allowanceKey := (3, fromAddr, tx.sender)
      runUnit (ERC20.transferFrom fromAddr toAddr amount) state [] [] [fromKey, toKey] [] [allowanceKey]
    ),
    case1Address "balanceOf" tx (fun addr =>
      let addrKey := (2, addr)
      runUint (ERC20.balanceOf addr) state [] [] [addrKey]
    ),
    case2AddressAddress "allowanceOf" tx (fun ownerAddr spender =>
      runUint (ERC20.allowanceOf ownerAddr spender) state [] [] []
    ),
    case0 "totalSupply" tx (fun _ => runUint ERC20.getTotalSupply state [1] [] []),
    case0 "owner" tx (fun _ => runAddress ERC20.getOwner state [] [0] [])
  ]

/-!
## ERC721 Interpreter
-/

def interpretERC721 (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case1Address "mint" tx (fun toAddr =>
      -- Track owner slot 0, counters (slots 1/2), recipient balance in slot-3 mapping,
      -- and owners[tokenId] in slot-4 mappingUint.
      let mintedTokenId : Uint256 := state.storage 2
      let recipientKey := (3, toAddr)
      let ownerWordKey := (4, mintedTokenId)
      runUint (ERC721.mint toAddr) state [1, 2] [0] [recipientKey] [ownerWordKey]
    ),
    case1Address "balanceOf" tx (fun addr =>
      let addrKey := (3, addr)
      runUint (ERC721.balanceOf addr) state [] [] [addrKey]
    ),
    case1 "ownerOf" tx (fun tokenId =>
      let tokenIdU : Uint256 := tokenId
      let ownerKey := (4, tokenIdU)
      runAddress (ERC721.ownerOf tokenIdU) state [] [] [] [ownerKey]
    ),
    case2AddressNat "approve" tx (fun approved tokenId =>
      let tokenIdU : Uint256 := tokenId
      let ownerKey := (4, tokenIdU)
      let approvalKey := (5, tokenIdU)
      runUnit (ERC721.approve approved tokenIdU) state [] [] [] [ownerKey, approvalKey]
    ),
    case1 "getApproved" tx (fun tokenId =>
      let tokenIdU : Uint256 := tokenId
      let ownerKey := (4, tokenIdU)
      let approvalKey := (5, tokenIdU)
      runAddress (ERC721.getApproved tokenIdU) state [] [] [] [ownerKey, approvalKey]
    ),
    case2AddressNat "setApprovalForAll" tx (fun operator approvedWord =>
      let ownerAddr := tx.sender
      let approvalKey := (6, ownerAddr, operator)
      runUnit (ERC721.setApprovalForAll operator (approvedWord != 0)) state [] [] [] [] [approvalKey]
    ),
    case2AddressAddress "isApprovedForAll" tx (fun ownerAddr operator =>
      let approvalKey := (6, ownerAddr, operator)
      runBool (ERC721.isApprovedForAll ownerAddr operator) state [] [] [] [] [approvalKey]
    ),
    case3AddressAddressNat "transferFrom" tx (fun fromAddr toAddr tokenId =>
      let tokenIdU : Uint256 := tokenId
      let fromKey := (3, fromAddr)
      let toKey := (3, toAddr)
      let ownerKey := (4, tokenIdU)
      let approvalKey := (5, tokenIdU)
      runUnit (ERC721.transferFrom fromAddr toAddr tokenIdU) state [] [] [fromKey, toKey] [ownerKey, approvalKey]
    ),
    case0 "owner" tx (fun _ => runAddress (getStorageAddr ERC721.owner) state [] [0] []),
    case0 "totalSupply" tx (fun _ => runUint (getStorage ERC721.totalSupply) state [1] [] []),
    case0 "nextTokenId" tx (fun _ => runUint (getStorage ERC721.nextTokenId) state [2] [] [])
  ]

def interpretCryptoHash (tx : Transaction) (state : ContractState) : ExecutionResult :=
  dispatch tx [
    case2 "storeHashTwo" tx (fun a b =>
      runUnit (Contracts.CryptoHash.storeHashTwo a b) state [0] [] []
    ),
    case3 "storeHashThree" tx (fun a b c =>
      runUnit (Contracts.CryptoHash.storeHashThree a b c) state [0] [] []
    ),
    case0 "getLastHash" tx (fun _ =>
      runUint Contracts.CryptoHash.getLastHash state [0] [] []
    )
  ]

/-!
## Generic Interpreter Interface

For use by the differential testing harness.
-/

def interpret (contractType : ContractType) (tx : Transaction) (state : ContractState) : ExecutionResult :=
  match contractType with
  | ContractType.simpleStorage => interpretSimpleStorage tx state
  | ContractType.localObligationMacroSmoke => interpretLocalObligationMacroSmoke tx state
  | ContractType.counter => interpretCounter tx state
  | ContractType.safeCounter => interpretSafeCounter tx state
  | ContractType.owned => interpretOwned tx state
  | ContractType.ledger => interpretLedger tx state
  | ContractType.vault => interpretVault tx state
  | ContractType.ownedCounter => interpretOwnedCounter tx state
  | ContractType.simpleToken => interpretSimpleToken tx state

/-!
## JSON Serialization

For communication with Foundry via vm.ffi.
-/

def ExecutionResult.toJSON (r : ExecutionResult) : String :=
  let successStr := if r.success then "true" else "false"
  let returnStr := match r.returnValue with
    | some v => "\"" ++ toString v ++ "\""
    | none => "null"
  let revertStr := match r.revertReason with
    | some msg => "\"" ++ escapeJsonString msg ++ "\""
    | none => "null"
  let changesStr := r.storageChanges.foldl (fun acc (slotIdx, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slotIdx ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let changesStr := changesStr ++ "]"
  let addrChangesStr := r.storageAddrChanges.foldl (fun acc (slotIdx, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slotIdx ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let addrChangesStr := addrChangesStr ++ "]"
  let mappingChangesStr := r.mappingChanges.foldl (fun acc (slotIdx, key, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slotIdx ++ ",\"key\":\"" ++ addressToHexString key ++ "\",\"value\":" ++ toString val ++ "}"
  ) "["
  let mappingChangesStr := mappingChangesStr ++ "]"
  let mappingUintChangesStr := r.mappingUintChanges.foldl (fun acc (slotIdx, key, val) =>
    acc ++ (if acc == "[" then "" else ",") ++ "{\"slot\":" ++ toString slotIdx ++ ",\"key\":" ++ toString key ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let mappingUintChangesStr := mappingUintChangesStr ++ "]"
  let mapping2ChangesStr := r.mapping2Changes.foldl (fun acc (slotIdx, key1, key2, val) =>
    acc ++ (if acc == "[" then "" else ",")
      ++ "{\"slot\":" ++ toString slotIdx
      ++ ",\"key1\":\"" ++ addressToHexString key1 ++ "\""
      ++ ",\"key2\":\"" ++ addressToHexString key2 ++ "\""
      ++ ",\"value\":" ++ toString val ++ "}"
  ) "["
  let mapping2ChangesStr := mapping2ChangesStr ++ "]"
  "{\"success\":" ++ successStr
    ++ ",\"returnValue\":" ++ returnStr
    ++ ",\"revertReason\":" ++ revertStr
    ++ ",\"storageChanges\":" ++ changesStr
    ++ ",\"storageAddrChanges\":" ++ addrChangesStr
    ++ ",\"mappingChanges\":" ++ mappingChangesStr
    ++ ",\"mappingUintChanges\":" ++ mappingUintChangesStr
    ++ ",\"mapping2Changes\":" ++ mapping2ChangesStr
    ++ "}"

end Compiler.Interpreter

/-!
## CLI Entry Point

For use via `lake exe difftest-interpreter`
-/

open Compiler.Interpreter
open Compiler.DiffTestTypes
open Compiler.Hex
open Verity

private def parseArgNat? (s : String) : Option Nat :=
  match parseHexNat? s with
  | some n => some n
  | none => s.toNat?

-- Generic parser for "slot:value,slot:value,..." storage formats.
-- Takes a value parser and default, returns a slot→value lookup function.
private def parseSlotPairs (storageStr : String) (parseVal : String → Option α) (default : α) : Nat → α :=
  let pairs := storageStr.splitOn ","
  let entries := pairs.foldl (fun acc pair =>
    if pair.isEmpty then acc
    else match pair.splitOn ":" with
      | [slotStr, valStr] =>
        match parseArgNat? slotStr, parseVal valStr with
        | some slotIdx, some val => acc ++ [(slotIdx, val)]
        | _, _ => acc
      | _ => acc
  ) []
  fun slotIdx => (entries.find? (fun (s, _) => s == slotIdx)).map Prod.snd |>.getD default

-- Parse storage state: "slot0:value0,slot1:value1,..."
def parseStorage (storageStr : String) : Nat → Uint256 :=
  parseSlotPairs storageStr (fun s => (parseArgNat? s).map (fun n => (n : Uint256))) 0

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
      else if normalized == "mapuint" || normalized == "mappinguint" || normalized == "storagemapuint" then
        some ("mapuint", value)
      else if normalized == "map2" || normalized == "mapping2" || normalized == "storagemap2" then
        some ("map2", value)
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

-- Parse address storage: "slot0:addr0,slot1:addr1,..."
def parseStorageAddr (storageStr : String) : Nat → Address :=
  parseSlotPairs storageStr (fun s => some (Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress s)))) (0 : Address)

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
        | some slotIdx, some val =>
          let valU : Uint256 := val
          let keyAddr := Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress key))
          acc ++ [(slotIdx, keyAddr, valU)]
        | _, _ => acc
      | [slotStr, rest] =>
        match rest.splitOn "=" with
        | [key, valStr] =>
          match parseArgNat? slotStr, parseArgNat? valStr with
          | some slotIdx, some val =>
            let valU : Uint256 := val
            let keyAddr := Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress key))
            acc ++ [(slotIdx, keyAddr, valU)]
          | _, _ => acc
        | _ => acc
      | _ => acc
  ) []
  fun slotIdx key =>
    (mapping.find? (fun (s, k, _) => s == slotIdx && k == key)).map (fun (_, _, v) => v) |>.getD 0

def parseStorageMapUint (storageStr : String) : Nat → Uint256 → Uint256 :=
  let entries := storageStr.splitOn ","
  let mapping := entries.foldl (fun acc entry =>
    if entry.isEmpty then
      acc
    else
      match entry.splitOn ":" with
      | [slotStr, keyStr, valStr] =>
        match parseArgNat? slotStr, parseArgNat? keyStr, parseArgNat? valStr with
        | some slotIdx, some key, some val =>
          acc ++ [(slotIdx, (key : Uint256), (val : Uint256))]
        | _, _, _ => acc
      | [slotStr, rest] =>
        match rest.splitOn "=" with
        | [keyStr, valStr] =>
          match parseArgNat? slotStr, parseArgNat? keyStr, parseArgNat? valStr with
          | some slotIdx, some key, some val =>
            acc ++ [(slotIdx, (key : Uint256), (val : Uint256))]
          | _, _, _ => acc
        | _ => acc
      | _ => acc
  ) []
  fun slotIdx key =>
    (mapping.find? (fun (s, k, _) => s == slotIdx && k == key)).map (fun (_, _, v) => v) |>.getD 0

def parseStorageMap2 (storageStr : String) : Nat → Address → Address → Uint256 :=
  let entries := storageStr.splitOn ","
  let mapping := entries.foldl (fun acc entry =>
    if entry.isEmpty then
      acc
    else
      match entry.splitOn ":" with
      | [slotStr, key1Str, key2Str, valStr] =>
        match parseArgNat? slotStr, parseArgNat? valStr with
        | some slotIdx, some val =>
          let key1 := Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress key1Str))
          let key2 := Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress key2Str))
          acc ++ [(slotIdx, key1, key2, (val : Uint256))]
        | _, _ => acc
      | _ => acc
  ) []
  fun slotIdx key1 key2 =>
    (mapping.find? (fun (s, k1, k2, _) => s == slotIdx && k1 == key1 && k2 == key2)).map (fun (_, _, _, v) => v) |>.getD 0

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
    Except String (Option String × Option String × Option String × Option String × Option String × Option Nat × Option Nat) :=
  let rec go (args : List String)
      (storageOpt addrOpt mapOpt mapUintOpt map2Opt : Option String)
      (valueOpt timestampOpt : Option Nat) :
      Except String (Option String × Option String × Option String × Option String × Option String × Option Nat × Option Nat) :=
    match args with
    | [] => Except.ok (storageOpt, addrOpt, mapOpt, mapUintOpt, map2Opt, valueOpt, timestampOpt)
    | s :: rest =>
      let (kind, value) := parseStorageConfig s
      match kind with
      | "storage" =>
        if storageOpt.isSome then
          Except.error "Multiple storage args provided"
        else
          go rest (some value) addrOpt mapOpt mapUintOpt map2Opt valueOpt timestampOpt
      | "addr" =>
        if addrOpt.isSome then
          Except.error "Multiple address storage args provided"
        else
          go rest storageOpt (some value) mapOpt mapUintOpt map2Opt valueOpt timestampOpt
      | "map" =>
        if mapOpt.isSome then
          Except.error "Multiple mapping storage args provided"
        else
          go rest storageOpt addrOpt (some value) mapUintOpt map2Opt valueOpt timestampOpt
      | "mapuint" =>
        if mapUintOpt.isSome then
          Except.error "Multiple mapping-uint storage args provided"
        else
          go rest storageOpt addrOpt mapOpt (some value) map2Opt valueOpt timestampOpt
      | "map2" =>
        if map2Opt.isSome then
          Except.error "Multiple mapping2 storage args provided"
        else
          go rest storageOpt addrOpt mapOpt mapUintOpt (some value) valueOpt timestampOpt
      | "value" =>
        if valueOpt.isSome then
          Except.error "Multiple msg.value args provided"
        else
          match parseArgNat? value with
          | some n => go rest storageOpt addrOpt mapOpt mapUintOpt map2Opt (some n) timestampOpt
          | none => Except.error "Invalid msg.value: expected decimal or 0x-prefixed hex integer"
      | "timestamp" =>
        if timestampOpt.isSome then
          Except.error "Multiple block.timestamp args provided"
        else
          match parseArgNat? value with
          | some n => go rest storageOpt addrOpt mapOpt mapUintOpt map2Opt valueOpt (some n)
          | none => Except.error "Invalid block.timestamp: expected decimal or 0x-prefixed hex integer"
      | _ => Except.error "Invalid config prefix"
  go configArgs none none none none none none none

def main (args : List String) : IO Unit := do
  match args with
  | contractType :: functionName :: senderAddr :: rest =>
    let (argStrs, configArgs) ← match splitTrailingStorageArgs rest with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    let (storageOpt, addrOpt, mapOpt, mapUintOpt, map2Opt, valueOpt, timestampOpt) ← match parseConfigArgs configArgs with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    -- Filter out empty strings from args (can happen when storage is empty)
    let nonEmptyArgStrs := argStrs.filter (fun s => !s.isEmpty)
    let argsNat ← match parseArgs nonEmptyArgStrs with
      | Except.ok vals => pure vals
      | Except.error msg => throw <| IO.userError msg
    let senderAddress := Verity.Core.Address.ofNat (Compiler.Hex.addressToNat (normalizeAddress senderAddr))
    let tx : Transaction := {
      sender := senderAddress
      functionName := functionName
      args := argsNat
      msgValue := valueOpt.getD 0
      blockTimestamp := timestampOpt.getD 0
    }
    -- Parse storage from optional arg (format: "slot:value,...")
    let storageState := match storageOpt with
      | some s => parseStorage s
      | none => fun _ => 0  -- Default: empty storage
    let storageAddrState := match addrOpt with
      | some s => parseStorageAddr s
      | none => fun _ => (0 : Address) -- Default: empty address storage
    let storageMapState := match mapOpt with
      | some s => parseStorageMap s
      | none => fun _ _ => 0 -- Default: empty mapping storage
    let storageMapUintState := match mapUintOpt with
      | some s => parseStorageMapUint s
      | none => fun _ _ => 0 -- Default: empty uint-key mapping storage
    let storageMap2State := match map2Opt with
      | some s => parseStorageMap2 s
      | none => fun _ _ _ => 0 -- Default: empty 2-key mapping storage

    let initialState : ContractState := {
      «storage» := storageState
      transientStorage := fun _ => 0
      storageAddr := storageAddrState
      storageMap := storageMapState
      storageMapUint := storageMapUintState
      storageMap2 := storageMap2State
      sender := senderAddress
      thisAddress := Verity.Core.Address.ofNat 0xC0437AC7
      msgValue := valueOpt.getD 0
      blockTimestamp := timestampOpt.getD 0
      knownAddresses := fun _ => Verity.Core.FiniteAddressSet.empty
      events := []
    }
    let contractTypeEnum? : Option ContractType := match contractType with
      | "SimpleStorage" => some ContractType.simpleStorage
      | "LocalObligationMacroSmoke" => some ContractType.localObligationMacroSmoke
      | "Counter" => some ContractType.counter
      | "Owned" => some ContractType.owned
      | "Ledger" => some ContractType.ledger
      | "Vault" => some ContractType.vault
      | "OwnedCounter" => some ContractType.ownedCounter
      | "SimpleToken" => some ContractType.simpleToken
      | "SafeCounter" => some ContractType.safeCounter
      | "ERC20" => none
      | "ERC721" => none
      | "CryptoHash" => none
      | _ => none
    let result := match contractType with
      | "ERC20" => some (interpretERC20 tx initialState)
      | "ERC721" => some (interpretERC721 tx initialState)
      | "CryptoHash" => some (interpretCryptoHash tx initialState)
      | _ => contractTypeEnum?.map (fun contractTypeEnum => interpret contractTypeEnum tx initialState)
    match result with
    | some out =>
      IO.println out.toJSON
    | none =>
      throw <| IO.userError
        s!"Unknown contract type: {contractType}. Supported: SimpleStorage, LocalObligationMacroSmoke, Counter, Owned, Ledger, OwnedCounter, SimpleToken, SafeCounter, ERC20, ERC721, CryptoHash"
  | _ =>
    IO.println "Usage: difftest-interpreter <contract> <function> <sender> [arg0] [storage] [addr=...] [map=...] [mapuint=...] [map2=...] [value=...] [timestamp=...]"
    IO.println "Example: difftest-interpreter SimpleStorage store 0xAlice 42"
    IO.println "No-arg example: difftest-interpreter SimpleStorage retrieve 0xAlice"
    IO.println "With storage: difftest-interpreter SimpleStorage retrieve 0xAlice \"0:42\""
    IO.println "With address storage: difftest-interpreter Owned transferOwnership 0xAlice 0xBob addr=\"0:0xAlice\""
    IO.println "With mapping: difftest-interpreter Ledger deposit 0xAlice 10 map=\"0:0xAlice=10\""
    IO.println "With uint-key mapping: difftest-interpreter ERC721 ownerOf 0xAlice 0 mapuint=\"4:0:0xA11CE\""
    IO.println "With 2-key mapping: difftest-interpreter ERC20 allowanceOf 0xAlice 0xA11CE 0xB0B map2=\"3:0xA11CE:0xB0B:10\""
    IO.println "With context: difftest-interpreter Counter increment 0xAlice value=100 timestamp=1700000000"
