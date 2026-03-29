/-
  Shared helpers for specs.

  Keep specs human-friendly by naming the common "unchanged" clauses
  instead of repeating field-by-field equality.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Specs

open Verity
open Verity.EVM.Uint256

/-- Contract context (sender, address, msg value, timestamp, block number, chain id, blob base fee, calldata size) is unchanged. -/
def sameContext (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp ∧
  s'.blockNumber = s.blockNumber ∧
  s'.chainId = s.chainId ∧
  s'.blobBaseFee = s.blobBaseFee ∧
  s'.calldataSize = s.calldataSize

@[simp] theorem sameContext_rfl (s : ContractState) : sameContext s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Uint256 storage is unchanged. -/
def sameStorage (s s' : ContractState) : Prop :=
  s'.storage = s.storage

@[simp] theorem sameStorage_rfl (s : ContractState) : sameStorage s s := rfl

/-- One Uint256 storage slot is unchanged. -/
def sameStorageSlot (slot : Nat) (s s' : ContractState) : Prop :=
  s'.storage slot = s.storage slot

@[simp] theorem sameStorageSlot_rfl (slot : Nat) (s : ContractState) :
    sameStorageSlot slot s s := rfl

/-- Address storage is unchanged. -/
def sameStorageAddr (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

@[simp] theorem sameStorageAddr_rfl (s : ContractState) : sameStorageAddr s s := rfl

/-- One address storage slot is unchanged. -/
def sameStorageAddrSlot (slot : Nat) (s s' : ContractState) : Prop :=
  s'.storageAddr slot = s.storageAddr slot

@[simp] theorem sameStorageAddrSlot_rfl (slot : Nat) (s : ContractState) :
    sameStorageAddrSlot slot s s := rfl

/-- Mapping storage is unchanged. -/
def sameStorageMap (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

@[simp] theorem sameStorageMap_rfl (s : ContractState) : sameStorageMap s s := rfl

/-- Uint256-keyed mapping storage is unchanged. -/
def sameStorageMapUint (s s' : ContractState) : Prop :=
  s'.storageMapUint = s.storageMapUint

@[simp] theorem sameStorageMapUint_rfl (s : ContractState) : sameStorageMapUint s s := rfl

/-- Double mapping storage is unchanged. -/
def sameStorageMap2 (s s' : ContractState) : Prop :=
  s'.storageMap2 = s.storageMap2

@[simp] theorem sameStorageMap2_rfl (s : ContractState) : sameStorageMap2 s s := rfl

/-- Dynamic-array storage is unchanged. -/
def sameStorageArray (s s' : ContractState) : Prop :=
  s'.storageArray = s.storageArray

@[simp] theorem sameStorageArray_rfl (s : ContractState) : sameStorageArray s s := rfl

/-- Event log is unchanged. -/
def sameEvents (s s' : ContractState) : Prop :=
  s'.events = s.events

@[simp] theorem sameEvents_rfl (s : ContractState) : sameEvents s s := rfl

/-- Known addresses tracking is unchanged. -/
def sameKnownAddresses (s s' : ContractState) : Prop :=
  s'.knownAddresses = s.knownAddresses

@[simp] theorem sameKnownAddresses_rfl (s : ContractState) : sameKnownAddresses s s := rfl

/-- Address storage, mapping storage, and context are unchanged. -/
def sameAddrMapContext (s s' : ContractState) : Prop :=
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameAddrMapContext_rfl (s : ContractState) : sameAddrMapContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, mapping storage, and context are unchanged. -/
def sameStorageMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMapContext_rfl (s : ContractState) : sameStorageMapContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, address storage, and context are unchanged. -/
def sameStorageAddrContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrContext_rfl (s : ContractState) : sameStorageAddrContext s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage, double-mapping storage, and context are unchanged. -/
def sameStorageMap2Context (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMap2Context_rfl (s : ContractState) : sameStorageMap2Context s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage and context are unchanged. -/
def sameMapContext (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameMapContext_rfl (s : ContractState) : sameMapContext s s :=
  ⟨rfl, rfl, sameContext_rfl s⟩

/-- One address slot and context are unchanged. -/
def sameStorageAddrSlotContext (addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageAddrSlot addrSlot s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrSlotContext_rfl (addrSlot : Nat) (s : ContractState) :
    sameStorageAddrSlotContext addrSlot s s :=
  ⟨rfl, sameContext_rfl s⟩

/-- One address slot, double-mapping storage, and context are unchanged. -/
def sameStorageAddrSlotMap2Context (addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageAddrSlot addrSlot s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrSlotMap2Context_rfl (addrSlot : Nat) (s : ContractState) :
    sameStorageAddrSlotMap2Context addrSlot s s :=
  ⟨rfl, rfl, rfl, sameContext_rfl s⟩

/-- One Uint256 slot, one address slot, double-mapping storage, and context are unchanged. -/
def sameStorageSlotAddrSlotMap2Context
    (storageSlot addrSlot : Nat) (s s' : ContractState) : Prop :=
  sameStorageSlot storageSlot s s' ∧
  sameStorageAddrSlot addrSlot s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageSlotAddrSlotMap2Context_rfl
    (storageSlot addrSlot : Nat) (s : ContractState) :
    sameStorageSlotAddrSlotMap2Context storageSlot addrSlot s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, address storage, mapping storage, and context are unchanged. -/
def sameStorageAddrMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrMapContext_rfl (s : ContractState) : sameStorageAddrMapContext s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Uint256/address storage, mapping storage (word+uint-keyed), and context are unchanged. -/
def sameStorageAddrMapUintContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrMapUintContext_rfl (s : ContractState) : sameStorageAddrMapUintContext s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- Mapping storage (word + uint-keyed + double), and context are unchanged. -/
def sameStorageMapsContext (s s' : ContractState) : Prop :=
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMapsContext_rfl (s : ContractState) : sameStorageMapsContext s s :=
  ⟨rfl, rfl, rfl, rfl, sameContext_rfl s⟩

/-- All storage slots except `slot` are unchanged. -/
def storageUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storage other = s.storage other

/-- All address storage slots except `slot` are unchanged. -/
def storageAddrUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storageAddr other = s.storageAddr other

/-- Canonical two-state spec shape for updating one `storage` slot. -/
def storageUpdateSpec
    (slot : Nat)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storage slot = value s ∧
  storageUnchangedExcept slot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot. -/
def storageAddrUpdateSpec
    (slot : Nat)
    (value : ContractState → Address)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr slot = value s ∧
  storageAddrUnchangedExcept slot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot and one `storage` slot. -/
def storageAddrStorageUpdateSpec
    (addrSlot storageSlot : Nat)
    (addrValue : ContractState → Address)
    (storageValue : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr addrSlot = addrValue s ∧
  s'.storage storageSlot = storageValue s ∧
  storageAddrUnchangedExcept addrSlot s s' ∧
  storageUnchangedExcept storageSlot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageAddr` slot and two `storage` slots. -/
def storageAddrStorage2UpdateSpec
    (addrSlot storageSlot1 storageSlot2 : Nat)
    (addrValue : ContractState → Address)
    (storageValue1 storageValue2 : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageAddr addrSlot = addrValue s ∧
  s'.storage storageSlot1 = storageValue1 s ∧
  s'.storage storageSlot2 = storageValue2 s ∧
  storageAddrUnchangedExcept addrSlot s s' ∧
  (∀ other : Nat, other ≠ storageSlot1 → other ≠ storageSlot2 → s'.storage other = s.storage other) ∧
  frame s s'

/-- Canonical two-state spec shape for updating two `storage` slots. -/
def storage2UpdateSpec
    (slot1 slot2 : Nat)
    (value1 value2 : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storage slot1 = value1 s ∧
  s'.storage slot2 = value2 s ∧
  (∀ other : Nat, other ≠ slot1 → other ≠ slot2 → s'.storage other = s.storage other) ∧
  frame s s'

/-- All mapping storage slots except `slot` are unchanged. -/
def storageMapUnchangedExceptSlot (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → ∀ addr : Address, s'.storageMap other addr = s.storageMap other addr

/-- All mapping entries at `slot` except `addr` are unchanged. -/
def storageMapUnchangedExceptKey (slot : Nat) (addr : Address) (s s' : ContractState) : Prop :=
  ∀ other : Address, other ≠ addr → s'.storageMap slot other = s.storageMap slot other

/-- All mapping entries at `slot` except `addr1` and `addr2` are unchanged. -/
def storageMapUnchangedExceptKeys (slot : Nat) (addr1 addr2 : Address) (s s' : ContractState) : Prop :=
  ∀ other : Address, other ≠ addr1 → other ≠ addr2 → s'.storageMap slot other = s.storageMap slot other

/-- Mapping storage is unchanged except at `slot` for key `addr`. -/
def storageMapUnchangedExceptKeyAtSlot (slot : Nat) (addr : Address) (s s' : ContractState) : Prop :=
  storageMapUnchangedExceptKey slot addr s s' ∧
  storageMapUnchangedExceptSlot slot s s'

/-- Mapping storage is unchanged except at `slot` for keys `addr1` and `addr2`. -/
def storageMapUnchangedExceptKeysAtSlot (slot : Nat) (addr1 addr2 : Address) (s s' : ContractState) : Prop :=
  storageMapUnchangedExceptKeys slot addr1 addr2 s s' ∧
  storageMapUnchangedExceptSlot slot s s'

/-- All double-mapping entries at `slot` are unchanged except possibly `(key1, key2)`. -/
def storageMap2UnchangedExceptKeyPair
    (slot : Nat) (key1 key2 : Address) (s s' : ContractState) : Prop :=
  (∀ k1' : Address, ∀ k2' : Address,
    k1' ≠ key1 → s'.storageMap2 slot k1' k2' = s.storageMap2 slot k1' k2') ∧
  (∀ k2' : Address,
    k2' ≠ key2 → s'.storageMap2 slot key1 k2' = s.storageMap2 slot key1 k2')

/-- Canonical two-state spec shape for updating one `storageMap` slot/key entry. -/
def storageMapUpdateSpec
    (slot : Nat)
    (key : Address)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap slot key = value s ∧
  storageMapUnchangedExceptKeyAtSlot slot key s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageMap` entry and one `storage` slot. -/
def storageMapAndStorageUpdateSpec
    (mapSlot : Nat)
    (key : Address)
    (mapValue : ContractState → Uint256)
    (storageSlot : Nat)
    (storageValue : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap mapSlot key = mapValue s ∧
  s'.storage storageSlot = storageValue s ∧
  storageMapUnchangedExceptKeyAtSlot mapSlot key s s' ∧
  storageUnchangedExcept storageSlot s s' ∧
  frame s s'

/-- Canonical two-state spec shape for updating one `storageMap2` slot/key pair. -/
def storageMap2UpdateSpec
    (slot : Nat)
    (key1 key2 : Address)
    (value : ContractState → Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  s'.storageMap2 slot key1 key2 = value s ∧
  storageMap2UnchangedExceptKeyPair slot key1 key2 s s' ∧
  frame s s'

/-- Canonical two-state spec shape for transfer-style updates on one mapping slot.
When `from == to`, balances are unchanged; otherwise `from` is debited and `to` is credited. -/
@[simp]
def storageMapTransferSpec
    (slot : Nat)
    (fromAddr to : Address)
    (amount : Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  (if fromAddr == to
    then s'.storageMap slot fromAddr = s.storageMap slot fromAddr
    else s'.storageMap slot fromAddr = sub (s.storageMap slot fromAddr) amount) ∧
  (if fromAddr == to
    then s'.storageMap slot to = s.storageMap slot to
    else s'.storageMap slot to = add (s.storageMap slot to) amount) ∧
  (if fromAddr == to
    then storageMapUnchangedExceptKeyAtSlot slot fromAddr s s'
    else storageMapUnchangedExceptKeysAtSlot slot fromAddr to s s') ∧
  frame s s'

/-- Canonical two-state spec shape for ERC20-style `transferFrom` updates.
When `from == to`, balances are unchanged; otherwise `from` is debited and `to` is credited.
Allowance stays at `MAX_UINT256` or decreases by `amount` and all other allowance pairs are unchanged. -/
@[simp]
def storageMapTransferFromSpec
    (balanceSlot allowanceSlot : Nat)
    (fromAddr to spender : Address)
    (amount : Uint256)
    (frame : ContractState → ContractState → Prop)
    (s s' : ContractState) : Prop :=
  (if fromAddr == to
    then s'.storageMap balanceSlot fromAddr = s.storageMap balanceSlot fromAddr
    else s'.storageMap balanceSlot fromAddr = sub (s.storageMap balanceSlot fromAddr) amount) ∧
  (if fromAddr == to
    then s'.storageMap balanceSlot to = s.storageMap balanceSlot to
    else s'.storageMap balanceSlot to = add (s.storageMap balanceSlot to) amount) ∧
  (if fromAddr == to
    then storageMapUnchangedExceptKeyAtSlot balanceSlot fromAddr s s'
    else storageMapUnchangedExceptKeysAtSlot balanceSlot fromAddr to s s') ∧
  (if s.storageMap2 allowanceSlot fromAddr spender == Verity.EVM.MAX_UINT256
    then s'.storageMap2 allowanceSlot fromAddr spender = Verity.EVM.MAX_UINT256
    else s'.storageMap2 allowanceSlot fromAddr spender =
      sub (s.storageMap2 allowanceSlot fromAddr spender) amount) ∧
  storageMap2UnchangedExceptKeyPair allowanceSlot fromAddr spender s s' ∧
  frame s s'

/-- All storage (uint256, addr, map, mapUint, map2, array) is unchanged. -/
def sameAllStorage (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameStorageArray s s'

@[simp] theorem sameAllStorage_rfl (s : ContractState) : sameAllStorage s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Everything except the event log is unchanged. -/
def sameExceptEvents (s s' : ContractState) : Prop :=
  sameAllStorage s s' ∧
  sameContext s s' ∧
  sameKnownAddresses s s'

@[simp] theorem sameExceptEvents_rfl (s : ContractState) : sameExceptEvents s s :=
  ⟨sameAllStorage_rfl s, sameContext_rfl s, rfl⟩

end Verity.Specs
