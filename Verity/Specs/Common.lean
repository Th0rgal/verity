/-
  Shared helpers for specs.

  Keep specs human-friendly by naming the common "unchanged" clauses
  instead of repeating field-by-field equality.
-/

import Verity.Core

namespace Verity.Specs

open Verity

/-- Contract context (sender, address, msg value, timestamp) is unchanged. -/
def sameContext (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

@[simp] theorem sameContext_rfl (s : ContractState) : sameContext s s :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Uint256 storage is unchanged. -/
def sameStorage (s s' : ContractState) : Prop :=
  s'.storage = s.storage

@[simp] theorem sameStorage_rfl (s : ContractState) : sameStorage s s := rfl

/-- Address storage is unchanged. -/
def sameStorageAddr (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

@[simp] theorem sameStorageAddr_rfl (s : ContractState) : sameStorageAddr s s := rfl

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
  sameContext s s'

@[simp] theorem sameAddrMapContext_rfl (s : ContractState) : sameAddrMapContext s s :=
  ⟨rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, mapping storage, and context are unchanged. -/
def sameStorageMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageMap s s' ∧
  sameContext s s'

@[simp] theorem sameStorageMapContext_rfl (s : ContractState) : sameStorageMapContext s s :=
  ⟨rfl, rfl, sameContext_rfl s⟩

/-- Uint256 storage, address storage, and context are unchanged. -/
def sameStorageAddrContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameContext s s'

@[simp] theorem sameStorageAddrContext_rfl (s : ContractState) : sameStorageAddrContext s s :=
  ⟨rfl, rfl, sameContext_rfl s⟩

/-- All storage slots except `slot` are unchanged. -/
def storageUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storage other = s.storage other

/-- All address storage slots except `slot` are unchanged. -/
def storageAddrUnchangedExcept (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → s'.storageAddr other = s.storageAddr other

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

/-- All storage (uint256, addr, map, mapUint, map2) is unchanged. -/
def sameAllStorage (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s'

@[simp] theorem sameAllStorage_rfl (s : ContractState) : sameAllStorage s s :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Everything except the event log is unchanged. -/
def sameExceptEvents (s s' : ContractState) : Prop :=
  sameAllStorage s s' ∧
  sameContext s s' ∧
  sameKnownAddresses s s'

@[simp] theorem sameExceptEvents_rfl (s : ContractState) : sameExceptEvents s s :=
  ⟨sameAllStorage_rfl s, sameContext_rfl s, rfl⟩

end Verity.Specs
