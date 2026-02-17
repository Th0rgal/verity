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

/-- Uint256 storage is unchanged. -/
def sameStorage (s s' : ContractState) : Prop :=
  s'.storage = s.storage

/-- Address storage is unchanged. -/
def sameStorageAddr (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

/-- Mapping storage is unchanged. -/
def sameStorageMap (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

/-- Uint256-keyed mapping storage is unchanged. -/
def sameStorageMapUint (s s' : ContractState) : Prop :=
  s'.storageMapUint = s.storageMapUint

/-- Double mapping storage is unchanged. -/
def sameStorageMap2 (s s' : ContractState) : Prop :=
  s'.storageMap2 = s.storageMap2

/-- Address storage, mapping storage, and context are unchanged. -/
def sameAddrMapContext (s s' : ContractState) : Prop :=
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameContext s s'

/-- Uint256 storage, mapping storage, and context are unchanged. -/
def sameStorageMapContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageMap s s' ∧
  sameContext s s'

/-- Uint256 storage, address storage, and context are unchanged. -/
def sameStorageAddrContext (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameContext s s'

/-- All five storage types are unchanged (nothing about context).
    Use this when an operation only modifies context fields. -/
def sameAllStorage (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s'

/-- Everything except uint256 storage is unchanged.
    Use for operations that only modify `storage` slots. -/
def sameExceptStorage (s s' : ContractState) : Prop :=
  sameStorageAddr s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameContext s s'

/-- Everything except address storage is unchanged.
    Use for operations that only modify `storageAddr` slots. -/
def sameExceptStorageAddr (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageMap s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameContext s s'

/-- Everything except mapping storage is unchanged.
    Use for operations that only modify `storageMap` entries. -/
def sameExceptStorageMap (s s' : ContractState) : Prop :=
  sameStorage s s' ∧
  sameStorageAddr s s' ∧
  sameStorageMapUint s s' ∧
  sameStorageMap2 s s' ∧
  sameContext s s'

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

/-- All uint256-keyed mapping slots except `slot` are unchanged. -/
def storageMapUintUnchangedExceptSlot (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → ∀ key : Uint256, s'.storageMapUint other key = s.storageMapUint other key

/-- All uint256-keyed mapping entries at `slot` except `key` are unchanged. -/
def storageMapUintUnchangedExceptKey (slot : Nat) (key : Uint256) (s s' : ContractState) : Prop :=
  ∀ other : Uint256, other ≠ key → s'.storageMapUint slot other = s.storageMapUint slot other

/-- All double-mapping slots except `slot` are unchanged. -/
def storageMap2UnchangedExceptSlot (slot : Nat) (s s' : ContractState) : Prop :=
  ∀ other : Nat, other ≠ slot → ∀ a1 a2 : Address, s'.storageMap2 other a1 a2 = s.storageMap2 other a1 a2

end Verity.Specs
