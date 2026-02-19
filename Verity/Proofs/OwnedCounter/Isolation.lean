/-
  Storage isolation proofs for OwnedCounter contract.

  Proves that counter operations and owner operations don't interfere:
  - increment/decrement preserve owner storage (count_preserves_owner)
  - transferOwnership preserves counter storage (owner_preserves_count)
  - All operations preserve mapping storage
  - All operations preserve context (sender, thisAddress)

  These connect the spec definitions in Invariants.lean to the
  actual contract behavior.
-/

import Verity.Proofs.OwnedCounter.Basic

namespace Verity.Proofs.OwnedCounter.Isolation

open Verity
open Verity.Examples.OwnedCounter
open Verity.Specs.OwnedCounter
open Verity.Proofs.OwnedCounter

/-! ## Counter operations preserve owner storage (count_preserves_owner)

These prove that increment and decrement don't touch the owner address
storage, using the count_preserves_owner spec definition.
-/

/-- Increment preserves all address storage (including owner). -/
theorem increment_count_preserves_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  count_preserves_owner s (increment.run s).snd := by
  unfold count_preserves_owner
  exact increment_preserves_owner s h_owner

/-- Decrement preserves all address storage (including owner). -/
theorem decrement_count_preserves_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  count_preserves_owner s (decrement.run s).snd := by
  unfold count_preserves_owner
  exact decrement_preserves_owner s h_owner

/-- Constructor preserves counter storage. -/
theorem constructor_owner_preserves_count (s : ContractState) (initialOwner : Address) :
  owner_preserves_count s ((constructor initialOwner).run s).snd := by
  unfold owner_preserves_count
  exact constructor_preserves_count s initialOwner

/-! ## Owner operations preserve counter storage (owner_preserves_count)

TransferOwnership doesn't touch the counter value.
-/

/-- TransferOwnership preserves all uint256 storage (including count). -/
theorem transferOwnership_owner_preserves_count (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  owner_preserves_count s ((transferOwnership newOwner).run s).snd := by
  unfold owner_preserves_count
  exact transferOwnership_preserves_count s newOwner h_owner

/-! ## Context preservation

All successful operations preserve sender and thisAddress.
-/

/-- Constructor preserves context. -/
theorem constructor_context_preserved (s : ContractState) (initialOwner : Address) :
  context_preserved s ((constructor initialOwner).run s).snd := by
  simp [context_preserved, Specs.sameContext, constructor, setStorageAddr, owner, Contract.run, ContractResult.snd]

/-- Increment preserves context (when authorized). -/
theorem increment_context_preserved (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  context_preserved s (increment.run s).snd := by
  unfold context_preserved Specs.sameContext
  rw [increment_unfold s h_owner]; simp [ContractResult.snd]

/-- Decrement preserves context (when authorized). -/
theorem decrement_context_preserved (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  context_preserved s (decrement.run s).snd := by
  unfold context_preserved Specs.sameContext
  rw [decrement_unfold s h_owner]; simp [ContractResult.snd]

/-- TransferOwnership preserves context (when authorized). -/
theorem transferOwnership_context_preserved (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  context_preserved s ((transferOwnership newOwner).run s).snd := by
  unfold context_preserved Specs.sameContext
  rw [transferOwnership_unfold s newOwner h_owner]; simp [ContractResult.snd]

/-- getCount preserves context. -/
theorem getCount_context_preserved (s : ContractState) :
  context_preserved s (getCount.run s).snd := by
  simp [context_preserved, Specs.sameContext, getCount, getStorage, count, Contract.run, ContractResult.snd]

/-- getOwner preserves context. -/
theorem getOwner_context_preserved (s : ContractState) :
  context_preserved s (getOwner.run s).snd := by
  simp [context_preserved, Specs.sameContext, getOwner, getStorageAddr, owner, Contract.run, ContractResult.snd]

/-! ## Mapping storage isolation

All OwnedCounter operations preserve mapping storage (the contract
doesn't use mappings at all).
-/

/-- Constructor preserves mapping storage. -/
theorem constructor_preserves_map_storage (s : ContractState) (initialOwner : Address) :
  ((constructor initialOwner).run s).snd.storageMap = s.storageMap := by
  simp [constructor, setStorageAddr, owner, Contract.run, ContractResult.snd]

/-- Increment preserves mapping storage. -/
theorem increment_preserves_map_storage (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  (increment.run s).snd.storageMap = s.storageMap := by
  rw [increment_unfold s h_owner]; simp [ContractResult.snd]

/-- Decrement preserves mapping storage. -/
theorem decrement_preserves_map_storage (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  (decrement.run s).snd.storageMap = s.storageMap := by
  rw [decrement_unfold s h_owner]; simp [ContractResult.snd]

/-- TransferOwnership preserves mapping storage. -/
theorem transferOwnership_preserves_map_storage (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  ((transferOwnership newOwner).run s).snd.storageMap = s.storageMap := by
  rw [transferOwnership_unfold s newOwner h_owner]; simp [ContractResult.snd]

/-! ## Summary

All 14 theorems fully proven with zero sorry:

count_preserves_owner (counter ops don't touch owner):
1. increment_count_preserves_owner
2. decrement_count_preserves_owner

owner_preserves_count (owner ops don't touch counter):
3. constructor_owner_preserves_count
4. transferOwnership_owner_preserves_count

context_preserved (sender/thisAddress unchanged):
5. constructor_context_preserved
6. increment_context_preserved
7. decrement_context_preserved
8. transferOwnership_context_preserved
9. getCount_context_preserved
10. getOwner_context_preserved

Mapping storage isolation:
11. constructor_preserves_map_storage
12. increment_preserves_map_storage
13. decrement_preserves_map_storage
14. transferOwnership_preserves_map_storage
-/

end Verity.Proofs.OwnedCounter.Isolation
