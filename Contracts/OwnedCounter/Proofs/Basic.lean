/-
  Correctness proofs for OwnedCounter contract.

  Proves that the composition of Owned + Counter patterns is correct:
  - Constructor sets owner without touching counter
  - Owner-guarded increment/decrement work when authorized
  - Non-owner calls revert
  - Ownership and counter storage are independent
  - State preservation and well-formedness
-/

import Contracts.OwnedCounter.Spec
import Contracts.OwnedCounter.Invariants
import Verity.Proofs.Stdlib.Automation

namespace Contracts.OwnedCounter.Proofs

open Verity
open Contracts.MacroContracts.OwnedCounter
open Contracts.OwnedCounter.Spec
open Verity.Proofs.Stdlib.Automation
open Contracts.OwnedCounter.Invariants

/-! ## Owner Guard -/

private theorem onlyOwner_reverts (s : ContractState) (h : s.sender ≠ s.storageAddr 0) :
    onlyOwner s = ContractResult.revert "Caller is not the owner" s := by
  simp [onlyOwner, isOwner, owner, msgSender, getStorageAddr,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    address_beq_false_of_ne s.sender (s.storageAddr 0) h]

private theorem guarded_reverts (f : Unit → Contract α) (s : ContractState)
    (h : s.sender ≠ s.storageAddr 0) :
    ∃ msg, (Verity.bind onlyOwner f).run s = ContractResult.revert msg s :=
  ⟨"Caller is not the owner", by simp [Verity.bind, Contract.run, onlyOwner_reverts s h]⟩

/-! ## Constructor Correctness -/

theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
  let s' := ((setStorageAddr owner initialOwner).run s).snd
  constructor_spec initialOwner s s' := by
  simp [setStorageAddr, owner, constructor_spec, Contract.run, ContractResult.snd,
    Specs.sameStorageMapContext, Specs.sameStorage, Specs.sameStorageMap, Specs.sameContext]
  intro slotIdx h_neq
  simp [h_neq]

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
  let s' := ((setStorageAddr owner initialOwner).run s).snd
  s'.storageAddr 0 = initialOwner := by
  simp [setStorageAddr, owner, Contract.run, ContractResult.snd]

theorem constructor_preserves_count (s : ContractState) (initialOwner : Address) :
  let s' := ((setStorageAddr owner initialOwner).run s).snd
  s'.storage = s.storage := by
  simp [setStorageAddr, owner, Contract.run, ContractResult.snd]

/-! ## Read Operation Correctness -/

private theorem getCount_run (s : ContractState) :
  (getCount).run s = ContractResult.success (s.storage 1) s := by
  simp [getCount, count, getStorage, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run]

theorem getCount_meets_spec (s : ContractState) :
  let result := ((getCount).run s).fst
  getCount_spec result s := by
  rw [getCount_run s]
  simp [getCount_spec]

theorem getCount_returns_count (s : ContractState) :
  ((getCount).run s).fst = s.storage 1 := by
  rw [getCount_run s]
  simp

theorem getCount_preserves_state (s : ContractState) :
  ((getCount).run s).snd = s := by
  rw [getCount_run s]
  simp

private theorem getOwner_run (s : ContractState) :
  (getOwner).run s = ContractResult.success (s.storageAddr 0) s := by
  simp [getOwner, owner, getStorageAddr, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run]

theorem getOwner_meets_spec (s : ContractState) :
  let result := ((getOwner).run s).fst
  getOwner_spec result s := by
  rw [getOwner_run s]
  simp [getOwner_spec]

theorem getOwner_returns_owner (s : ContractState) :
  ((getOwner).run s).fst = s.storageAddr 0 := by
  rw [getOwner_run s]
  simp

theorem getOwner_preserves_state (s : ContractState) :
  ((getOwner).run s).snd = s := by
  rw [getOwner_run s]
  simp

/-! ## isOwner Correctness -/

theorem isOwner_correct (s : ContractState) :
  ((isOwner).run s).fst = (s.sender == s.storageAddr 0) := by
  verity_unfold isOwner
  simp [owner]

/-! ## Increment Correctness (Owner-Guarded) -/

/-- Helper: unfold increment when caller is owner -/
theorem increment_unfold (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  (increment.run s) = ContractResult.success ()
    { «storage» := fun slotIdx => if (slotIdx == 1) = true then EVM.Uint256.add (s.storage 1) 1 else s.storage slotIdx,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  verity_unfold increment
  simp [owner, count, h_owner]

theorem increment_meets_spec_when_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (increment.run s).snd
  increment_spec s s' := by
  rw [increment_unfold s h_owner]
  simp [increment_spec, ContractResult.snd, Specs.sameAddrMapContext,
    Specs.sameContext, Specs.sameStorageAddr, Specs.sameStorageMap]
  intro slotIdx h_neq
  simp [h_neq]

theorem increment_adds_one_when_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (increment.run s).snd
  s'.storage 1 = EVM.Uint256.add (s.storage 1) 1 := by
  rw [increment_unfold s h_owner]
  simp [ContractResult.snd]

theorem increment_reverts_when_not_owner (s : ContractState)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, increment.run s = ContractResult.revert msg s := by
  unfold increment; exact guarded_reverts _ s h_not_owner

/-! ## Decrement Correctness (Owner-Guarded) -/

/-- Helper: unfold decrement when caller is owner -/
theorem decrement_unfold (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  (decrement.run s) = ContractResult.success ()
    { «storage» := fun slotIdx => if (slotIdx == 1) = true then EVM.Uint256.sub (s.storage 1) 1 else s.storage slotIdx,
      storageAddr := s.storageAddr,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  verity_unfold decrement
  simp [owner, count, h_owner]

theorem decrement_meets_spec_when_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (decrement.run s).snd
  decrement_spec s s' := by
  rw [decrement_unfold s h_owner]
  simp [decrement_spec, ContractResult.snd, Specs.sameAddrMapContext,
    Specs.sameContext, Specs.sameStorageAddr, Specs.sameStorageMap]
  intro slotIdx h_neq
  simp [h_neq]

theorem decrement_subtracts_one_when_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (decrement.run s).snd
  s'.storage 1 = EVM.Uint256.sub (s.storage 1) 1 := by
  rw [decrement_unfold s h_owner]
  simp [ContractResult.snd]

theorem decrement_reverts_when_not_owner (s : ContractState)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, decrement.run s = ContractResult.revert msg s := by
  unfold decrement; exact guarded_reverts _ s h_not_owner

/-! ## TransferOwnership Correctness (Owner-Guarded) -/

theorem transferOwnership_unfold (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  (transferOwnership newOwner).run s = ContractResult.success ()
    { «storage» := s.storage,
      storageAddr := fun slotIdx => if (slotIdx == 0) = true then newOwner else s.storageAddr slotIdx,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  verity_unfold transferOwnership
  simp [owner, h_owner]

theorem transferOwnership_meets_spec_when_owner (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  transferOwnership_spec newOwner s s' := by
  rw [transferOwnership_unfold s newOwner h_owner]
  simp [transferOwnership_spec, ContractResult.snd, Specs.sameStorageMapContext,
    Specs.sameStorage, Specs.sameStorageMap, Specs.sameContext]
  intro slotIdx h_neq
  simp [h_neq]

theorem transferOwnership_changes_owner (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  s'.storageAddr 0 = newOwner := by
  rw [transferOwnership_unfold s newOwner h_owner]
  simp [ContractResult.snd]

theorem transferOwnership_reverts_when_not_owner (s : ContractState) (newOwner : Address)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, (transferOwnership newOwner).run s = ContractResult.revert msg s := by
  unfold transferOwnership; exact guarded_reverts _ s h_not_owner

/-! ## Composition Properties — The Key Results

These prove that ownership and counter storage are independent:
increment/decrement don't touch the owner, and transferOwnership doesn't touch the count.
-/

theorem increment_preserves_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (increment.run s).snd
  s'.storageAddr = s.storageAddr := by
  rw [increment_unfold s h_owner]
  simp [ContractResult.snd]

theorem decrement_preserves_owner (s : ContractState)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := (decrement.run s).snd
  s'.storageAddr = s.storageAddr := by
  rw [decrement_unfold s h_owner]
  simp [ContractResult.snd]

theorem transferOwnership_preserves_count (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  s'.storage = s.storage := by
  rw [transferOwnership_unfold s newOwner h_owner]
  simp [ContractResult.snd]

/-! ## Well-Formedness Preservation -/

theorem constructor_preserves_wellformedness (s : ContractState) (initialOwner : Address)
  (h : WellFormedState s) (h_owner : initialOwner ≠ 0) :
  let s' := ((setStorageAddr owner initialOwner).run s).snd
  WellFormedState s' := by
  have h_spec := constructor_meets_spec s initialOwner
  rcases h_spec with ⟨h_set, _h_other_addr, h_same⟩
  rcases h_same with ⟨_h_storage, _h_map, h_ctx⟩
  exact ⟨h_ctx.1 ▸ h.sender_nonzero, h_ctx.2.1 ▸ h.contract_nonzero, h_set ▸ h_owner⟩

theorem increment_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) :
  let s' := (increment.run s).snd
  WellFormedState s' := by
  rw [increment_unfold s h_owner]; simp [ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero, h.owner_nonzero⟩

theorem decrement_preserves_wellformedness (s : ContractState)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) :
  let s' := (decrement.run s).snd
  WellFormedState s' := by
  rw [decrement_unfold s h_owner]; simp [ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero, h.owner_nonzero⟩

/-! ## Composition Sequence: constructor → increment → getCount -/

theorem constructor_increment_getCount (s : ContractState) (initialOwner : Address)
  (h_sender : s.sender = initialOwner) :
  let s1 := ((setStorageAddr owner initialOwner).run s).snd
  let s2 := (increment.run s1).snd
  (getCount.run s2).fst = EVM.Uint256.add (s.storage 1) 1 := by
  -- Fully unfold constructor → increment → getCount in one go
  simp only [setStorageAddr, increment, onlyOwner, isOwner, owner, count,
    getCount, getStorage, getStorageAddr, setStorage, setStorageAddr,
    msgSender, Verity.require, Verity.pure, Verity.bind,
    Bind.bind, Pure.pure, Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_sender]

/-! ## Summary of Proven Properties

All theorems fully proven with zero sorry and zero axioms:

Constructor:
1. constructor_meets_spec
2. constructor_sets_owner
3. constructor_preserves_count

Read operations:
4. getCount_meets_spec
5. getCount_returns_count
6. getCount_preserves_state
7. getOwner_meets_spec
8. getOwner_returns_owner
9. getOwner_preserves_state
10. isOwner_correct

Increment (owner-guarded):
11. increment_meets_spec_when_owner
12. increment_adds_one_when_owner
13. increment_reverts_when_not_owner

Decrement (owner-guarded):
14. decrement_meets_spec_when_owner
15. decrement_subtracts_one_when_owner
16. decrement_reverts_when_not_owner

Transfer ownership (owner-guarded):
17. transferOwnership_meets_spec_when_owner
18. transferOwnership_changes_owner
19. transferOwnership_reverts_when_not_owner

Composition / isolation:
20. increment_preserves_owner
21. decrement_preserves_owner
22. transferOwnership_preserves_count

Well-formedness:
23. constructor_preserves_wellformedness
24. increment_preserves_wellformedness
25. decrement_preserves_wellformedness

Composition sequence:
26. constructor_increment_getCount
-/

end Contracts.OwnedCounter.Proofs
