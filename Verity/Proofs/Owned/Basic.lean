/-
  Basic correctness proofs for Owned contract.

  Proves that Owned operations satisfy their specifications.

  Note: Properties involving require/onlyOwner are partially proven
  due to require behavior not being fully modeled in the EDSL.
-/

import Verity.Specs.Owned.Spec
import Verity.Specs.Owned.Invariants
import Verity.Proofs.Stdlib.Automation

namespace Verity.Proofs.Owned

open Verity
open Verity.Examples.Owned
open Verity.Specs.Owned
open Verity.Proofs.Stdlib.Automation (wf_of_state_eq)

/-! ## Basic Lemmas about setStorageAddr and getStorageAddr

These establish fundamental properties of address storage operations.
-/

theorem setStorageAddr_updates_owner (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.storageAddr 0 = addr := by
  simp [setStorageAddr, owner]

theorem getStorageAddr_reads_owner (s : ContractState) :
  let slot : StorageSlot Address := owner
  let result := ((getStorageAddr slot).run s).fst
  result = s.storageAddr 0 := by
  simp [getStorageAddr, owner]

theorem setStorageAddr_preserves_other_slots (s : ContractState) (addr : Address) (slot_num : Nat)
  (h : slot_num ≠ 0) :
  let slot : StorageSlot Address := owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.storageAddr slot_num = s.storageAddr slot_num := by
  simp [setStorageAddr, owner, h]

theorem setStorageAddr_preserves_uint_storage (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.storage = s.storage := by
  simp [setStorageAddr, owner]

theorem setStorageAddr_preserves_map_storage (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.storageMap = s.storageMap := by
  simp [setStorageAddr, owner]

theorem setStorageAddr_preserves_context (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.sender = s.sender ∧ s'.thisAddress = s.thisAddress := by
  simp [setStorageAddr, owner]

/-! ## constructor Correctness -/

theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  constructor_spec initialOwner s s' := by
  simp [constructor, constructor_spec, owner, Specs.sameStorageMapContext,
    Specs.sameStorage, Specs.sameStorageMap, Specs.sameContext]
  intro slot h_neq
  simp [setStorageAddr, owner, h_neq]

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  s'.storageAddr 0 = initialOwner := by
  have h := constructor_meets_spec s initialOwner; simp [constructor_spec] at h; exact h.1

/-! ## getOwner Correctness -/

theorem getOwner_meets_spec (s : ContractState) :
  let result := ((getOwner).run s).fst
  getOwner_spec result s := by
  simp [getOwner, getOwner_spec, owner]

theorem getOwner_returns_owner (s : ContractState) :
  let result := ((getOwner).run s).fst
  result = s.storageAddr 0 := by
  simpa [getOwner_spec] using getOwner_meets_spec s

theorem getOwner_preserves_state (s : ContractState) :
  let s' := ((getOwner).run s).snd
  s' = s := by
  simp [getOwner, getStorageAddr, owner]

/-! ## isOwner Correctness -/

theorem isOwner_meets_spec (s : ContractState) :
  let result := ((isOwner).run s).fst
  isOwner_spec result s := by
  simp only [isOwner, isOwner_spec, msgSender, getStorageAddr, owner, bind, Bind.bind, Contract.run, pure, ContractResult.fst]
  rfl

theorem isOwner_returns_correct_value (s : ContractState) :
  let result := ((isOwner).run s).fst
  result = (s.sender == s.storageAddr 0) := by
  simpa [isOwner_spec] using isOwner_meets_spec s

/-! ## transferOwnership Correctness

These proofs show that when the caller is the current owner,
transferOwnership correctly updates the owner address.
The key insight: with ContractResult, require/onlyOwner behavior
is fully modeled and can be unfolded in proofs.
-/

/-- Helper: unfold transferOwnership when caller is owner -/
theorem transferOwnership_unfold (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) :
  (transferOwnership newOwner).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := fun slot => if (slot == 0) = true then newOwner else s.storageAddr slot,
      storageMap := s.storageMap,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := s.knownAddresses,
      events := s.events } := by
  simp [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst, h_owner]

theorem transferOwnership_meets_spec_when_owner (s : ContractState) (newOwner : Address)
  (h_is_owner : s.sender = s.storageAddr 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  transferOwnership_spec newOwner s s' := by
  rw [transferOwnership_unfold s newOwner h_is_owner]
  simp [transferOwnership_spec, ContractResult.snd, Specs.sameStorageMapContext,
    Specs.sameStorage, Specs.sameStorageMap, Specs.sameContext]
  intro slot h_neq
  simp [beq_iff_eq, h_neq]

theorem transferOwnership_changes_owner_when_allowed (s : ContractState) (newOwner : Address)
  (h_is_owner : s.sender = s.storageAddr 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  s'.storageAddr 0 = newOwner := by
  rw [transferOwnership_unfold s newOwner h_is_owner]
  simp [ContractResult.snd]

/-! ## Composition Properties -/

theorem constructor_getOwner_correct (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  let result := ((getOwner).run s').fst
  result = initialOwner := by
  have h_constr := constructor_sets_owner s initialOwner
  simpa only [h_constr] using getOwner_returns_owner (((constructor initialOwner).run s).snd)

/-! ## State Preservation -/

theorem constructor_preserves_wellformedness (s : ContractState) (initialOwner : Address)
  (h : WellFormedState s) (h_owner : initialOwner ≠ 0) :
  let s' := ((constructor initialOwner).run s).snd
  WellFormedState s' := by
  have h_spec := constructor_meets_spec s initialOwner
  rcases h_spec with ⟨h_owner_set, _h_other_addr, h_same⟩
  rcases h_same with ⟨_h_storage, _h_map, h_ctx⟩
  have h_sender := h_ctx.1
  have h_this := h_ctx.2.1
  exact ⟨h_sender ▸ h.sender_nonzero, h_this ▸ h.contract_nonzero, h_owner_set ▸ h_owner⟩

theorem getOwner_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getOwner).run s).snd
  WellFormedState s' :=
  wf_of_state_eq _ _ _ (getOwner_preserves_state s) h

/-! ## Summary of Proven Properties

All 18 theorems fully proven with zero sorry and zero axioms:

1. setStorageAddr_updates_owner
2. getStorageAddr_reads_owner
3. setStorageAddr_preserves_other_slots
4. setStorageAddr_preserves_uint_storage
5. setStorageAddr_preserves_map_storage
6. setStorageAddr_preserves_context
7. constructor_meets_spec
8. constructor_sets_owner
9. getOwner_meets_spec
10. getOwner_returns_owner
11. getOwner_preserves_state
12. isOwner_meets_spec
13. isOwner_returns_correct_value
14. transferOwnership_meets_spec_when_owner ✅ (guard fully modeled)
15. transferOwnership_changes_owner_when_allowed ✅ (guard fully modeled)
16. constructor_getOwner_correct
17. constructor_preserves_wellformedness
18. getOwner_preserves_wellformedness
-/

end Verity.Proofs.Owned
