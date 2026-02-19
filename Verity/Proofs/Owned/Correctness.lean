/-
  Advanced correctness proofs for Owned contract.

  Proves deeper properties beyond Basic.lean:
  - Guard revert: transferOwnership reverts when caller is not the owner
  - Invariant preservation: transferOwnership preserves WellFormedState
  - End-to-end composition: constructor → transferOwnership → getOwner
-/

import Verity.Proofs.Owned.Basic

namespace Verity.Proofs.Owned.Correctness

open Verity
open Verity.Examples.Owned
open Verity.Specs.Owned
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne)
open Verity.Proofs.Owned

/-! ## Guard Revert Proof

The fundamental access control property: non-owners cannot transfer ownership.
-/

/-- transferOwnership reverts when the caller is not the owner.
    This is the core security property of the Owned pattern. -/
theorem transferOwnership_reverts_when_not_owner (s : ContractState) (newOwner : Address)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, (transferOwnership newOwner).run s = ContractResult.revert msg s := by
  simp [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    address_beq_false_of_ne s.sender (s.storageAddr 0) h_not_owner]

/-! ## Invariant Preservation -/

/-- transferOwnership preserves WellFormedState when the new owner is non-empty.
    After ownership transfer, all address fields remain non-empty. -/
theorem transferOwnership_preserves_wellformedness (s : ContractState) (newOwner : Address)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) (h_new : newOwner ≠ 0) :
  let s' := ((transferOwnership newOwner).run s).snd
  WellFormedState s' := by
  rw [transferOwnership_unfold s newOwner h_owner]; simp [ContractResult.snd]
  exact ⟨h_owner ▸ h.sender_nonzero, h.contract_nonzero, h_new⟩

/-! ## End-to-End Composition -/

/-- After constructor then transferOwnership, getOwner returns the new owner.
    Proves the full lifecycle: create → transfer → read. -/
theorem constructor_transferOwnership_getOwner (s : ContractState) (initialOwner newOwner : Address)
  (h_sender : s.sender = initialOwner) :
  let s1 := ((constructor initialOwner).run s).snd
  let s2 := ((transferOwnership newOwner).run s1).snd
  ((getOwner).run s2).fst = newOwner := by
  simp [constructor, transferOwnership, onlyOwner, isOwner, owner, getOwner,
    msgSender, getStorageAddr, setStorageAddr,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst, h_sender]

/-- After ownership transfer, the previous owner can no longer transfer.
    Proves that ownership is truly transferred, not just copied. -/
theorem transferred_owner_cannot_act (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) (h_ne : s.sender ≠ newOwner) :
  let s' := ((transferOwnership newOwner).run s).snd
  ∃ msg, (transferOwnership 42).run s' = ContractResult.revert msg s' := by
  have h_ne' : ((transferOwnership newOwner).run s).snd.sender ≠
      ((transferOwnership newOwner).run s).snd.storageAddr 0 := by
    rw [transferOwnership_unfold s newOwner h_owner]; simp [ContractResult.snd, h_ne]
  exact transferOwnership_reverts_when_not_owner _ _ h_ne'

/-! ## Summary

All 4 theorems fully proven with zero sorry:

1. transferOwnership_reverts_when_not_owner — core access control security
2. transferOwnership_preserves_wellformedness — invariant preservation
3. constructor_transferOwnership_getOwner — end-to-end lifecycle
4. transferred_owner_cannot_act — ownership is exclusively transferred
-/

end Verity.Proofs.Owned.Correctness
