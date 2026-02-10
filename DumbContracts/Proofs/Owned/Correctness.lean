/-
  Advanced correctness proofs for Owned contract.

  Proves deeper properties beyond Basic.lean:
  - Guard revert: transferOwnership reverts when caller is not the owner
  - Invariant preservation: transferOwnership preserves WellFormedState
  - End-to-end composition: constructor → transferOwnership → getOwner
-/

import DumbContracts.Core
import DumbContracts.Examples.Owned
import DumbContracts.Specs.Owned.Spec
import DumbContracts.Specs.Owned.Invariants
import DumbContracts.Proofs.Owned.Basic

namespace DumbContracts.Proofs.Owned.Correctness

open DumbContracts
open DumbContracts.Examples.Owned
open DumbContracts.Specs.Owned
open DumbContracts.Proofs.Owned

/-! ## Guard Revert Proof

The fundamental access control property: non-owners cannot transfer ownership.
-/

/-- transferOwnership reverts when the caller is not the owner.
    This is the core security property of the Owned pattern. -/
theorem transferOwnership_reverts_when_not_owner (s : ContractState) (newOwner : Address)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, (transferOwnership newOwner).run s = ContractResult.revert msg s := by
  simp only [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h : (s.sender == s.storageAddr 0) = false := by
    simp [beq_iff_eq]; exact h_not_owner
  simp [h]

/-! ## Invariant Preservation -/

/-- transferOwnership preserves WellFormedState when the new owner is non-empty.
    After ownership transfer, all address fields remain non-empty. -/
theorem transferOwnership_preserves_wellformedness (s : ContractState) (newOwner : Address)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) (h_new : newOwner ≠ "") :
  let s' := ((transferOwnership newOwner).run s).snd
  WellFormedState s' := by
  simp only [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_owner]
  constructor
  · exact h_owner ▸ h.sender_nonempty
  · exact h.contract_nonempty
  · exact h_new

/-! ## End-to-End Composition -/

/-- After constructor then transferOwnership, getOwner returns the new owner.
    Proves the full lifecycle: create → transfer → read. -/
theorem constructor_transferOwnership_getOwner (s : ContractState) (initialOwner newOwner : Address)
  (h_sender : s.sender = initialOwner) :
  let s1 := ((constructor initialOwner).run s).snd
  let s2 := ((transferOwnership newOwner).run s1).snd
  ((getOwner).run s2).fst = newOwner := by
  simp only [constructor, transferOwnership, onlyOwner, isOwner, owner, getOwner,
    msgSender, getStorageAddr, setStorageAddr,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_sender]

/-- After ownership transfer, the previous owner can no longer transfer.
    Proves that ownership is truly transferred, not just copied. -/
theorem transferred_owner_cannot_act (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0) (h_ne : s.sender ≠ newOwner) :
  let s' := ((transferOwnership newOwner).run s).snd
  ∃ msg, (transferOwnership "anyone").run s' = ContractResult.revert msg s' := by
  simp only [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_ne2 : s.storageAddr 0 ≠ newOwner := h_owner ▸ h_ne
  simp [h_owner, h_ne2]

/-! ## Summary

All 4 theorems fully proven with zero sorry:

1. transferOwnership_reverts_when_not_owner — core access control security
2. transferOwnership_preserves_wellformedness — invariant preservation
3. constructor_transferOwnership_getOwner — end-to-end lifecycle
4. transferred_owner_cannot_act — ownership is exclusively transferred
-/

end DumbContracts.Proofs.Owned.Correctness
