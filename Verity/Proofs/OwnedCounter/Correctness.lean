/-
  Advanced correctness proofs for OwnedCounter contract.

  Proves deeper properties beyond Basic.lean:
  - Cross-operation guard interaction: after ownership transfer, old owner is locked out
  - Invariant preservation: transferOwnership preserves WellFormedState
  - End-to-end: constructor → increment → getCount → transferOwnership → verify lockout
-/

import Verity.Core
import Verity.Examples.OwnedCounter
import Verity.EVM.Uint256
import Verity.Specs.OwnedCounter.Spec
import Verity.Specs.OwnedCounter.Invariants
import Verity.Proofs.OwnedCounter.Basic

namespace Verity.Proofs.OwnedCounter.Correctness

open Verity
open Verity.Examples.OwnedCounter
open Verity.Specs.OwnedCounter
open Verity.Proofs.OwnedCounter

/-! ## Cross-Operation Guard Interaction

The critical property for composed contracts: after transferring ownership
to a different address, the original owner can no longer increment, decrement,
or transfer ownership again. This tests that the onlyOwner guard correctly
reads the updated owner from storage, not a stale value.
-/

/-- After transferring ownership, the old owner cannot increment.
    The guard correctly reads the new owner from storage and rejects. -/
theorem transfer_then_increment_reverts (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0)
  (h_ne : s.sender ≠ newOwner) :
  let s' := ((transferOwnership newOwner).run s).snd
  ∃ msg, increment.run s' = ContractResult.revert msg s' := by
  simp only [transferOwnership, increment, onlyOwner, isOwner, owner, count,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_ne2 : s.storageAddr 0 ≠ newOwner := h_owner ▸ h_ne
  simp [h_owner, h_ne2]

/-- After transferring ownership, the old owner cannot decrement. -/
theorem transfer_then_decrement_reverts (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0)
  (h_ne : s.sender ≠ newOwner) :
  let s' := ((transferOwnership newOwner).run s).snd
  ∃ msg, decrement.run s' = ContractResult.revert msg s' := by
  simp only [transferOwnership, decrement, onlyOwner, isOwner, owner, count,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_ne2 : s.storageAddr 0 ≠ newOwner := h_owner ▸ h_ne
  simp [h_owner, h_ne2]

/-- After transferring ownership, the old owner cannot transfer again. -/
theorem transfer_then_transfer_reverts (s : ContractState) (newOwner : Address)
  (h_owner : s.sender = s.storageAddr 0)
  (h_ne : s.sender ≠ newOwner) :
  let s' := ((transferOwnership newOwner).run s).snd
  ∃ msg, (transferOwnership "anyone").run s' = ContractResult.revert msg s' := by
  simp only [transferOwnership, onlyOwner, isOwner, owner,
    msgSender, getStorageAddr, setStorageAddr,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_ne2 : s.storageAddr 0 ≠ newOwner := h_owner ▸ h_ne
  simp [h_owner, h_ne2]

/-! ## Invariant Preservation -/

/-- transferOwnership preserves WellFormedState when new owner is non-empty. -/
theorem transferOwnership_preserves_wellformedness (s : ContractState) (newOwner : Address)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) (h_new : newOwner ≠ "") :
  let s' := ((transferOwnership newOwner).run s).snd
  WellFormedState s' := by
  rw [transferOwnership_unfold s newOwner h_owner]; simp [ContractResult.snd]
  exact ⟨h_owner ▸ h.sender_nonempty, h.contract_nonempty, h_new⟩

/-! ## Ownership Transfer Preserves Counter Value

After transferring ownership, the counter value is untouched.
This is the isolation guarantee for composed patterns.
-/

/-- Full sequence: construct → increment → transferOwnership → getCount.
    The counter value survives ownership transfer. -/
theorem increment_survives_transfer (s : ContractState) (initialOwner newOwner : Address)
  (h_sender : s.sender = initialOwner) :
  let s1 := ((constructor initialOwner).run s).snd
  let s2 := (increment.run s1).snd
  let s3 := ((transferOwnership newOwner).run s2).snd
  (getCount.run s3).fst = EVM.Uint256.add (s.storage 1) 1 := by
  simp only [constructor, increment, transferOwnership, onlyOwner, isOwner, owner, count,
    getCount, getStorage, getStorageAddr, setStorage, setStorageAddr,
    msgSender, Verity.require, Verity.pure, Verity.bind,
    Bind.bind, Pure.pure, Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_sender]

/-! ## Summary

All 5 theorems fully proven with zero sorry:

Cross-operation guard interaction:
1. transfer_then_increment_reverts — old owner locked out of increment
2. transfer_then_decrement_reverts — old owner locked out of decrement
3. transfer_then_transfer_reverts — old owner locked out of re-transfer

Invariant preservation:
4. transferOwnership_preserves_wellformedness

Composition / isolation:
5. increment_survives_transfer — counter value survives ownership transfer
-/

end Verity.Proofs.OwnedCounter.Correctness
