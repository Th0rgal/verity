/-
  Correctness proofs for Ledger contract.

  Proves mapping-based balance operations:
  - deposit increases sender balance
  - withdraw decreases sender balance (guarded)
  - transfer moves between accounts (guarded, sender ≠ to, no overflow)
  - getBalance returns correct value
  - All operations preserve non-mapping storage
-/

import Contracts.Ledger.Spec
import Contracts.Ledger.Invariants
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Contracts.Ledger.Proofs

open Verity
open Contracts.Ledger
open Contracts.Ledger.Spec
open Verity.Stdlib.Math (MAX_UINT256)
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne uint256_ge_val_le)
open Contracts.Ledger.Invariants

/-! ## getBalance Correctness -/

theorem getBalance_meets_spec (s : ContractState) (addr : Address) :
  let result := ((getBalance addr).run s).fst
  getBalance_spec addr result s := by
  unfold getBalance
  simp [getBalance_spec, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, getMapping,
    balances]

theorem getBalance_returns_balance (s : ContractState) (addr : Address) :
  ((getBalance addr).run s).fst = s.storageMap 0 addr := by
  unfold getBalance
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, getMapping, balances]

theorem getBalance_preserves_state (s : ContractState) (addr : Address) :
  ((getBalance addr).run s).snd = s := by
  unfold getBalance
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, getMapping, balances]

/-! ## Deposit Correctness -/

/-- Helper: unfold deposit computation -/
private theorem deposit_unfold (s : ContractState) (amount : Uint256) :
  (deposit amount).run s = ContractResult.success ()
    { «storage» := s.storage,
      transientStorage := s.transientStorage,
      storageAddr := s.storageAddr,
      storageMap := fun slotIdx addr =>
        if (slotIdx == 0 && addr == s.sender) = true then EVM.Uint256.add (s.storageMap 0 s.sender) amount
        else s.storageMap slotIdx addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      storageArray := s.storageArray,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      blockNumber := s.blockNumber,
      chainId := s.chainId,
      blobBaseFee := s.blobBaseFee,
      calldataSize := s.calldataSize,
      calldata := s.calldata,
      memory := s.memory,
      knownAddresses := fun slotIdx =>
        if slotIdx == 0 then (s.knownAddresses slotIdx).insert s.sender
        else s.knownAddresses slotIdx,
      events := s.events } := by
  verity_unfold deposit
  simp only [balances]

theorem deposit_meets_spec (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  deposit_spec amount s s' := by
  rw [deposit_unfold]
  unfold deposit_spec Specs.storageMapUpdateSpec
  refine ⟨?_, ?_, ?_⟩
  · simp [ContractResult.snd, beq_iff_eq]
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [ContractResult.snd, beq_iff_eq, h_ne]
    · intro slotIdx h_ne addr
      simp [ContractResult.snd, beq_iff_eq, h_ne]
  · exact ⟨rfl, rfl, rfl, Specs.sameContext_rfl _⟩

theorem deposit_increases_balance (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.add (s.storageMap 0 s.sender) amount := by
  verity_frame deposit_unfold

theorem deposit_preserves_other_balances (s : ContractState) (amount : Uint256)
  (addr : Address) (h_ne : addr ≠ s.sender) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 addr = s.storageMap 0 addr := by
  verity_frame deposit_unfold with h_ne

/-! ## Withdraw Correctness -/

/-- Helper: unfold withdraw when balance is sufficient -/
private theorem withdraw_unfold (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  (withdraw amount).run s = ContractResult.success ()
    { «storage» := s.storage,
      transientStorage := s.transientStorage,
      storageAddr := s.storageAddr,
      storageMap := fun slotIdx addr =>
        if (slotIdx == 0 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 0 s.sender) amount
        else s.storageMap slotIdx addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      storageArray := s.storageArray,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      blockNumber := s.blockNumber,
      chainId := s.chainId,
      blobBaseFee := s.blobBaseFee,
      calldataSize := s.calldataSize,
      calldata := s.calldata,
      memory := s.memory,
      knownAddresses := fun slotIdx =>
        if slotIdx == 0 then (s.knownAddresses slotIdx).insert s.sender
        else s.knownAddresses slotIdx,
      events := s.events } := by
  verity_unfold withdraw
  simp [balances, h_balance]

theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  withdraw_spec amount s s' := by
  rw [withdraw_unfold s amount h_balance]
  unfold withdraw_spec Specs.storageMapUpdateSpec
  refine ⟨?_, ?_, ?_⟩
  · simp [ContractResult.snd, beq_iff_eq]
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [ContractResult.snd, beq_iff_eq, h_ne]
    · intro slotIdx h_ne addr
      simp [ContractResult.snd, beq_iff_eq, h_ne]
  · exact ⟨rfl, rfl, rfl, Specs.sameContext_rfl _⟩

theorem withdraw_decreases_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  verity_frame (withdraw_unfold s amount h_balance)

theorem withdraw_reverts_insufficient (s : ContractState) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (withdraw amount).run s = ContractResult.revert msg s := by
  simp [withdraw, msgSender, getMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Contract.run,
    show (s.storageMap 0 s.sender >= amount) = false from by
      simp [ge_iff_le] at h_insufficient ⊢; omega]

/-! ## Transfer Correctness -/

/-- Helper: unfold transfer when balance sufficient and sender == to (no-op). -/
private theorem transfer_unfold_self (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_eq : s.sender = to) :
  (transfer to amount).run s = ContractResult.success () s := by
  verity_unfold transfer
  simp [balances, Verity.pure, uint256_ge_val_le (h_eq ▸ h_balance), h_eq]

/-- Helper: unfold transfer when balance sufficient and sender ≠ to. -/
private theorem transfer_unfold_other (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  (transfer to amount).run s = ContractResult.success ()
    { «storage» := s.storage,
      transientStorage := s.transientStorage,
      storageAddr := s.storageAddr,
      storageMap := fun slotIdx addr =>
        if (slotIdx == 0 && addr == to) = true then EVM.Uint256.add (s.storageMap 0 to) amount
        else if (slotIdx == 0 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 0 s.sender) amount
        else s.storageMap slotIdx addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      storageArray := s.storageArray,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      blockNumber := s.blockNumber,
      chainId := s.chainId,
      blobBaseFee := s.blobBaseFee,
      calldataSize := s.calldataSize,
      calldata := s.calldata,
      memory := s.memory,
      knownAddresses := fun slotIdx =>
        if slotIdx == 0 then ((s.knownAddresses slotIdx).insert s.sender).insert to
        else s.knownAddresses slotIdx,
      events := s.events } := by
  simp only [transfer, Contracts.Ledger.balances,
    msgSender, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, h_balance, h_ne, beq_iff_eq,
    decide_eq_true_eq, ite_true, ite_false]
  congr 1
  congr 1
  funext slotIdx
  split <;> simp [*]

theorem transfer_meets_spec (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((transfer to amount).run s).snd
  transfer_spec to amount s s' := by
  by_cases h_eq : s.sender = to
  · rw [transfer_unfold_self s to amount h_balance h_eq]
    simp only [ContractResult.snd, transfer_spec]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h_eq]
    · simp [h_eq]
    · simp [h_eq, Specs.storageMapUnchangedExceptKeyAtSlot,
        Specs.storageMapUnchangedExceptKey, Specs.storageMapUnchangedExceptSlot]
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameStorageArray, Specs.sameContext]
  · rw [transfer_unfold_other s to amount h_balance h_eq]
    simp only [ContractResult.snd, transfer_spec]
    have h_ne' := address_beq_false_of_ne s.sender to h_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h_ne']
    · simp [h_ne']
    · simp [h_ne']
      refine ⟨?_, ?_⟩
      · intro addr h_ne_sender h_ne_to
        simp [h_ne_sender, h_ne_to]
      · intro slotIdx h_slot addr
        simp [h_slot]
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameStorageArray, Specs.sameContext]

theorem transfer_self_preserves_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((transfer s.sender amount).run s).snd
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender := by
  have h := transfer_meets_spec s s.sender amount h_balance
  simp [transfer_spec] at h
  exact h.1

theorem transfer_decreases_sender (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  have h := transfer_meets_spec s to amount h_balance
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  exact h.1

theorem transfer_increases_recipient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 to = EVM.Uint256.add (s.storageMap 0 to) amount := by
  have h := transfer_meets_spec s to amount h_balance
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  exact h.2.1

theorem transfer_reverts_insufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp [transfer, msgSender, getMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Contract.run,
    show (s.storageMap 0 s.sender >= amount) = false from by
      simp [ge_iff_le] at h_insufficient ⊢; omega]

-- Transfer does not revert on recipient overflow; Uint256 addition wraps.
theorem transfer_succeeds_recipient_overflow (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (_h_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) > MAX_UINT256) :
  ∃ s', (transfer to amount).run s = ContractResult.success () s' := by
  let s' : ContractState :=
    { «storage» := s.storage,
      transientStorage := s.transientStorage,
      storageAddr := s.storageAddr,
      storageMap := fun slotIdx addr =>
        if (slotIdx == 0 && addr == to) = true then EVM.Uint256.add (s.storageMap 0 to) amount
        else if (slotIdx == 0 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 0 s.sender) amount
        else s.storageMap slotIdx addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      storageArray := s.storageArray,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      blockNumber := s.blockNumber,
      chainId := s.chainId,
      blobBaseFee := s.blobBaseFee,
      calldataSize := s.calldataSize,
      calldata := s.calldata,
      memory := s.memory,
      knownAddresses := fun slotIdx =>
        if slotIdx == 0 then ((s.knownAddresses slotIdx).insert s.sender).insert to
        else s.knownAddresses slotIdx,
      events := s.events }
  refine ⟨s', ?_⟩
  simpa [s'] using transfer_unfold_other s to amount h_balance h_ne

/-! ## State Preservation -/

theorem deposit_preserves_non_mapping (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [deposit_unfold]
  simp [ContractResult.snd, non_mapping_storage_unchanged, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameStorageArray]

theorem withdraw_preserves_non_mapping (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [withdraw_unfold s amount h_balance]
  simp [ContractResult.snd, non_mapping_storage_unchanged, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameStorageArray]

theorem deposit_preserves_wellformedness (s : ContractState) (amount : Uint256)
  (h : WellFormedState s) :
  let s' := ((deposit amount).run s).snd
  WellFormedState s' := by
  rw [deposit_unfold]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero⟩

theorem withdraw_preserves_wellformedness (s : ContractState) (amount : Uint256)
  (h : WellFormedState s) (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  WellFormedState s' := by
  rw [withdraw_unfold s amount h_balance]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero⟩

/-! ## Composition: deposit → getBalance -/

theorem deposit_getBalance_correct (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.add (s.storageMap 0 s.sender) amount := by
  rw [deposit_unfold]
  unfold getBalance
  simp [ContractResult.snd, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    getMapping, balances]

/-! ## Summary of Proven Properties

All theorems fully proven with zero sorry and zero axioms:

Read operations:
1. getBalance_meets_spec
2. getBalance_returns_balance
3. getBalance_preserves_state

Deposit:
4. deposit_meets_spec
5. deposit_increases_balance
6. deposit_preserves_other_balances

Withdraw (guarded):
7. withdraw_meets_spec
8. withdraw_decreases_balance
9. withdraw_reverts_insufficient

Transfer (guarded, sender ≠ to):
10. transfer_meets_spec
11. transfer_decreases_sender
12. transfer_increases_recipient
13. transfer_reverts_insufficient
14. transfer_succeeds_recipient_overflow

State preservation:
15. deposit_preserves_non_mapping
16. withdraw_preserves_non_mapping
17. deposit_preserves_wellformedness
18. withdraw_preserves_wellformedness

Composition:
19. deposit_getBalance_correct
-/

end Contracts.Ledger.Proofs
