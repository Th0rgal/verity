/-
  Correctness proofs for Ledger contract.

  Proves mapping-based balance operations:
  - deposit increases sender balance
  - withdraw decreases sender balance (guarded)
  - transfer moves between accounts (guarded, sender ≠ to, no overflow)
  - getBalance returns correct value
  - All operations preserve non-mapping storage
-/

import Verity.Specs.Ledger.Spec
import Verity.Specs.Ledger.Invariants
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation

namespace Verity.Proofs.Ledger

open Verity
open Verity.Examples.Ledger
open Verity.Specs.Ledger
open Verity.Stdlib.Math (safeAdd requireSomeUint MAX_UINT256)
open Verity.Proofs.Stdlib.Math (safeAdd_some safeAdd_none)
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne uint256_ge_val_le)

/-! ## getBalance Correctness -/

theorem getBalance_meets_spec (s : ContractState) (addr : Address) :
  let result := ((getBalance addr).run s).fst
  getBalance_spec addr result s := by
  simp [getBalance, getMapping, balances, getBalance_spec, Contract.run, ContractResult.fst]

theorem getBalance_returns_balance (s : ContractState) (addr : Address) :
  ((getBalance addr).run s).fst = s.storageMap 0 addr := by
  simp [getBalance, getMapping, balances, Contract.run, ContractResult.fst]

theorem getBalance_preserves_state (s : ContractState) (addr : Address) :
  ((getBalance addr).run s).snd = s := by
  simp [getBalance, getMapping, balances, Contract.run, ContractResult.snd]

/-! ## Deposit Correctness -/

/-- Helper: unfold deposit computation -/
private theorem deposit_unfold (s : ContractState) (amount : Uint256) :
  (deposit amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 0 && addr == s.sender) = true then EVM.Uint256.add (s.storageMap 0 s.sender) amount
        else s.storageMap slot addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := fun slot =>
        if slot == 0 then (s.knownAddresses slot).insert s.sender
        else s.knownAddresses slot,
      events := s.events } := by
  simp only [deposit, msgSender, getMapping, setMapping, balances,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]

theorem deposit_meets_spec (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  deposit_spec amount s s' := by
  rw [deposit_unfold]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ContractResult.snd, beq_iff_eq]
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [ContractResult.snd, beq_iff_eq, h_ne]
    · intro slot h_ne addr
      simp [ContractResult.snd, beq_iff_eq, h_ne]
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

theorem deposit_increases_balance (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.add (s.storageMap 0 s.sender) amount := by
  rw [deposit_unfold]; simp [ContractResult.snd]

theorem deposit_preserves_other_balances (s : ContractState) (amount : Uint256)
  (addr : Address) (h_ne : addr ≠ s.sender) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 addr = s.storageMap 0 addr := by
  rw [deposit_unfold]; simp [ContractResult.snd, beq_iff_eq, h_ne]

/-! ## Withdraw Correctness -/

/-- Helper: unfold withdraw when balance is sufficient -/
private theorem withdraw_unfold (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  (withdraw amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 0 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 0 s.sender) amount
        else s.storageMap slot addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := fun slot =>
        if slot == 0 then (s.knownAddresses slot).insert s.sender
        else s.knownAddresses slot,
      events := s.events } := by
  simp only [withdraw, msgSender, getMapping, setMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance]

theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  withdraw_spec amount s s' := by
  rw [withdraw_unfold s amount h_balance]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ContractResult.snd, beq_iff_eq]
  · refine ⟨?_, ?_⟩
    · intro addr h_ne
      simp [ContractResult.snd, beq_iff_eq, h_ne]
    · intro slot h_ne addr
      simp [ContractResult.snd, beq_iff_eq, h_ne]
  · rfl
  · rfl
  · exact Specs.sameContext_rfl _

theorem withdraw_decreases_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  rw [withdraw_unfold s amount h_balance]; simp [ContractResult.snd]

theorem withdraw_reverts_insufficient (s : ContractState) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (withdraw amount).run s = ContractResult.revert msg s := by
  simp only [withdraw, msgSender, getMapping, setMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [show (s.storageMap 0 s.sender >= amount) = false from by
    simp [ge_iff_le] at h_insufficient ⊢; omega]

/-! ## Transfer Correctness -/

/-- Helper: unfold transfer when balance sufficient and sender == to (no-op). -/
private theorem transfer_unfold_self (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_eq : s.sender = to) :
  (transfer to amount).run s = ContractResult.success () s := by
  simp [transfer, msgSender, getMapping, setMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    uint256_ge_val_le (h_eq ▸ h_balance), h_eq, beq_iff_eq]

/-- Helper: unfold transfer when balance sufficient, sender ≠ to, and no overflow. -/
private theorem transfer_unfold_other (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  (transfer to amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 0 && addr == to) = true then EVM.Uint256.add (s.storageMap 0 to) amount
        else if (slot == 0 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 0 s.sender) amount
        else s.storageMap slot addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := fun slot =>
        if slot == 0 then ((s.knownAddresses slot).insert s.sender).insert to
        else s.knownAddresses slot,
      events := s.events } := by
  simp only [transfer, Examples.Ledger.balances,
    msgSender, getMapping, setMapping,
    requireSomeUint,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_balance, h_ne, beq_iff_eq, safeAdd_some (s.storageMap 0 to) amount h_no_overflow, ge_iff_le,
    decide_eq_true_eq, uint256_ge_val_le h_balance, ite_true, ite_false, HAdd.hAdd, Add.add]
  congr 1
  congr 1
  funext slot
  split <;> simp [*]

theorem transfer_meets_spec (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_no_overflow : s.sender ≠ to → (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  transfer_spec to amount s s' := by
  by_cases h_eq : s.sender = to
  · rw [transfer_unfold_self s to amount h_balance h_eq]
    simp only [ContractResult.snd, transfer_spec]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h_eq, beq_iff_eq, h_balance]
    · simp [h_eq, beq_iff_eq]
    · simp [h_eq, beq_iff_eq, Specs.storageMapUnchangedExceptKeyAtSlot,
        Specs.storageMapUnchangedExceptKey, Specs.storageMapUnchangedExceptSlot]
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameContext]
  · rw [transfer_unfold_other s to amount h_balance h_eq (h_no_overflow h_eq)]
    simp only [ContractResult.snd, transfer_spec]
    have h_ne' := address_beq_false_of_ne s.sender to h_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [beq_iff_eq, h_ne', h_balance]
    · simp [beq_iff_eq, h_ne']
    · simp [h_ne']
      refine ⟨?_, ?_⟩
      · intro addr h_ne_sender h_ne_to
        simp [beq_iff_eq, h_ne_sender, h_ne_to]
      · intro slot h_slot addr
        simp [beq_iff_eq, h_slot]
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameContext]

theorem transfer_self_preserves_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((transfer s.sender amount).run s).snd
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender := by
  have h := transfer_meets_spec s s.sender amount h_balance (fun h => absurd rfl h)
  simp [transfer_spec, beq_iff_eq] at h
  exact h.1

theorem transfer_decreases_sender (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 s.sender = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  have h := transfer_meets_spec s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  exact h.1

theorem transfer_increases_recipient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 to = EVM.Uint256.add (s.storageMap 0 to) amount := by
  have h := transfer_meets_spec s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h
  exact h.2.1

theorem transfer_reverts_insufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp only [transfer, msgSender, getMapping, setMapping, balances,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [show (s.storageMap 0 s.sender >= amount) = false from by
    simp [ge_iff_le] at h_insufficient ⊢; omega]

-- Transfer reverts on recipient balance overflow
theorem transfer_reverts_recipient_overflow (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) > MAX_UINT256) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp [transfer, requireSomeUint, Examples.Ledger.balances,
    msgSender, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    uint256_ge_val_le h_balance, h_ne, beq_iff_eq,
    safeAdd_none (s.storageMap 0 to) amount h_overflow]

/-! ## State Preservation -/

theorem deposit_preserves_non_mapping (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [deposit_unfold]
  simp [ContractResult.snd, non_mapping_storage_unchanged, Specs.sameStorage, Specs.sameStorageAddr]

theorem withdraw_preserves_non_mapping (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [withdraw_unfold s amount h_balance]
  simp [ContractResult.snd, non_mapping_storage_unchanged, Specs.sameStorage, Specs.sameStorageAddr]

theorem deposit_preserves_wellformedness (s : ContractState) (amount : Uint256)
  (h : WellFormedState s) :
  let s' := ((deposit amount).run s).snd
  WellFormedState s' := by
  rw [deposit_unfold]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

theorem withdraw_preserves_wellformedness (s : ContractState) (amount : Uint256)
  (h : WellFormedState s) (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  WellFormedState s' := by
  rw [withdraw_unfold s amount h_balance]
  simp [ContractResult.snd]
  exact ⟨h.sender_nonempty, h.contract_nonempty⟩

/-! ## Composition: deposit → getBalance -/

theorem deposit_getBalance_correct (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.add (s.storageMap 0 s.sender) amount := by
  rw [deposit_unfold]
  simp [ContractResult.snd, getBalance, getMapping, balances, Contract.run, ContractResult.fst]

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

Transfer (guarded, sender ≠ to, overflow-safe):
10. transfer_meets_spec
11. transfer_decreases_sender
12. transfer_increases_recipient
13. transfer_reverts_insufficient
14. transfer_reverts_recipient_overflow

State preservation:
15. deposit_preserves_non_mapping
16. withdraw_preserves_non_mapping
17. deposit_preserves_wellformedness
18. withdraw_preserves_wellformedness

Composition:
19. deposit_getBalance_correct
-/

end Verity.Proofs.Ledger
