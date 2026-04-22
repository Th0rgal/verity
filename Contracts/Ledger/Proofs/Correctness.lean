/-
  Advanced correctness proofs for Ledger contract.

  Proves deeper properties beyond Basic.lean:
  - Invariant preservation: transfer preserves WellFormedState
  - End-toAddr-end composition: withdraw→getBalance, transfer→getBalance
  - Deposit-withdraw cancellation: deposit then withdraw returns toAddr original balance
-/

import Contracts.Ledger.Proofs.Basic

namespace Contracts.Ledger.Proofs.Correctness

open Verity
open Contracts.Ledger
open Contracts.Ledger.Spec
open Contracts.Ledger.Proofs
open Contracts.Ledger.Invariants

/-! ## Invariant Preservation -/

/-- Transfer preserves WellFormedState (sender ≠ recipient). -/
theorem transfer_preserves_wellformedness (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h : WellFormedState s)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ toAddr) :
  let s' := ((transfer toAddr amount).run s).snd
  WellFormedState s' := by
  have h_spec := transfer_meets_spec s toAddr amount h_balance
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  have h_frame := h_spec.2.2.2
  constructor
  · exact h_frame.2.2.2.1 ▸ h.sender_nonzero
  · exact h_frame.2.2.2.2.1 ▸ h.contract_nonzero

/-- Transfer preserves non-mapping storage. -/
theorem transfer_preserves_non_mapping (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ toAddr) :
  let s' := ((transfer toAddr amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  have h_spec := transfer_meets_spec s toAddr amount h_balance
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  have h_frame := h_spec.2.2.2
  simp [non_mapping_storage_unchanged]
  exact ⟨h_frame.1, h_frame.2.1, h_frame.2.2.1⟩

/-! ## End-toAddr-End Composition -/

/-- After withdraw, getBalance returns the decreased balance. -/
theorem withdraw_getBalance_correct (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  simp only [getBalance_returns_balance]
  exact withdraw_decreases_balance s amount h_balance

/-- After transfer, sender's balance is decreased. -/
theorem transfer_getBalance_sender_correct (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ toAddr) :
  let s' := ((transfer toAddr amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  simp only [getBalance_returns_balance]
  exact transfer_decreases_sender s toAddr amount h_balance h_ne

/-- After transfer, recipient's balance is increased. -/
theorem transfer_getBalance_recipient_correct (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ toAddr) :
  let s' := ((transfer toAddr amount).run s).snd
  ((getBalance toAddr).run s').fst = EVM.Uint256.add (s.storageMap 0 toAddr) amount := by
  simp only [getBalance_returns_balance]
  exact transfer_increases_recipient s toAddr amount h_balance h_ne

/-! ## Deposit-Withdraw Cancellation

A key property: depositing and then withdrawing the same amount
returns toAddr the original balance. This proves operations are inverses.
-/

/-- Deposit then withdraw of the same amount returns toAddr original balance.
    Requires that the intermediate balance (original + amount) is sufficient
    for withdrawal, which is trivially true. -/
theorem deposit_withdraw_cancel (s : ContractState) (amount : Uint256)
  (h_balance : amount ≤ EVM.Uint256.add (s.storageMap 0 s.sender) amount) :
  let s1 := ((deposit amount).run s).snd
  let s2 := ((withdraw amount).run s1).snd
  s2.storageMap 0 s.sender = s.storageMap 0 s.sender := by
  let s1 := ((deposit amount).run s).snd
  have h_inc := deposit_increases_balance s amount
  have h_sender : s1.sender = s.sender := by
    simp [s1, deposit, msgSender, getMapping, setMapping, balances,
      Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd]
  have h_balance' : s1.storageMap 0 s.sender ≥ amount := by
    simpa [s1, h_inc] using h_balance
  have h_wd := withdraw_decreases_balance (s := s1) amount h_balance'
  rw [h_sender, h_inc] at h_wd
  simpa [s1, EVM.Uint256.sub_add_cancel (s.storageMap 0 s.sender) amount] using h_wd

/-! ## Summary

All 6 theorems fully proven with zero sorry:

Invariant preservation:
1. transfer_preserves_wellformedness
2. transfer_preserves_non_mapping

End-toAddr-end composition:
3. withdraw_getBalance_correct
4. transfer_getBalance_sender_correct
5. transfer_getBalance_recipient_correct

Cancellation:
6. deposit_withdraw_cancel — deposit then withdraw is identity
-/

end Contracts.Ledger.Proofs.Correctness
