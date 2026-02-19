/-
  Advanced correctness proofs for Ledger contract.

  Proves deeper properties beyond Basic.lean:
  - Invariant preservation: transfer preserves WellFormedState
  - End-to-end composition: withdraw→getBalance, transfer→getBalance
  - Deposit-withdraw cancellation: deposit then withdraw returns to original balance
-/

import Verity.Proofs.Ledger.Basic

namespace Verity.Proofs.Ledger.Correctness

open Verity
open Verity.Examples.Ledger
open Verity.Specs.Ledger
open Verity.Proofs.Ledger
open Verity.Stdlib.Math (MAX_UINT256)

/-! ## Invariant Preservation -/

/-- Transfer preserves WellFormedState (sender ≠ recipient). -/
theorem transfer_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  WellFormedState s' := by
  have h_spec := transfer_meets_spec s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  obtain ⟨_, _, _, _, _, h_sender, h_this, _, _⟩ := h_spec
  constructor
  · exact h_sender ▸ h.sender_nonempty
  · exact h_this ▸ h.contract_nonempty

/-- Transfer preserves non-mapping storage. -/
theorem transfer_preserves_non_mapping (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  have h_spec := transfer_meets_spec s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  obtain ⟨_, _, _, h_storage, h_addr, _h_ctx⟩ := h_spec
  simp [non_mapping_storage_unchanged]
  exact ⟨h_storage, h_addr⟩

/-! ## End-to-End Composition -/

/-- After withdraw, getBalance returns the decreased balance. -/
theorem withdraw_getBalance_correct (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  simp only [getBalance_returns_balance]
  exact withdraw_decreases_balance s amount h_balance

/-- After transfer, sender's balance is decreased. -/
theorem transfer_getBalance_sender_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  ((getBalance s.sender).run s').fst = EVM.Uint256.sub (s.storageMap 0 s.sender) amount := by
  simp only [getBalance_returns_balance]
  exact transfer_decreases_sender s to amount h_balance h_ne h_no_overflow

/-- After transfer, recipient's balance is increased. -/
theorem transfer_getBalance_recipient_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  ((getBalance to).run s').fst = EVM.Uint256.add (s.storageMap 0 to) amount := by
  simp only [getBalance_returns_balance]
  exact transfer_increases_recipient s to amount h_balance h_ne h_no_overflow

/-! ## Deposit-Withdraw Cancellation

A key property: depositing and then withdrawing the same amount
returns to the original balance. This proves operations are inverses.
-/

/-- Deposit then withdraw of the same amount returns to original balance.
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
      Verity.bind, Bind.bind, Verity.pure, Pure.pure,
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

End-to-end composition:
3. withdraw_getBalance_correct
4. transfer_getBalance_sender_correct
5. transfer_getBalance_recipient_correct

Cancellation:
6. deposit_withdraw_cancel — deposit then withdraw is identity
-/

end Verity.Proofs.Ledger.Correctness
