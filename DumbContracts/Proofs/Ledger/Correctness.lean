/-
  Advanced correctness proofs for Ledger contract.

  Proves deeper properties beyond Basic.lean:
  - Invariant preservation: transfer preserves WellFormedState
  - End-to-end composition: withdraw→getBalance, transfer→getBalance
  - Deposit-withdraw cancellation: deposit then withdraw returns to original balance
-/

import DumbContracts.Core
import DumbContracts.Examples.Ledger
import DumbContracts.Specs.Ledger.Spec
import DumbContracts.Specs.Ledger.Invariants
import DumbContracts.Proofs.Ledger.Basic

namespace DumbContracts.Proofs.Ledger.Correctness

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.Specs.Ledger
open DumbContracts.Proofs.Ledger

/-! ## Invariant Preservation -/

/-- Transfer preserves WellFormedState (sender ≠ recipient). -/
theorem transfer_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  WellFormedState s' := by
  have h_spec := transfer_meets_spec s to amount h_balance h_ne
  simp [transfer_spec] at h_spec
  obtain ⟨_, _, _, _, _, _, h_sender, h_this⟩ := h_spec
  constructor
  · exact h_sender ▸ h.sender_nonempty
  · exact h_this ▸ h.contract_nonempty

/-- Transfer preserves non-mapping storage. -/
theorem transfer_preserves_non_mapping (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  have h_spec := transfer_meets_spec s to amount h_balance h_ne
  simp [transfer_spec, non_mapping_storage_unchanged] at *
  exact ⟨h_spec.2.2.2.2.1, h_spec.2.2.2.2.2.1⟩

/-! ## End-to-End Composition -/

/-- After withdraw, getBalance returns the decreased balance. -/
theorem withdraw_getBalance_correct (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  ((getBalance s.sender).run s').fst = s.storageMap 0 s.sender - amount := by
  show ((getBalance s.sender).run ((withdraw amount).run s).snd).fst = _
  rw [getBalance_returns_balance]
  exact withdraw_decreases_balance s amount h_balance

/-- After transfer, sender's balance is decreased. -/
theorem transfer_getBalance_sender_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  ((getBalance s.sender).run s').fst = s.storageMap 0 s.sender - amount := by
  show ((getBalance s.sender).run ((transfer to amount).run s).snd).fst = _
  rw [getBalance_returns_balance]
  exact transfer_decreases_sender s to amount h_balance h_ne

/-- After transfer, recipient's balance is increased. -/
theorem transfer_getBalance_recipient_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  ((getBalance to).run s').fst = s.storageMap 0 to + amount := by
  show ((getBalance to).run ((transfer to amount).run s).snd).fst = _
  rw [getBalance_returns_balance]
  exact transfer_increases_recipient s to amount h_balance h_ne

/-! ## Deposit-Withdraw Cancellation

A key property: depositing and then withdrawing the same amount
returns to the original balance. This proves operations are inverses.
-/

/-- Deposit then withdraw of the same amount returns to original balance.
    Requires that the intermediate balance (original + amount) is sufficient
    for withdrawal, which is trivially true. -/
theorem deposit_withdraw_cancel (s : ContractState) (amount : Uint256) :
  let s1 := ((deposit amount).run s).snd
  let s2 := ((withdraw amount).run s1).snd
  s2.storageMap 0 s.sender = s.storageMap 0 s.sender := by
  -- After deposit, sender balance = original + amount
  have h_dep := deposit_increases_balance s amount
  -- The intermediate state has sufficient balance for withdrawal
  -- s1.storageMap 0 s.sender = s.storageMap 0 s.sender + amount
  -- s1.sender = s.sender (context preserved)
  simp only [deposit, withdraw, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [Nat.add_sub_cancel]

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

end DumbContracts.Proofs.Ledger.Correctness
