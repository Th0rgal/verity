/-
  Correctness proofs for Ledger contract.

  Proves mapping-based balance operations:
  - deposit increases sender balance
  - withdraw decreases sender balance (guarded)
  - transfer moves between accounts (guarded, sender ≠ to)
  - getBalance returns correct value
  - All operations preserve non-mapping storage
-/

import DumbContracts.Core
import DumbContracts.Examples.Ledger
import DumbContracts.Specs.Ledger.Spec
import DumbContracts.Specs.Ledger.Invariants

namespace DumbContracts.Proofs.Ledger

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.Specs.Ledger

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
        if (slot == 0 && addr == s.sender) = true then s.storageMap 0 s.sender + amount
        else s.storageMap slot addr,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  simp only [deposit, msgSender, getMapping, setMapping, balances,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]

theorem deposit_meets_spec (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  deposit_spec amount s s' := by
  rw [deposit_unfold]
  simp only [ContractResult.snd, deposit_spec]
  refine ⟨by simp, ?_, ?_, trivial, trivial, trivial, trivial⟩
  · intro addr h_ne
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne
  · intro slot h_ne addr
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne

theorem deposit_increases_balance (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender + amount := by
  rw [deposit_unfold]; simp [ContractResult.snd]

theorem deposit_preserves_other_balances (s : ContractState) (amount : Uint256)
  (addr : Address) (h_ne : addr ≠ s.sender) :
  let s' := ((deposit amount).run s).snd
  s'.storageMap 0 addr = s.storageMap 0 addr := by
  rw [deposit_unfold]; simp [ContractResult.snd, beq_iff_eq]
  intro h_eq; exact absurd h_eq h_ne

/-! ## Withdraw Correctness -/

/-- Helper: unfold withdraw when balance is sufficient -/
private theorem withdraw_unfold (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  (withdraw amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 0 && addr == s.sender) = true then s.storageMap 0 s.sender - amount
        else s.storageMap slot addr,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  simp only [withdraw, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance]

theorem withdraw_meets_spec (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  withdraw_spec amount s s' := by
  rw [withdraw_unfold s amount h_balance]
  simp only [ContractResult.snd, withdraw_spec]
  refine ⟨by simp, ?_, ?_, trivial, trivial, trivial, trivial⟩
  · intro addr h_ne
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne
  · intro slot h_ne addr
    simp [beq_iff_eq]
    intro h_eq; exact absurd h_eq h_ne

theorem withdraw_decreases_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender - amount := by
  rw [withdraw_unfold s amount h_balance]; simp [ContractResult.snd]

theorem withdraw_reverts_insufficient (s : ContractState) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (withdraw amount).run s = ContractResult.revert msg s := by
  simp only [withdraw, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [show (s.storageMap 0 s.sender >= amount) = false from by
    simp [ge_iff_le] at h_insufficient ⊢; omega]

/-! ## Transfer Correctness -/

/-- Helper: unfold transfer when balance sufficient and sender ≠ to -/
private theorem transfer_unfold (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  (transfer to amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 0 && addr == to) = true then s.storageMap 0 to + amount
        else if (slot == 0 && addr == s.sender) = true then s.storageMap 0 s.sender - amount
        else s.storageMap slot addr,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  simp only [transfer, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_ne' : (s.sender == to) = false := by simp [beq_iff_eq]; exact h_ne
  simp [h_balance, h_ne']

theorem transfer_meets_spec (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  transfer_spec to amount s s' := by
  simp only [transfer, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst, transfer_spec]
  have h_ne' : (s.sender == to) = false := by simp [beq_iff_eq]; exact h_ne
  simp [h_balance, h_ne']
  refine ⟨?_, ?_, ?_⟩
  · -- case: addr = s.sender = to (contradicts h_ne)
    intro h_eq; exact absurd h_eq h_ne
  · -- other balances unchanged
    intro addr h1 h2
    simp [show ¬(addr = to) from h2, show ¬(addr = s.sender) from fun h => h1 (h ▸ rfl)]
  · -- other slots unchanged
    intro slot h_slot addr
    simp [show ¬(slot = 0) from h_slot]

theorem transfer_decreases_sender (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender - amount := by
  have h := transfer_meets_spec s to amount h_balance h_ne
  simp [transfer_spec] at h
  exact h.1

theorem transfer_increases_recipient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 0 to = s.storageMap 0 to + amount := by
  have h := transfer_meets_spec s to amount h_balance h_ne
  simp [transfer_spec] at h
  exact h.2.1

theorem transfer_reverts_insufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_insufficient : ¬(s.storageMap 0 s.sender >= amount)) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp only [transfer, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [show (s.storageMap 0 s.sender >= amount) = false from by
    simp [ge_iff_le] at h_insufficient ⊢; omega]

/-! ## State Preservation -/

theorem deposit_preserves_non_mapping (s : ContractState) (amount : Uint256) :
  let s' := ((deposit amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [deposit_unfold]
  simp [ContractResult.snd, non_mapping_storage_unchanged]

theorem withdraw_preserves_non_mapping (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  let s' := ((withdraw amount).run s).snd
  non_mapping_storage_unchanged s s' := by
  rw [withdraw_unfold s amount h_balance]
  simp [ContractResult.snd, non_mapping_storage_unchanged]

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
  ((getBalance s.sender).run s').fst = s.storageMap 0 s.sender + amount := by
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

Transfer (guarded, sender ≠ to):
10. transfer_meets_spec
11. transfer_decreases_sender
12. transfer_increases_recipient
13. transfer_reverts_insufficient

State preservation:
14. deposit_preserves_non_mapping
15. withdraw_preserves_non_mapping
16. deposit_preserves_wellformedness
17. withdraw_preserves_wellformedness

Composition:
18. deposit_getBalance_correct
-/

end DumbContracts.Proofs.Ledger
