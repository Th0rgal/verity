/-
  Advanced correctness proofs for SimpleToken

  This file proves deeper properties beyond Basic.lean:
  - Guard revert behavior (mint reverts when not owner, transfer reverts with insufficient balance)
  - Invariant preservation (mint/transfer preserve WellFormedState)
  - Owner stability (mint/transfer don't change owner)
  - End-to-end composition (mint→balanceOf, transfer→balanceOf)

  These are Tier 2-3 properties: functional correctness and invariant preservation.
-/

import DumbContracts.Examples.SimpleToken
import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants
import DumbContracts.Proofs.SimpleToken.Basic

namespace DumbContracts.Proofs.SimpleToken.Correctness

open DumbContracts
open DumbContracts.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open DumbContracts.Specs.SimpleToken hiding owner balances totalSupply
open DumbContracts.Proofs.SimpleToken

/-! ## Guard Revert Proofs

These prove that operations correctly revert when preconditions are not met.
This is critical for safety: unauthorized or invalid operations must fail.
-/

/-- Mint reverts when caller is not the owner.
    Safety property: non-owners cannot create tokens. -/
theorem mint_reverts_when_not_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, (mint to amount).run s = ContractResult.revert msg s := by
  simp only [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h : (s.sender == s.storageAddr 0) = false := by
    simp [beq_iff_eq]; exact h_not_owner
  simp [h]

/-- Transfer reverts when sender has insufficient balance.
    Safety property: no overdrafts possible. -/
theorem transfer_reverts_insufficient_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_insufficient : s.storageMap 1 s.sender < amount) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  have h_not_ge : ¬(s.storageMap 1 s.sender ≥ amount) := Nat.not_le.mpr h_insufficient
  simp [h_not_ge]

/-! ## Invariant Preservation

These prove that WellFormedState is preserved by all state-modifying operations.
Combined with Basic.lean's proofs for constructor/reads, this gives full coverage.
-/

/-- Mint preserves well-formedness when caller is owner.
    The owner address stays non-empty, context is preserved. -/
theorem mint_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  WellFormedState s' := by
  have h_spec := mint_meets_spec_when_owner s to amount h_owner
  simp [mint_spec] at h_spec
  obtain ⟨_, _, _, h_owner_pres, _, _, h_sender_pres, h_this_pres⟩ := h_spec
  constructor
  · exact h_sender_pres ▸ h.sender_nonempty
  · exact h_this_pres ▸ h.contract_nonempty
  · exact h_owner_pres ▸ h.owner_nonempty

/-- Transfer preserves well-formedness when balance is sufficient.
    Owner, context all remain intact across transfers. -/
theorem transfer_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s) (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  WellFormedState s' := by
  have h_spec := transfer_meets_spec_when_sufficient s to amount h_balance h_ne
  simp [transfer_spec] at h_spec
  obtain ⟨_, _, _, _, _, h_owner_pres, _, _, h_addr_pres, h_sender_pres, h_this_pres⟩ := h_spec
  constructor
  · exact h_sender_pres ▸ h.sender_nonempty
  · exact h_this_pres ▸ h.contract_nonempty
  · exact (h_addr_pres 0) ▸ h.owner_nonempty

/-! ## Owner Stability

These prove that only the constructor sets the owner — mint and transfer
never change it. This is a critical access control property.
-/

/-- Mint does not change the owner address. -/
theorem mint_preserves_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  s'.storageAddr 0 = s.storageAddr 0 := by
  have h := mint_meets_spec_when_owner s to amount h_owner
  simp [mint_spec] at h
  exact h.2.2.2.1

/-- Transfer does not change the owner address. -/
theorem transfer_preserves_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageAddr 0 = s.storageAddr 0 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_ne
  simp [transfer_spec] at h
  obtain ⟨_, _, _, _, _, _, _, _, h_addr, _, _⟩ := h
  exact h_addr 0

/-! ## End-to-End Composition

These prove that operation sequences produce the expected observable results.
They combine state-modifying operations with read operations.
-/

/-- After minting, balanceOf returns the increased balance. -/
theorem mint_then_balanceOf_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  ((balanceOf to).run s').fst = s.storageMap 1 to + amount := by
  show ((balanceOf to).run ((mint to amount).run s).snd).fst = _
  rw [balanceOf_returns_balance, mint_increases_balance s to amount h_owner]

/-- After minting, getTotalSupply returns the increased supply. -/
theorem mint_then_getTotalSupply_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  ((getTotalSupply).run s').fst = s.storage 2 + amount := by
  show ((getTotalSupply).run ((mint to amount).run s).snd).fst = _
  rw [getTotalSupply_returns_supply, mint_increases_supply s to amount h_owner]

/-- After transfer, sender's balance is decreased by the transfer amount. -/
theorem transfer_then_balanceOf_sender_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  ((balanceOf s.sender).run s').fst = s.storageMap 1 s.sender - amount := by
  show ((balanceOf s.sender).run ((transfer to amount).run s).snd).fst = _
  rw [balanceOf_returns_balance]
  exact transfer_decreases_sender_balance s to amount h_balance h_ne

/-- After transfer, recipient's balance is increased by the transfer amount. -/
theorem transfer_then_balanceOf_recipient_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  ((balanceOf to).run s').fst = s.storageMap 1 to + amount := by
  show ((balanceOf to).run ((transfer to amount).run s).snd).fst = _
  rw [balanceOf_returns_balance]
  exact transfer_increases_recipient_balance s to amount h_balance h_ne

/-! ## Summary

All 12 theorems in this file are fully proven with zero sorry:

Guard revert behavior:
1. mint_reverts_when_not_owner — non-owners cannot mint
2. transfer_reverts_insufficient_balance — no overdrafts

Invariant preservation:
3. mint_preserves_wellformedness — WellFormedState survives mint
4. transfer_preserves_wellformedness — WellFormedState survives transfer

Owner stability:
5. mint_preserves_owner — mint doesn't change owner
6. transfer_preserves_owner — transfer doesn't change owner

End-to-end composition:
7. mint_then_balanceOf_correct — mint→read gives expected balance
8. mint_then_getTotalSupply_correct — mint→read gives expected supply
9. transfer_then_balanceOf_sender_correct — transfer→read sender balance
10. transfer_then_balanceOf_recipient_correct — transfer→read recipient balance
-/

end DumbContracts.Proofs.SimpleToken.Correctness
