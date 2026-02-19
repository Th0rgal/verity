/-
  Advanced correctness proofs for SimpleToken

  This file proves deeper properties beyond Basic.lean:
  - Guard revert behavior (mint reverts when not owner, transfer reverts with insufficient balance)
  - Invariant preservation (mint/transfer preserve WellFormedState)
  - Owner stability (mint/transfer don't change owner)
  - End-to-end composition (mint→balanceOf, transfer→balanceOf)

  These are Tier 2-3 properties: functional correctness and invariant preservation.
-/

import Verity.Proofs.SimpleToken.Basic

namespace Verity.Proofs.SimpleToken.Correctness

open Verity
open Verity.Stdlib.Math (MAX_UINT256 safeAdd requireSomeUint)
open Verity.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open Verity.Specs.SimpleToken
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne)
open Verity.Proofs.SimpleToken

/-! ## Guard Revert Proofs

These prove that operations correctly revert when preconditions are not met.
This is critical for safety: unauthorized or invalid operations must fail.
-/

/-- Mint reverts when caller is not the owner.
    Safety property: non-owners cannot create tokens. -/
theorem mint_reverts_when_not_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_not_owner : s.sender ≠ s.storageAddr 0) :
  ∃ msg, (mint to amount).run s = ContractResult.revert msg s := by
  simp only [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [address_beq_false_of_ne s.sender (s.storageAddr 0) h_not_owner]

/-- Transfer reverts when sender has insufficient balance.
    Safety property: no overdrafts possible. -/
theorem transfer_reverts_insufficient_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_insufficient : s.storageMap 1 s.sender < amount) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [show ¬(s.storageMap 1 s.sender ≥ amount) from Nat.not_le.mpr h_insufficient]

/-! ## Invariant Preservation

These prove that WellFormedState is preserved by all state-modifying operations.
Combined with Basic.lean's proofs for constructor/reads, this gives full coverage.
-/

/-- Mint preserves well-formedness when caller is owner and no overflow.
    The owner address stays non-empty, context is preserved. -/
theorem mint_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s) (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  WellFormedState s' := by
  have h_spec := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  obtain ⟨_, _, _, h_owner_pres, _, h_ctx⟩ := h_spec
  exact ⟨h_ctx.1 ▸ h.sender_nonempty, h_ctx.2.1 ▸ h.contract_nonempty, h_owner_pres ▸ h.owner_nonempty⟩

/-- Transfer preserves well-formedness when balance is sufficient and no overflow.
    Owner, context all remain intact across transfers. -/
theorem transfer_preserves_wellformedness (s : ContractState) (to : Address) (amount : Uint256)
  (h : WellFormedState s) (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_no_overflow : s.sender ≠ to → (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  WellFormedState s' := by
  have h_spec := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  obtain ⟨_, _, _, _, h_owner_pres, _h_storage, _h_addr_pres, h_ctx⟩ := h_spec
  exact ⟨h_ctx.1 ▸ h.sender_nonempty, h_ctx.2.1 ▸ h.contract_nonempty, h_owner_pres ▸ h.owner_nonempty⟩

/-! ## Owner Stability

These prove that only the constructor sets the owner — mint and transfer
never change it. This is a critical access control property.
-/

/-- Mint does not change the owner address. -/
theorem mint_preserves_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  s'.storageAddr 0 = s.storageAddr 0 :=
  (mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow).2.2.2.1

/-- Transfer does not change the owner address. -/
theorem transfer_preserves_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_no_overflow : s.sender ≠ to → (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storageAddr 0 = s.storageAddr 0 :=
  (transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow).2.2.2.2.1

/-! ## End-to-End Composition

These prove that operation sequences produce the expected observable results.
They combine state-modifying operations with read operations.
-/

/-- After minting, balanceOf returns the increased balance. -/
theorem mint_then_balanceOf_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  ((balanceOf to).run s').fst = EVM.Uint256.add (s.storageMap 1 to) amount := by
  simp only [balanceOf_returns_balance, mint_increases_balance s to amount h_owner h_no_bal_overflow h_no_sup_overflow]

/-- After minting, getTotalSupply returns the increased supply. -/
theorem mint_then_getTotalSupply_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  ((getTotalSupply).run s').fst = EVM.Uint256.add (s.storage 2) amount := by
  simp only [getTotalSupply_returns_supply, mint_increases_supply s to amount h_owner h_no_bal_overflow h_no_sup_overflow]

/-- After transfer, sender's balance is decreased by the transfer amount. -/
theorem transfer_then_balanceOf_sender_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  ((balanceOf s.sender).run s').fst = EVM.Uint256.sub (s.storageMap 1 s.sender) amount := by
  simp only [balanceOf_returns_balance]
  exact transfer_decreases_sender_balance s to amount h_balance h_ne h_no_overflow

/-- After transfer, recipient's balance is increased by the transfer amount. -/
theorem transfer_then_balanceOf_recipient_correct (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  ((balanceOf to).run s').fst = EVM.Uint256.add (s.storageMap 1 to) amount := by
  simp only [balanceOf_returns_balance]
  exact transfer_increases_recipient_balance s to amount h_balance h_ne h_no_overflow

/-! ## Summary

All 10 theorems in this file are fully proven with zero sorry:

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

end Verity.Proofs.SimpleToken.Correctness
