/-
  Token supply conservation proofs for SimpleToken.

  Proves supply-related conservation properties:
  1. Constructor establishes the supply_bounds_balances invariant
  2. Mint has an exact sum equation (accounting for occurrences)
  3. Transfer has an exact sum conservation equation (accounting for occurrences)

  Key insight: supply_bounds_balances (∀ lists, sum ≤ supply) quantifies over ALL
  lists including duplicates. For a list containing address `toAddr` twice, minting
  `amount` toAddr `toAddr` increases the sum by 2*amount but supply by only amount.
  This means the invariant cannot be preserved by mint/transfer in general.
  We prove the exact conservation equation instead, which is the strongest
  provable statement about how sums change under state-modifying operations.
-/

import Contracts.SimpleToken.Proofs.Basic
import Verity.Proofs.Stdlib.ListSum

namespace Contracts.SimpleToken.Proofs.Supply

open Verity
open Verity.Stdlib.Math (MAX_UINT256)
open Contracts.SimpleToken (mint transfer balanceOf getTotalSupply getOwner isOwner)
open Contracts.SimpleToken.Spec
open Contracts.SimpleToken.Proofs
open Verity.Proofs.Stdlib.ListSum (countOcc countOccU countOccU_cons_eq countOccU_cons_ne
  map_sum_point_update map_sum_transfer_eq map_sum_point_decrease)
open Verity.Proofs.Stdlib.Automation (evm_add_eq_hadd)
open Contracts.SimpleToken.Invariants

/-! ## Helper: All-Zero List Sum -/

/-- If every element maps toAddr 0, the list sum is 0. -/
private theorem map_sum_zero_of_all_zero
  (f : Address → Uint256) (h_zero : ∀ addr, f addr = 0) :
  ∀ addrs : List Address, (addrs.map f).sum = 0 := by
  intro addrs
  induction addrs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    rw [h_zero a, ih]
    simp

/-! ## Constructor Establishes Supply Invariant -/

/-- Constructor establishes supply_bounds_balances when starting from
    a state with all-zero balance mapping. -/
theorem constructor_establishes_supply_bounds (s : ContractState) (initialOwner : Address)
  (h_zero : ∀ addr : Address, s.storageMap 1 addr = 0) :
  let s' := ((simpleTokenConstructor initialOwner).run s).snd
  supply_bounds_balances s' := by
  simp [supply_bounds_balances]
  intro addrs
  have h_spec := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h_spec
  obtain ⟨_, h_supply_zero, _, _, h_map, _, _⟩ := h_spec
  have h_all_zero : ∀ addr, ((simpleTokenConstructor initialOwner).run s).snd.storageMap 1 addr = 0 := by
    intro addr; rw [h_map]; exact h_zero addr
  have h_sum : sum_balances ((simpleTokenConstructor initialOwner).run s).snd addrs = 0 := by
    simpa [sum_balances] using
      map_sum_zero_of_all_zero
        (fun addr => ((simpleTokenConstructor initialOwner).run s).snd.storageMap 1 addr) h_all_zero addrs
  have h_supply_zero' : ((simpleTokenConstructor initialOwner).run s).snd.storage 2 = 0 := h_supply_zero
  simp [h_sum, h_supply_zero']

/-! ## Mint: Exact Sum Equation -/

/-- Exact sum relationship after mint: the new sum equals the old sum plus
    count(toAddr, addrs) * amount. This captures that each occurrence of `toAddr` in
    the list contributes an additional `amount` toAddr the sum. -/
theorem mint_sum_equation (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 toAddr : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((mint toAddr amount).run s).snd.storageMap 1 addr)).sum
    = (addrs.map (fun addr => s.storageMap 1 addr)).sum + countOccU toAddr addrs * amount := by
  have h_spec := mint_meets_spec_when_owner s toAddr amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp [mint_spec] at h_spec
  obtain ⟨h_bal_raw, _, h_other, _, _, _⟩ := h_spec
  have h_bal :
      ((mint toAddr amount).run s).snd.storageMap 1 toAddr = s.storageMap 1 toAddr + amount := by
    simpa [evm_add_eq_hadd] using h_bal_raw
  exact map_sum_point_update
    (fun addr => s.storageMap 1 addr)
    (fun addr => ((mint toAddr amount).run s).snd.storageMap 1 addr)
    toAddr amount h_bal h_other.1

/-- Corollary: for a list where `toAddr` appears exactly once, mint adds exactly `amount`. -/
theorem mint_sum_singleton_to (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 toAddr : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (addrs : List Address) (h_once : countOcc toAddr addrs = 1) :
  (addrs.map (fun addr => ((mint toAddr amount).run s).snd.storageMap 1 addr)).sum
  = (addrs.map (fun addr => s.storageMap 1 addr)).sum + amount := by
  have h := mint_sum_equation s toAddr amount h_owner h_no_bal_overflow h_no_sup_overflow addrs
  simp [countOccU, h_once] at h
  simpa [Verity.Core.Uint256.add_comm] using h

/-- Exact sum conservation equation for transfer:
    new_sum + count(sender, addrs) * amount = old_sum + count(toAddr, addrs) * amount.

    This is the fundamental conservation law for transfer: each occurrence of the
    sender in the list loses `amount`, and each occurrence of the recipient gains
    `amount`. The equation holds exactly (not just as an inequality). -/
theorem transfer_sum_equation (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ toAddr)
  (h_no_overflow : (s.storageMap 1 toAddr : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((transfer toAddr amount).run s).snd.storageMap 1 addr)).sum
      + countOccU s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 1 addr)).sum
      + countOccU toAddr addrs * amount := by
  have h_spec := transfer_meets_spec_when_sufficient s toAddr amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  obtain ⟨_, h_sender_bal, h_recip_bal, h_other_bal, _, _, _, _⟩ := h_spec
  have h_recip_bal' :
      ((transfer toAddr amount).run s).snd.storageMap 1 toAddr = s.storageMap 1 toAddr + amount := by
    simpa [evm_add_eq_hadd] using h_recip_bal
  exact map_sum_transfer_eq
    (fun addr => s.storageMap 1 addr)
    (fun addr => ((transfer toAddr amount).run s).snd.storageMap 1 addr)
    s.sender toAddr amount h_ne h_sender_bal h_recip_bal'
    h_other_bal.1

/-- Corollary: for NoDup lists where sender and toAddr each appear once,
    the total balance sum is exactly preserved by transfer. -/
theorem transfer_sum_preserved_unique (s : ContractState) (toAddr : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ toAddr)
  (h_no_overflow : (s.storageMap 1 toAddr : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (addrs : List Address)
  (h_sender_once : countOcc s.sender addrs = 1)
  (h_to_once : countOcc toAddr addrs = 1) :
  (addrs.map (fun addr => ((transfer toAddr amount).run s).snd.storageMap 1 addr)).sum
  = (addrs.map (fun addr => s.storageMap 1 addr)).sum := by
  have h := transfer_sum_equation s toAddr amount h_balance h_ne h_no_overflow addrs
  simp [countOccU, h_sender_once, h_to_once] at h
  have h' : (addrs.map (fun addr => ((transfer toAddr amount).run s).snd.storageMap 1 addr)).sum + amount =
      (addrs.map (fun addr => s.storageMap 1 addr)).sum + amount := by
    simpa [Verity.Core.Uint256.add_comm] using h
  exact Verity.Core.Uint256.add_right_cancel h'

/-! ## Summary

All 6 theorems fully proven with zero sorry (5 public + 1 private helper).
Generic list-sum helpers (countOcc, map_sum_point_update, map_sum_transfer_eq)
are imported from Verity.Proofs.Stdlib.ListSum.

Helper lemma:
1. map_sum_zero_of_all_zero — helper for zero-sum lists

Supply conservation:
2. constructor_establishes_supply_bounds — simpleTokenConstructor establishes invariant (all lists)
3. mint_sum_equation — exact sum change: new = old + count(toAddr) * amount
4. mint_sum_singleton_to — for unique toAddr: new_sum = old_sum + amount
5. transfer_sum_equation — exact conservation: new + count(sender)*amt = old + count(toAddr)*amt
6. transfer_sum_preserved_unique — for unique sender & toAddr: new_sum = old_sum

NoDup corollaries (4 and 6) give the strongest practical conservation statements:
when each address appears at most once in the list, mint adds exactly `amount` toAddr
the balance sum, and transfer preserves it exactly.
-/

end Contracts.SimpleToken.Proofs.Supply
