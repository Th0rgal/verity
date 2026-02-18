/-
  Token supply conservation proofs for SimpleToken.

  Proves supply-related conservation properties:
  1. Constructor establishes the supply_bounds_balances invariant
  2. Mint has an exact sum equation (accounting for occurrences)
  3. Transfer has an exact sum conservation equation (accounting for occurrences)

  Key insight: supply_bounds_balances (∀ lists, sum ≤ supply) quantifies over ALL
  lists including duplicates. For a list containing address `to` twice, minting
  `amount` to `to` increases the sum by 2*amount but supply by only amount.
  This means the invariant cannot be preserved by mint/transfer in general.
  We prove the exact conservation equation instead, which is the strongest
  provable statement about how sums change under state-modifying operations.
-/

import Verity.Core
import Verity.Examples.SimpleToken
import Verity.EVM.Uint256
import Verity.Stdlib.Math
import Verity.Specs.SimpleToken.Spec
import Verity.Specs.SimpleToken.Invariants
import Verity.Proofs.SimpleToken.Basic
import Verity.Proofs.Stdlib.ListSum

namespace Verity.Proofs.SimpleToken.Supply

open Verity
open Verity.Stdlib.Math (MAX_UINT256)
open Verity.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open Verity.Specs.SimpleToken hiding owner balances totalSupply
open Verity.Proofs.SimpleToken
open Verity.Proofs.Stdlib.ListSum (countOcc countOccU countOccU_cons_eq countOccU_cons_ne
  map_sum_point_update map_sum_transfer_eq)

/-! ## Helper: All-Zero List Sum -/

/-- If every element maps to 0, the list sum is 0. -/
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
  let s' := ((constructor initialOwner).run s).snd
  supply_bounds_balances s' := by
  simp [supply_bounds_balances]
  intro addrs
  have h_spec := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h_spec
  obtain ⟨_, h_supply_zero, _, _, h_map, _, _⟩ := h_spec
  have h_all_zero : ∀ addr, ((constructor initialOwner).run s).snd.storageMap 1 addr = 0 := by
    intro addr; rw [h_map]; exact h_zero addr
  have h_sum : sum_balances ((constructor initialOwner).run s).snd addrs = 0 := by
    simpa [sum_balances] using
      map_sum_zero_of_all_zero
        (fun addr => ((constructor initialOwner).run s).snd.storageMap 1 addr) h_all_zero addrs
  have h_supply_zero' : ((constructor initialOwner).run s).snd.storage 2 = 0 := h_supply_zero
  simp [h_sum, h_supply_zero']

/-! ## Mint: Exact Sum Equation -/

/-- Exact sum relationship after mint: the new sum equals the old sum plus
    count(to, addrs) * amount. This captures that each occurrence of `to` in
    the list contributes an additional `amount` to the sum. -/
theorem mint_sum_equation (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((mint to amount).run s).snd.storageMap 1 addr)).sum
    = (addrs.map (fun addr => s.storageMap 1 addr)).sum + countOccU to addrs * amount := by
  have h_spec := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp [mint_spec] at h_spec
  obtain ⟨h_bal_raw, _, h_other, _, _, _⟩ := h_spec
  have h_bal :
      ((mint to amount).run s).snd.storageMap 1 to = s.storageMap 1 to + amount := by
    have h_bal' := h_bal_raw
    simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] at h_bal'
    exact h_bal'
  exact map_sum_point_update
    (fun addr => s.storageMap 1 addr)
    (fun addr => ((mint to amount).run s).snd.storageMap 1 addr)
    to amount h_bal (fun addr h_ne => h_other.1 addr h_ne)

/-- Exact sum conservation equation for transfer:
    new_sum + count(sender, addrs) * amount = old_sum + count(to, addrs) * amount.

    This is the fundamental conservation law for transfer: each occurrence of the
    sender in the list loses `amount`, and each occurrence of the recipient gains
    `amount`. The equation holds exactly (not just as an inequality). -/
theorem transfer_sum_equation (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 1 addr)).sum
      + countOccU s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 1 addr)).sum
      + countOccU to addrs * amount := by
  have h_spec := transfer_meets_spec_when_sufficient s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  obtain ⟨_, h_sender_bal, h_recip_bal, h_other_bal, _, _, _, _⟩ := h_spec
  have h_sender_bal' :
      ((transfer to amount).run s).snd.storageMap 1 s.sender = s.storageMap 1 s.sender - amount := by
    exact h_sender_bal
  have h_recip_bal' :
      ((transfer to amount).run s).snd.storageMap 1 to = s.storageMap 1 to + amount := by
    have h_recip_bal' := h_recip_bal
    simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] at h_recip_bal'
    exact h_recip_bal'
  exact map_sum_transfer_eq
    (fun addr => s.storageMap 1 addr)
    (fun addr => ((transfer to amount).run s).snd.storageMap 1 addr)
    s.sender to amount h_ne h_sender_bal' h_recip_bal'
    (fun addr h1 h2 => h_other_bal.1 addr h1 h2)

/-! ## Summary

All 4 theorems fully proven with zero sorry (3 public + 1 private helper).
Generic list-sum helpers (countOcc, map_sum_point_update, map_sum_transfer_eq)
are imported from Verity.Proofs.Stdlib.ListSum.

Helper lemma:
1. map_sum_zero_of_all_zero — helper for zero-sum lists

Supply conservation:
2. constructor_establishes_supply_bounds — constructor establishes invariant (all lists)
3. mint_sum_equation — exact sum change: new = old + count(to) * amount
4. transfer_sum_equation — exact conservation: new + count(sender)*amt = old + count(to)*amt
Note: supply_bounds_balances as defined in Invariants.lean quantifies over ALL lists
including duplicates. For a list with address `to` appearing k times, minting increases
the sum by k*amount but supply by only amount, so the invariant is not preserved when
k > 1. The exact equations above are the strongest correct statements. For full
preservation, either restrict to NoDup lists or use a finite address model where
supply = Σ all balances exactly (see Future Directions in STATUS.md).
-/

end Verity.Proofs.SimpleToken.Supply
