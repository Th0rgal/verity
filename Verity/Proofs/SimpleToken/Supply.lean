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

namespace Verity.Proofs.SimpleToken.Supply

open Verity
open Verity.Stdlib.Math (MAX_UINT256)
open Verity.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open Verity.Specs.SimpleToken hiding owner balances totalSupply
open Verity.Proofs.SimpleToken

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

/-! ## Occurrence Counting -/

/-- Count occurrences of an element in a list. -/
def countOcc (target : Address) : List Address → Nat
  | [] => 0
  | a :: rest => (if a = target then 1 else 0) + countOcc target rest

/-- Uint256 version of countOcc for arithmetic in sum equations. -/
def countOccU (target : Address) (addrs : List Address) : Uint256 :=
  Core.Uint256.ofNat (countOcc target addrs)

/-! ## Auxiliary lemma: countOcc cons simplification -/

private theorem countOcc_cons_eq (target : Address) (rest : List Address) :
  countOcc target (target :: rest) = 1 + countOcc target rest := by
  simp [countOcc]

private theorem countOcc_cons_ne (a target : Address) (rest : List Address) (h : a ≠ target) :
  countOcc target (a :: rest) = countOcc target rest := by
  simp [countOcc, h]

private theorem countOccU_cons_eq (target : Address) (rest : List Address) :
  countOccU target (target :: rest) = (1 : Uint256) + countOccU target rest := by
  simp [countOccU, countOcc, Verity.Core.Uint256.ofNat_add]

private theorem countOccU_cons_ne (a target : Address) (rest : List Address) (h : a ≠ target) :
  countOccU target (a :: rest) = countOccU target rest := by
  simp [countOccU, countOcc, h]

/-! ## Generic List Sum Lemma -/

/-- When f' agrees with f except at target where f'(target) = f(target) + delta,
    then for any list: sum(map f') = sum(map f) + countOcc(target, list) * delta. -/
private theorem map_sum_point_update
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target + delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum = (addrs.map f).sum + countOccU target addrs * delta := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    rw [ih]
    by_cases h : a = target
    · -- a = target case
      simp [h, h_target, countOccU_cons_eq]
      -- Goal: (f target + delta) + ((rest.map f).sum + countOccU target rest * delta)
      --     = (f target + (rest.map f).sum) + (1 + countOccU target rest) * delta
      have h_mul : delta * (1 + countOccU target rest) = delta + delta * countOccU target rest := by
        calc
          delta * (1 + countOccU target rest)
              = (1 + countOccU target rest) * delta := by
                  simp [Verity.Core.Uint256.mul_comm]
          _ = delta + countOccU target rest * delta := by
                  have h_add_mul := Verity.Core.Uint256.add_mul
                    (1 : Uint256) (countOccU target rest) delta
                  calc
                    (1 + countOccU target rest) * delta
                        = 1 * delta + countOccU target rest * delta := h_add_mul
                    _ = delta + countOccU target rest * delta := by
                        simp [Verity.Core.Uint256.one_mul]
          _ = delta + delta * countOccU target rest := by
                  simp [Verity.Core.Uint256.mul_comm]
      rw [h_mul]
      -- Reassociate/commute to match RHS ordering
      rw [← Verity.Core.Uint256.add_assoc delta (f target) _]
      rw [Verity.Core.Uint256.add_comm delta (f target)]
      rw [Verity.Core.Uint256.add_assoc (f target) delta _]
      rw [← Verity.Core.Uint256.add_assoc delta (List.map f rest).sum _]
      rw [Verity.Core.Uint256.add_comm delta (List.map f rest).sum]
      rw [Verity.Core.Uint256.add_assoc (List.map f rest).sum delta _]
    · -- a ≠ target case
      simp [h, h_other a h, countOccU_cons_ne a target rest h]
      -- (f a + (rest.map f).sum) + countOcc target rest * delta  (wrong — this is f a + ...)
      -- Actually after rw [ih] earlier, goal is:
      -- f a + ((rest.map f).sum + countOcc target rest * delta)
      -- = (f a + (rest.map f).sum) + countOcc target rest * delta
      -- simp closes the goal

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

/-! ## Transfer: Exact Sum Conservation Equation -/

/-- When f' has f'(src) = f(src) - d and f'(dst) = f(dst) + d and agrees elsewhere,
    then sum(map f') + countOcc(src) * d = sum(map f) + countOcc(dst) * d. -/
private theorem map_sum_transfer_eq
  (f f' : Address → Uint256) (src dst : Address) (d : Uint256)
  (h_ne : src ≠ dst)
  (h_src : f' src = f src - d)
  (h_dst : f' dst = f dst + d)
  (h_other : ∀ addr, addr ≠ src → addr ≠ dst → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOccU src addrs * d
    = (addrs.map f).sum + countOccU dst addrs * d := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
      -- ih: (rest.map f').sum + countOccU src rest * d = (rest.map f).sum + countOccU dst rest * d
    by_cases ha_s : a = src
    · -- a = src: use rw instead of subst to avoid variable elimination issues
      simp [ha_s, h_src, countOccU_cons_eq]
      -- countOcc dst for (src :: rest): src ≠ dst so it's just countOcc dst rest
      simp [countOccU_cons_ne src dst rest h_ne]
      -- Goal: (f src - d) + (rest.map f').sum + (1 + countOccU src rest) * d
      --     = f src + (rest.map f).sum + countOccU dst rest * d
      have h_mul : d * (1 + countOccU src rest) = d + d * countOccU src rest := by
        calc
            d * (1 + countOccU src rest)
                = (1 + countOccU src rest) * d := by
                  simp [Verity.Core.Uint256.mul_comm]
          _ = d + countOccU src rest * d := by
                  have h_add_mul := Verity.Core.Uint256.add_mul
                    (1 : Uint256) (countOccU src rest) d
                  calc
                    (1 + countOccU src rest) * d
                        = 1 * d + countOccU src rest * d := h_add_mul
                    _ = d + countOccU src rest * d := by
                        simp [Verity.Core.Uint256.one_mul]
          _ = d + d * countOccU src rest := by
                  simp [Verity.Core.Uint256.mul_comm]
      rw [h_mul]
      have h_cancel : f src - d + d = f src := Verity.Core.Uint256.sub_add_cancel_left (f src) d
      rw [← Verity.Core.Uint256.add_assoc (List.map f' rest).sum d _]
      rw [Verity.Core.Uint256.add_left_comm (List.map f' rest).sum d _]
      rw [Verity.Core.Uint256.add_assoc d (List.map f' rest).sum _]
      rw [← Verity.Core.Uint256.add_assoc (f src - d) d _]
      rw [h_cancel]
      have h_congr := congrArg (fun x => f src + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc] at h_congr'
      exact h_congr'
    · by_cases ha_d : a = dst
      · -- a = dst: use rw instead of subst
        simp [ha_d, h_dst]
        have h_ne_sym : dst ≠ src := Ne.symm h_ne
        simp [countOccU_cons_ne dst src rest h_ne_sym, countOccU_cons_eq]
        have h_mul : d * (1 + countOccU dst rest) = d + d * countOccU dst rest := by
          calc
            d * (1 + countOccU dst rest)
                = (1 + countOccU dst rest) * d := by
                    simp [Verity.Core.Uint256.mul_comm]
            _ = d + countOccU dst rest * d := by
                    have h_add_mul := Verity.Core.Uint256.add_mul
                      (1 : Uint256) (countOccU dst rest) d
                    calc
                      (1 + countOccU dst rest) * d
                          = 1 * d + countOccU dst rest * d := h_add_mul
                      _ = d + countOccU dst rest * d := by
                          simp [Verity.Core.Uint256.one_mul]
            _ = d + d * countOccU dst rest := by
                    simp [Verity.Core.Uint256.mul_comm]
        rw [h_mul]
        -- move d next to f dst
        rw [← Verity.Core.Uint256.add_assoc d (f dst) _]
        rw [Verity.Core.Uint256.add_comm d (f dst)]
        rw [Verity.Core.Uint256.add_assoc (f dst) d _]
        have h_congr := congrArg (fun x => f dst + (d + x)) ih
        calc
          f dst + (d + ((List.map f' rest).sum + d * countOccU src rest))
              = f dst + (d + ((List.map f rest).sum + d * countOccU dst rest)) := by
                  have h_congr' := h_congr
                  simp [Verity.Core.Uint256.mul_comm] at h_congr'
                  exact h_congr'
          _ = f dst + ((List.map f rest).sum + (d + d * countOccU dst rest)) := by
                  rw [← Verity.Core.Uint256.add_assoc d (List.map f rest).sum _]
                  rw [Verity.Core.Uint256.add_comm d (List.map f rest).sum]
                  rw [← Verity.Core.Uint256.add_assoc (List.map f rest).sum d _]
      · -- a ≠ src, a ≠ dst
        simp [h_other a ha_s ha_d, countOccU_cons_ne a src rest ha_s, countOccU_cons_ne a dst rest ha_d]
        -- LHS: (f a + (rest.map f').sum) + countOccU src rest * d
        -- RHS: (f a + (rest.map f).sum) + countOccU dst rest * d
        have h_congr := congrArg (fun x => f a + x) ih
        have h_congr' := h_congr
        simp [Verity.Core.Uint256.add_assoc] at h_congr'
        exact h_congr'

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

All 10 theorems fully proven with zero sorry (3 public + 7 private helpers):

Helper lemmas:
1. map_sum_zero_of_all_zero — helper for zero-sum lists
2. map_sum_point_update — exact sum after point update: sum f' = sum f + count * delta
3. map_sum_transfer_eq — exact sum equation: sum f' + count(src)*d = sum f + count(dst)*d

Supply conservation:
4. constructor_establishes_supply_bounds — constructor establishes invariant (all lists)
5. mint_sum_equation — exact sum change: new = old + count(to) * amount
6. transfer_sum_equation — exact conservation: new + count(sender)*amt = old + count(to)*amt
Note: supply_bounds_balances as defined in Invariants.lean quantifies over ALL lists
including duplicates. For a list with address `to` appearing k times, minting increases
the sum by k*amount but supply by only amount, so the invariant is not preserved when
k > 1. The exact equations above are the strongest correct statements. For full
preservation, either restrict to NoDup lists or use a finite address model where
supply = Σ all balances exactly (see Future Directions in STATUS.md).
-/

end Verity.Proofs.SimpleToken.Supply
