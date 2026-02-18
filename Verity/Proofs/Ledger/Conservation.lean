/-
  Balance conservation proofs for Ledger contract.

  Proves exact sum equations for how operations change the total balance
  across any list of addresses:
  1. Deposit: new_sum = old_sum + countOcc(sender, addrs) * amount
  2. Withdraw: new_sum + countOcc(sender, addrs) * amount = old_sum (when guarded)
  3. Transfer: new_sum + countOcc(sender, addrs) * amount = old_sum + countOcc(to, addrs) * amount

  These are the strongest correct statements about sum changes. The countOcc
  factor accounts for addresses appearing multiple times in the list.
-/

import Verity.Core
import Verity.Examples.Ledger
import Verity.EVM.Uint256
import Verity.Specs.Ledger.Spec
import Verity.Specs.Ledger.Invariants
import Verity.Proofs.Ledger.Basic
import Verity.Stdlib.Math

namespace Verity.Proofs.Ledger.Conservation

open Verity
open Verity.Examples.Ledger
open Verity.Specs.Ledger
open Verity.Proofs.Ledger
open Verity.Stdlib.Math (MAX_UINT256)

/-! ## Occurrence Counting -/

/-- Count occurrences of an element in a list. -/
def countOcc (target : Address) : List Address → Nat
  | [] => 0
  | a :: rest => (if a = target then 1 else 0) + countOcc target rest

/-- Uint256 version of countOcc for arithmetic in sum equations. -/
def countOccU (target : Address) (addrs : List Address) : Uint256 :=
  Core.Uint256.ofNat (countOcc target addrs)

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

/-! ## Generic List Sum Lemma: Point Update -/

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
    · simp [h, h_target, countOccU_cons_eq]
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
      rw [← Verity.Core.Uint256.add_assoc delta (f target) _]
      rw [Verity.Core.Uint256.add_comm delta (f target)]
      rw [Verity.Core.Uint256.add_assoc (f target) delta _]
      rw [← Verity.Core.Uint256.add_assoc delta (List.map f rest).sum _]
      rw [Verity.Core.Uint256.add_comm delta (List.map f rest).sum]
      rw [Verity.Core.Uint256.add_assoc (List.map f rest).sum delta _]
    · simp [h, h_other a h, countOccU_cons_ne a target rest h]
      -- simp closes the goal

/-! ## Generic List Sum Lemma: Point Decrease -/

/-- When f' agrees with f except at target where f'(target) = f(target) - delta,
    and f(target) ≥ delta, then:
    sum(map f') + countOcc(target, list) * delta = sum(map f). -/
private theorem map_sum_point_decrease
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target - delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOccU target addrs * delta = (addrs.map f).sum := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc, countOccU]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    by_cases h : a = target
    · simp [h, h_target, countOccU_cons_eq]
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
      have h_cancel : f target - delta + delta = f target := Verity.Core.Uint256.sub_add_cancel_left (f target) delta
      rw [← Verity.Core.Uint256.add_assoc (List.map f' rest).sum delta _]
      rw [Verity.Core.Uint256.add_left_comm (List.map f' rest).sum delta _]
      rw [Verity.Core.Uint256.add_assoc delta (List.map f' rest).sum _]
      rw [← Verity.Core.Uint256.add_assoc (f target - delta) delta _]
      rw [h_cancel]
      have h_congr := congrArg (fun x => f target + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc] at h_congr'
      exact h_congr'
    · simp [h, h_other a h, countOccU_cons_ne a target rest h]
      have h_congr := congrArg (fun x => f a + x) ih
      have h_congr' := h_congr
      simp [Verity.Core.Uint256.mul_comm,
        Verity.Core.Uint256.add_assoc,
        Verity.Core.Uint256.add_left_comm,
        Verity.Core.Uint256.add_comm] at h_congr'
      exact h_congr'

/-! ## Generic List Sum Lemma: Transfer (Two-Point Update) -/

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
    by_cases ha_s : a = src
    · simp [ha_s, h_src, countOccU_cons_eq, countOccU_cons_ne src dst rest h_ne]
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
      · simp [ha_d, h_dst]
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
      · simp [h_other a ha_s ha_d, countOccU_cons_ne a src rest ha_s, countOccU_cons_ne a dst rest ha_d]
        have h_congr := congrArg (fun x => f a + x) ih
        have h_congr' := h_congr
        simp [Verity.Core.Uint256.add_assoc] at h_congr'
        exact h_congr'

/-! ## Deposit: Exact Sum Equation -/

/-- Exact sum relationship after deposit: the new sum equals the old sum plus
    count(sender, addrs) * amount. Each occurrence of the sender in the list
    contributes an additional `amount` to the sum. -/
theorem deposit_sum_equation (s : ContractState) (amount : Uint256)
  :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)).sum
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum + countOccU s.sender addrs * amount := by
  have h_inc_raw := deposit_increases_balance s amount
  have h_inc :
      ((deposit amount).run s).snd.storageMap 0 s.sender =
        s.storageMap 0 s.sender + amount := by
    have h_inc' := h_inc_raw
    simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] at h_inc'
    exact h_inc'
  have h_other : ∀ addr, addr ≠ s.sender →
    ((deposit amount).run s).snd.storageMap 0 addr = s.storageMap 0 addr :=
    fun addr h_ne => deposit_preserves_other_balances s amount addr h_ne
  exact map_sum_point_update
    (fun addr => s.storageMap 0 addr)
    (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)
    s.sender amount h_inc h_other

/-- Corollary: for a list where sender appears exactly once, deposit adds exactly `amount`. -/
theorem deposit_sum_singleton_sender (s : ContractState) (amount : Uint256)
  (addrs : List Address) (h_once : countOcc s.sender addrs = 1) :
  (addrs.map (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)).sum
  = (addrs.map (fun addr => s.storageMap 0 addr)).sum + amount := by
  have h := deposit_sum_equation s amount addrs
  have h' := h
  simp [countOccU, h_once] at h'
  exact (by
    calc
      (addrs.map (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)).sum
          = amount + (addrs.map (fun addr => s.storageMap 0 addr)).sum := h'
      _ = (addrs.map (fun addr => s.storageMap 0 addr)).sum + amount := by
          exact Verity.Core.Uint256.add_comm amount
            ((addrs.map (fun addr => s.storageMap 0 addr)).sum))

/-! ## Withdraw: Exact Sum Equation -/

/-- Exact sum relationship after withdraw (when balance sufficient):
    new_sum + count(sender, addrs) * amount = old_sum.
    Each occurrence of the sender in the list contributes `amount` less to the new sum. -/
theorem withdraw_sum_equation (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum
      + countOccU s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h_dec_raw := withdraw_decreases_balance s amount h_balance
  have h_dec :
      ((withdraw amount).run s).snd.storageMap 0 s.sender =
        s.storageMap 0 s.sender - amount := by
    exact h_dec_raw
  have h_other : ∀ addr, addr ≠ s.sender →
    ((withdraw amount).run s).snd.storageMap 0 addr = s.storageMap 0 addr := by
    intro addr h_ne
    have h_spec := withdraw_meets_spec s amount h_balance
    simp [withdraw_spec] at h_spec
    exact h_spec.2.1.1 addr h_ne
  exact map_sum_point_decrease
    (fun addr => s.storageMap 0 addr)
    (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)
    s.sender amount h_dec h_other

/-- Corollary: for a list where sender appears exactly once, withdraw removes exactly `amount`. -/
theorem withdraw_sum_singleton_sender (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (addrs : List Address) (h_once : countOcc s.sender addrs = 1) :
  (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum + amount
  = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h := withdraw_sum_equation s amount h_balance addrs
  have h' := h
  simp [countOccU, h_once] at h'
  exact (by
    calc
      (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum + amount
          = amount + (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum := by
              exact Verity.Core.Uint256.add_comm
                ((addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum) amount
      _ = (addrs.map (fun addr => s.storageMap 0 addr)).sum := h'
    )

/-! ## Transfer: Exact Sum Conservation Equation -/

/-- Exact sum conservation equation for transfer:
    new_sum + count(sender, addrs) * amount = old_sum + count(to, addrs) * amount.

    This is the fundamental conservation law for Ledger transfer: each occurrence
    of the sender in the list loses `amount`, and each occurrence of the recipient
    gains `amount`. The equation holds exactly (not just as an inequality). -/
theorem transfer_sum_equation (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
      + countOccU s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum
      + countOccU to addrs * amount := by
  have h_spec := transfer_meets_spec s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h_spec
  obtain ⟨h_sender_bal, h_recip_bal, h_other_bal, _, _, _⟩ := h_spec
  have h_sender_bal' :
      ((transfer to amount).run s).snd.storageMap 0 s.sender =
        s.storageMap 0 s.sender - amount := by
    exact h_sender_bal
  have h_recip_bal' :
      ((transfer to amount).run s).snd.storageMap 0 to =
        s.storageMap 0 to + amount := by
    have h_recip_bal' := h_recip_bal
    simp [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] at h_recip_bal'
    exact h_recip_bal'
  exact map_sum_transfer_eq
    (fun addr => s.storageMap 0 addr)
    (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)
    s.sender to amount h_ne h_sender_bal' h_recip_bal'
    (fun addr h1 h2 => h_other_bal.1 addr h1 h2)

/-- Corollary: for NoDup lists where sender and to each appear once,
    the total sum is exactly preserved by transfer. -/
theorem transfer_sum_preserved_unique (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 0 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (addrs : List Address)
  (h_sender_once : countOcc s.sender addrs = 1)
  (h_to_once : countOcc to addrs = 1) :
  (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
  = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h := transfer_sum_equation s to amount h_balance h_ne h_no_overflow addrs
  have h' : (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum + amount =
      (addrs.map (fun addr => s.storageMap 0 addr)).sum + amount := by
    have h'' := h
    simp [countOccU, h_sender_once, h_to_once] at h''
    exact (by
      calc
        (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum + amount
            = amount + (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum := by
                exact Verity.Core.Uint256.add_comm
                  ((addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum) amount
        _ = amount + (addrs.map (fun addr => s.storageMap 0 addr)).sum := h''
        _ = (addrs.map (fun addr => s.storageMap 0 addr)).sum + amount := by
            exact Verity.Core.Uint256.add_comm amount
              ((addrs.map (fun addr => s.storageMap 0 addr)).sum))
  exact Verity.Core.Uint256.add_right_cancel h'

/-! ## Deposit-Withdraw Inverse (Sum Level) -/

/-- Deposit then withdraw of the same amount preserves the balance sum for any list.
    This is stronger than the single-address cancellation in Correctness.lean. -/
theorem deposit_withdraw_sum_cancel (s : ContractState) (amount : Uint256)
  (h_no_overflow : (s.storageMap 0 s.sender : Nat) + (amount : Nat) < 2^256) :
  ∀ addrs : List Address,
    let s1 := ((deposit amount).run s).snd
    (addrs.map (fun addr => ((withdraw amount).run s1).snd.storageMap 0 addr)).sum
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  intro addrs
  let s1 := ((deposit amount).run s).snd
  have h_inc_raw := deposit_increases_balance s amount
  have h_inc :
      s1.storageMap 0 s.sender = s.storageMap 0 s.sender + amount := by
    have h_inc' := h_inc_raw
    simp [s1, Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] at h_inc'
    exact h_inc'
  have h_balance : s1.storageMap 0 s.sender ≥ amount := by
    have h_le : (amount : Nat) ≤ (s.storageMap 0 s.sender : Nat) + (amount : Nat) := by
      exact Nat.le_add_left _ _
    have h_inc_val : (s1.storageMap 0 s.sender : Nat) =
        (s.storageMap 0 s.sender : Nat) + (amount : Nat) := by
      have h_add :
          ((s.storageMap 0 s.sender + amount : Uint256) : Nat) =
            (s.storageMap 0 s.sender : Nat) + (amount : Nat) :=
        Verity.Core.Uint256.add_eq_of_lt h_no_overflow
      have h_inc_val' : (s1.storageMap 0 s.sender : Nat) =
          ((s.storageMap 0 s.sender + amount : Uint256) : Nat) := by
        exact congrArg (fun x => x.val) h_inc
      calc
        (s1.storageMap 0 s.sender : Nat)
            = ((s.storageMap 0 s.sender + amount : Uint256) : Nat) := h_inc_val'
        _ = (s.storageMap 0 s.sender : Nat) + (amount : Nat) := h_add
    -- Convert to Uint256 order
    simp [Verity.Core.Uint256.le_def, h_inc_val, h_le]
  have h_dep := deposit_sum_equation s amount addrs
  have h_wd := withdraw_sum_equation (s := s1) amount h_balance addrs
  have h_eq :
      (addrs.map (fun addr => ((withdraw amount).run s1).snd.storageMap 0 addr)).sum
        + countOccU s.sender addrs * amount
        = (addrs.map (fun addr => s.storageMap 0 addr)).sum
          + countOccU s.sender addrs * amount := by
    calc
      (addrs.map (fun addr => ((withdraw amount).run s1).snd.storageMap 0 addr)).sum
          + countOccU s.sender addrs * amount
          = (addrs.map (fun addr => s1.storageMap 0 addr)).sum := h_wd
      _ = (addrs.map (fun addr => s.storageMap 0 addr)).sum
          + countOccU s.sender addrs * amount := h_dep
  exact Verity.Core.Uint256.add_right_cancel h_eq

/-! ## Summary

All theorems fully proven with zero sorry:

Generic helpers (private):
1. countOcc — occurrence counting (def)
2. countOccU — countOcc cast to Uint256 (def)
3. countOcc_cons_eq — simplification for matching head
4. countOcc_cons_ne — simplification for non-matching head
5. countOccU_cons_eq — Uint256 version of countOcc_cons_eq
6. countOccU_cons_ne — Uint256 version of countOcc_cons_ne
7. map_sum_point_update — exact sum after adding: sum f' = sum f + count * delta
8. map_sum_point_decrease — exact sum after subtracting: sum f' + count * delta = sum f
9. map_sum_transfer_eq — exact conservation: sum f' + count(src)*d = sum f + count(dst)*d

Deposit conservation:
10. deposit_sum_equation — new_sum = old_sum + count(sender) * amount
11. deposit_sum_singleton_sender — for unique sender: new_sum = old_sum + amount

Withdraw conservation:
12. withdraw_sum_equation — new_sum + count(sender) * amount = old_sum
13. withdraw_sum_singleton_sender — for unique sender: new_sum + amount = old_sum

Transfer conservation:
14. transfer_sum_equation — new_sum + count(sender)*amt = old_sum + count(to)*amt
15. transfer_sum_preserved_unique — for unique sender & to: new_sum = old_sum
Composition:
16. deposit_withdraw_sum_cancel — deposit then withdraw preserves sum
-/

end Verity.Proofs.Ledger.Conservation
