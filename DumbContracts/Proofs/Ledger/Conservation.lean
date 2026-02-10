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

import DumbContracts.Core
import DumbContracts.Examples.Ledger
import DumbContracts.Specs.Ledger.Spec
import DumbContracts.Specs.Ledger.Invariants
import DumbContracts.Proofs.Ledger.Basic

namespace DumbContracts.Proofs.Ledger.Conservation

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.Specs.Ledger
open DumbContracts.Proofs.Ledger

/-! ## Occurrence Counting -/

/-- Count occurrences of an element in a list. -/
def countOcc (target : Address) : List Address → Nat
  | [] => 0
  | a :: rest => (if a = target then 1 else 0) + countOcc target rest

private theorem countOcc_cons_eq (target : Address) (rest : List Address) :
  countOcc target (target :: rest) = 1 + countOcc target rest := by
  simp [countOcc]

private theorem countOcc_cons_ne (a target : Address) (rest : List Address) (h : a ≠ target) :
  countOcc target (a :: rest) = countOcc target rest := by
  simp [countOcc, h]

/-! ## Generic List Sum Lemma: Point Update -/

/-- When f' agrees with f except at target where f'(target) = f(target) + delta,
    then for any list: sum(map f') = sum(map f) + countOcc(target, list) * delta. -/
private theorem map_sum_point_update
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target + delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr) :
  ∀ addrs : List Address,
    (addrs.map f').sum = (addrs.map f).sum + countOcc target addrs * delta := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    rw [ih]
    by_cases h : a = target
    · rw [h, h_target, countOcc_cons_eq]
      have h_mul : (1 + countOcc target rest) * delta = delta + countOcc target rest * delta := by
        rw [Nat.add_mul]; simp
      rw [h_mul]
      rw [Nat.add_assoc (f target) delta]
      rw [← Nat.add_assoc delta _ _]
      rw [Nat.add_comm delta (List.map f rest).sum]
      rw [Nat.add_assoc (List.map f rest).sum delta]
      rw [← Nat.add_assoc (f target)]
    · rw [h_other a h, countOcc_cons_ne a target rest h]
      rw [Nat.add_assoc]

/-! ## Generic List Sum Lemma: Point Decrease -/

/-- When f' agrees with f except at target where f'(target) = f(target) - delta,
    and f(target) ≥ delta, then:
    sum(map f') + countOcc(target, list) * delta = sum(map f). -/
private theorem map_sum_point_decrease
  (f f' : Address → Uint256) (target : Address) (delta : Uint256)
  (h_target : f' target = f target - delta)
  (h_other : ∀ addr, addr ≠ target → f' addr = f addr)
  (h_bal : f target ≥ delta) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOcc target addrs * delta = (addrs.map f).sum := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    by_cases h : a = target
    · rw [h, h_target, countOcc_cons_eq]
      have h_mul : (1 + countOcc target rest) * delta = delta + countOcc target rest * delta := by
        rw [Nat.add_mul]; simp
      rw [h_mul]
      have h_cancel : f target - delta + delta = f target := Nat.sub_add_cancel h_bal
      -- LHS: ((f target - delta) + (rest.map f').sum) + (delta + countOcc target rest * delta)
      -- RHS: f target + (rest.map f).sum
      rw [Nat.add_assoc (f target - delta)]
      rw [← Nat.add_assoc (List.map f' rest).sum delta]
      rw [Nat.add_comm (List.map f' rest).sum delta]
      rw [Nat.add_assoc delta]
      rw [← Nat.add_assoc (f target - delta) delta]
      rw [h_cancel]
      rw [ih]
    · rw [h_other a h, countOcc_cons_ne a target rest h]
      rw [Nat.add_assoc]
      rw [ih]

/-! ## Generic List Sum Lemma: Transfer (Two-Point Update) -/

/-- When f' has f'(src) = f(src) - d and f'(dst) = f(dst) + d and agrees elsewhere,
    then sum(map f') + countOcc(src) * d = sum(map f) + countOcc(dst) * d. -/
private theorem map_sum_transfer_eq
  (f f' : Address → Uint256) (src dst : Address) (d : Uint256)
  (h_ne : src ≠ dst)
  (h_src : f' src = f src - d)
  (h_dst : f' dst = f dst + d)
  (h_other : ∀ addr, addr ≠ src → addr ≠ dst → f' addr = f addr)
  (h_bal : f src ≥ d) :
  ∀ addrs : List Address,
    (addrs.map f').sum + countOcc src addrs * d
    = (addrs.map f).sum + countOcc dst addrs * d := by
  intro addrs
  induction addrs with
  | nil => simp [countOcc]
  | cons a rest ih =>
    simp only [List.map, List.sum_cons]
    by_cases ha_s : a = src
    · rw [ha_s, h_src, countOcc_cons_eq]
      rw [countOcc_cons_ne src dst rest h_ne]
      have h_mul : (1 + countOcc src rest) * d = d + countOcc src rest * d := by
        rw [Nat.add_mul]; simp
      rw [h_mul]
      have h_cancel : f src - d + d = f src := Nat.sub_add_cancel h_bal
      rw [Nat.add_assoc (f src - d)]
      rw [← Nat.add_assoc (List.map f' rest).sum d]
      rw [Nat.add_comm (List.map f' rest).sum d]
      rw [Nat.add_assoc d]
      rw [← Nat.add_assoc (f src - d) d]
      rw [h_cancel]
      rw [ih]
      rw [Nat.add_assoc]
    · by_cases ha_d : a = dst
      · rw [ha_d, h_dst]
        have h_ne_sym : dst ≠ src := Ne.symm h_ne
        rw [countOcc_cons_ne dst src rest h_ne_sym, countOcc_cons_eq]
        have h_mul : (1 + countOcc dst rest) * d = d + countOcc dst rest * d := by
          rw [Nat.add_mul]; simp
        rw [h_mul]
        rw [Nat.add_assoc (f dst + d) _ _, Nat.add_assoc (f dst) d _,
            Nat.add_assoc (f dst) _ _]
        congr 1
        rw [ih]
        rw [Nat.add_left_comm]
      · rw [h_other a ha_s ha_d, countOcc_cons_ne a src rest ha_s, countOcc_cons_ne a dst rest ha_d]
        rw [Nat.add_assoc, Nat.add_assoc]
        exact congrArg (f a + ·) ih

/-! ## Deposit: Exact Sum Equation -/

/-- Exact sum relationship after deposit: the new sum equals the old sum plus
    count(sender, addrs) * amount. Each occurrence of the sender in the list
    contributes an additional `amount` to the sum. -/
theorem deposit_sum_equation (s : ContractState) (amount : Uint256) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)).sum
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum + countOcc s.sender addrs * amount := by
  have h_inc := deposit_increases_balance s amount
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
  rw [h_once] at h; simp at h; exact h

/-! ## Withdraw: Exact Sum Equation -/

/-- Exact sum relationship after withdraw (when balance sufficient):
    new_sum + count(sender, addrs) * amount = old_sum.
    Each occurrence of the sender in the list contributes `amount` less to the new sum. -/
theorem withdraw_sum_equation (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum
      + countOcc s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h_dec := withdraw_decreases_balance s amount h_balance
  have h_other : ∀ addr, addr ≠ s.sender →
    ((withdraw amount).run s).snd.storageMap 0 addr = s.storageMap 0 addr := by
    intro addr h_ne
    have h_spec := withdraw_meets_spec s amount h_balance
    simp [withdraw_spec] at h_spec
    exact h_spec.2.1 addr h_ne
  exact map_sum_point_decrease
    (fun addr => s.storageMap 0 addr)
    (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)
    s.sender amount h_dec h_other h_balance

/-- Corollary: for a list where sender appears exactly once, withdraw removes exactly `amount`. -/
theorem withdraw_sum_singleton_sender (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount)
  (addrs : List Address) (h_once : countOcc s.sender addrs = 1) :
  (addrs.map (fun addr => ((withdraw amount).run s).snd.storageMap 0 addr)).sum + amount
  = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h := withdraw_sum_equation s amount h_balance addrs
  rw [h_once] at h; simp at h; exact h

/-! ## Transfer: Exact Sum Conservation Equation -/

/-- Exact sum conservation equation for transfer:
    new_sum + count(sender, addrs) * amount = old_sum + count(to, addrs) * amount.

    This is the fundamental conservation law for Ledger transfer: each occurrence
    of the sender in the list loses `amount`, and each occurrence of the recipient
    gains `amount`. The equation holds exactly (not just as an inequality). -/
theorem transfer_sum_equation (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
      + countOcc s.sender addrs * amount
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum
      + countOcc to addrs * amount := by
  have h_spec := transfer_meets_spec s to amount h_balance h_ne
  simp [transfer_spec] at h_spec
  obtain ⟨h_sender_bal, h_recip_bal, h_other_bal, _, _, _, _, _⟩ := h_spec
  exact map_sum_transfer_eq
    (fun addr => s.storageMap 0 addr)
    (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)
    s.sender to amount h_ne h_sender_bal h_recip_bal
    (fun addr h1 h2 => h_other_bal addr h1 h2) h_balance

/-- Corollary: for NoDup lists where sender and to each appear once,
    the total sum is exactly preserved by transfer. -/
theorem transfer_sum_preserved_unique (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to)
  (addrs : List Address)
  (h_sender_once : countOcc s.sender addrs = 1)
  (h_to_once : countOcc to addrs = 1) :
  (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
  = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  have h := transfer_sum_equation s to amount h_balance h_ne addrs
  rw [h_sender_once, h_to_once] at h; simp at h; exact h

/-- Corollary: the new sum is bounded by old_sum + count(to) * amount. -/
theorem transfer_sum_bounded (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 0 s.sender >= amount) (h_ne : s.sender ≠ to) :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
    ≤ (addrs.map (fun addr => s.storageMap 0 addr)).sum + countOcc to addrs * amount := by
  intro addrs
  have h := transfer_sum_equation s to amount h_balance h_ne addrs
  calc (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
      ≤ (addrs.map (fun addr => ((transfer to amount).run s).snd.storageMap 0 addr)).sum
        + countOcc s.sender addrs * amount := Nat.le_add_right _ _
    _ = (addrs.map (fun addr => s.storageMap 0 addr)).sum + countOcc to addrs * amount := h

/-! ## Deposit-Withdraw Inverse (Sum Level) -/

/-- Deposit then withdraw of the same amount preserves the balance sum for any list.
    This is stronger than the single-address cancellation in Correctness.lean. -/
theorem deposit_withdraw_sum_cancel (s : ContractState) (amount : Uint256) :
  ∀ addrs : List Address,
    let s1 := ((deposit amount).run s).snd
    (addrs.map (fun addr => ((withdraw amount).run s1).snd.storageMap 0 addr)).sum
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum := by
  intro addrs
  simp only [deposit, withdraw, msgSender, getMapping, setMapping, balances,
    DumbContracts.require, DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [Nat.add_sub_cancel]
  -- After simp, the nested if-then-else doesn't fully collapse.
  -- Show the mapping function is extensionally equal to s.storageMap 0.
  have h_ext : ∀ addr : Address,
    (if addr = s.sender then s.storageMap 0 s.sender
     else if addr = s.sender then s.storageMap 0 s.sender + amount
     else s.storageMap 0 addr) = s.storageMap 0 addr := by
    intro addr
    by_cases h : addr = s.sender
    · simp [h]
    · simp [h]
  simp [h_ext]

/-! ## Summary

All theorems fully proven with zero sorry:

Generic helpers (private):
1. countOcc — occurrence counting
2. countOcc_cons_eq — simplification for matching head
3. countOcc_cons_ne — simplification for non-matching head
4. map_sum_point_update — exact sum after adding: sum f' = sum f + count * delta
5. map_sum_point_decrease — exact sum after subtracting: sum f' + count * delta = sum f
6. map_sum_transfer_eq — exact conservation: sum f' + count(src)*d = sum f + count(dst)*d

Deposit conservation:
7. deposit_sum_equation — new_sum = old_sum + count(sender) * amount
8. deposit_sum_singleton_sender — for unique sender: new_sum = old_sum + amount

Withdraw conservation:
9. withdraw_sum_equation — new_sum + count(sender) * amount = old_sum
10. withdraw_sum_singleton_sender — for unique sender: new_sum + amount = old_sum

Transfer conservation:
11. transfer_sum_equation — new_sum + count(sender)*amt = old_sum + count(to)*amt
12. transfer_sum_preserved_unique — for unique sender & to: new_sum = old_sum
13. transfer_sum_bounded — new_sum ≤ old_sum + count(to) * amount

Composition:
14. deposit_withdraw_sum_cancel — deposit then withdraw preserves sum
-/

end DumbContracts.Proofs.Ledger.Conservation
