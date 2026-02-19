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

import Verity.Proofs.Ledger.Basic
import Verity.Proofs.Stdlib.ListSum

namespace Verity.Proofs.Ledger.Conservation

open Verity
open Verity.Examples.Ledger
open Verity.Specs.Ledger
open Verity.Proofs.Ledger
open Verity.Proofs.Stdlib.ListSum (countOcc countOccU countOcc_cons_eq countOcc_cons_ne
  countOccU_cons_eq countOccU_cons_ne map_sum_point_update map_sum_point_decrease map_sum_transfer_eq)
open Verity.Stdlib.Math (MAX_UINT256)

/-! ## Deposit: Exact Sum Equation -/

/-- Exact sum relationship after deposit: the new sum equals the old sum plus
    count(sender, addrs) * amount. Each occurrence of the sender in the list
    contributes an additional `amount` to the sum. -/
theorem deposit_sum_equation (s : ContractState) (amount : Uint256)
  :
  ∀ addrs : List Address,
    (addrs.map (fun addr => ((deposit amount).run s).snd.storageMap 0 addr)).sum
    = (addrs.map (fun addr => s.storageMap 0 addr)).sum + countOccU s.sender addrs * amount := by
  have h_inc :
      ((deposit amount).run s).snd.storageMap 0 s.sender =
        s.storageMap 0 s.sender + amount := by
    simpa [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] using deposit_increases_balance s amount
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
    simpa [Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] using h_recip_bal
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
  have h_inc :
      s1.storageMap 0 s.sender = s.storageMap 0 s.sender + amount := by
    simpa [s1, Verity.EVM.Uint256.add, Verity.Core.Uint256.add,
      HAdd.hAdd, Verity.Core.Uint256.add_comm] using deposit_increases_balance s amount
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

All 7 theorems fully proven with zero sorry.
Generic list-sum helpers (countOcc, map_sum_point_update, map_sum_point_decrease,
map_sum_transfer_eq) are imported from Verity.Proofs.Stdlib.ListSum.

Deposit conservation:
1. deposit_sum_equation — new_sum = old_sum + count(sender) * amount
2. deposit_sum_singleton_sender — for unique sender: new_sum = old_sum + amount

Withdraw conservation:
3. withdraw_sum_equation — new_sum + count(sender) * amount = old_sum
4. withdraw_sum_singleton_sender — for unique sender: new_sum + amount = old_sum

Transfer conservation:
5. transfer_sum_equation — new_sum + count(sender)*amt = old_sum + count(to)*amt
6. transfer_sum_preserved_unique — for unique sender & to: new_sum = old_sum

Composition:
7. deposit_withdraw_sum_cancel — deposit then withdraw preserves sum
-/

end Verity.Proofs.Ledger.Conservation
