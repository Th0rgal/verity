/-
  Sum helper functions for proving sum properties.

  This module provides utilities for summing balances over finite address sets.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Specs.Common

open Verity
open Verity.Core
open Verity.EVM.Uint256

/-- Sum balances from a mapping over a finite set of addresses -/
def sumBalances (slot : Nat) (addrs : FiniteAddressSet) (balances : Nat → Address → Uint256) : Uint256 :=
  addrs.addresses.sum (fun addr => balances slot addr)

/-- Invariant: only known addresses have non-zero balances -/
def balancesFinite (slot : Nat) (s : ContractState) : Prop :=
  ∀ addr, addr ∉ (s.knownAddresses slot).addresses.elements →
    s.storageMap slot addr = 0

/-! ## Foldl Helper Lemmas -/

/-- Helper: foldl of addition over zeros starting from zero gives zero -/
private theorem foldl_add_zero_acc (l : List α) (f : α → Uint256)
    (h : ∀ x ∈ l, f x = 0) (acc : Uint256) :
    l.foldl (fun a x => a + f x) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = 0 := h a (by simp)
    rw [ha, Uint256.add_zero]
    exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) acc

/-- Helper: foldl with non-zero accumulator equals accumulator plus foldl from zero.
    This is the key lemma for decomposing foldl sums. -/
private theorem foldl_acc_comm (l : List α) (f : α → Uint256) (acc : Uint256) :
    l.foldl (fun a x => a + f x) acc = acc + l.foldl (fun a x => a + f x) 0 := by
  induction l generalizing acc with
  | nil =>
    simp only [List.foldl]
    rw [Uint256.add_zero]
  | cons a t ih =>
    simp only [List.foldl]
    rw [Uint256.zero_add]
    rw [ih (acc + f a)]
    rw [ih (f a)]
    simp [Uint256.add_assoc]

/-- Helper: foldl is invariant under pointwise-equal functions on list elements -/
private theorem foldl_congr (l : List α) (f g : α → Uint256) (acc : Uint256)
    (h : ∀ x ∈ l, f x = g x) :
    l.foldl (fun a x => a + f x) acc = l.foldl (fun a x => a + g x) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl]
    have ha : f a = g a := h a (by simp)
    rw [ha]
    exact ih (acc + g a) (fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ## Sum Properties -/

/-- Helper: sum is preserved when adding to known address -/
theorem sumBalances_insert_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256}
    (h : addr ∈ addrs.addresses.elements) :
    sumBalances slot (addrs.insert addr) balances = sumBalances slot addrs balances := by
  unfold sumBalances FiniteAddressSet.insert FiniteSet.insert
  simp [h]

/-- Helper: sum increases when adding balance to new address -/
theorem sumBalances_insert_new {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {amount : Uint256}
    (h : addr ∉ addrs.addresses.elements)
    (_h_zero : balances slot addr = 0) :
    sumBalances slot (addrs.insert addr) (fun s a =>
      if s == slot && a == addr then amount else balances s a) =
    add (sumBalances slot addrs balances) amount := by
  unfold sumBalances FiniteSet.sum
  -- After insert_of_not_mem, elements become addr :: addrs.addresses.elements
  rw [FiniteAddressSet.insert, FiniteSet.insert_of_not_mem addr addrs.addresses h]
  simp only [List.foldl]
  -- The head element is addr, so the if-condition is true: simplify 0 + amount to amount
  simp only [BEq.beq, decide_true, Bool.true_and, ite_true, Uint256.zero_add]
  -- Now goal: foldl (updated) amount rest = add (foldl (original) 0 rest) amount
  -- Step 1: use foldl_acc_comm to extract amount from the accumulator
  rw [foldl_acc_comm]
  -- Now goal: amount + foldl (updated) 0 rest = add (foldl (original) 0 rest) amount
  -- Step 2: show updated and original foldl agree on rest elements (none equal addr)
  have h_eq := foldl_congr addrs.addresses.elements
    (fun a => if decide (a = addr) = true then amount else balances slot a)
    (fun a => balances slot a)
    0
    (fun x hx => by
      have hne : x ≠ addr := fun heq => h (heq ▸ hx)
      simp [hne])
  -- Step 3: rewrite LHS foldl to match RHS foldl, then use add_comm
  -- h_eq equates the two foldl forms. Unfold HAdd/add so both sides use same notation.
  show amount + List.foldl (fun a x => a + (fun a => if decide (a = addr) = true then amount else balances slot a) x) 0
      addrs.addresses.elements =
    Uint256.add (List.foldl (fun acc x => acc + balances slot x) 0 addrs.addresses.elements) amount
  rw [h_eq]
  exact Uint256.add_comm amount _

/-- Helper: a + (b - c) = (a + b) - c in modular arithmetic (Z/2^256Z is a group) -/
private theorem add_sub_assoc (a b c : Uint256) : a + (b - c) = (a + b) - c := by
  -- Strategy: show both sides + c give the same result, then use add_right_cancel
  have lhs_eq : (a + (b - c)) + c = a + b := by
    have := Uint256.sub_add_cancel_left b c  -- (b - c) + c = b
    calc (a + (b - c)) + c
        = a + ((b - c) + c) := by
          rw [Uint256.add_assoc]
      _ = a + b := by rw [this]
  have rhs_eq : ((a + b) - c) + c = a + b := Uint256.sub_add_cancel_left (a + b) c
  exact Uint256.add_right_cancel (by rw [lhs_eq, rhs_eq])

/-- Helper: for a nodup list containing target, replacing target's value with new_val
    changes the foldl sum by (new_val - old_val):
    foldl(updated) = (foldl(original) - old_val) + new_val -/
private theorem foldl_replace_one (l : List α) [DecidableEq α]
    (f g : α → Uint256) (target : α) (new_val : Uint256)
    (h_mem : target ∈ l) (h_nodup : l.Nodup)
    (h_target : g target = new_val)
    (h_other : ∀ x ∈ l, x ≠ target → g x = f x) :
    l.foldl (fun acc x => acc + g x) 0 =
    (l.foldl (fun acc x => acc + f x) 0) - (f target) + new_val := by
  induction l with
  | nil => cases h_mem
  | cons a t ih =>
    simp only [List.foldl, Uint256.zero_add]
    have h_nodup_t := (List.nodup_cons.mp h_nodup).2
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      subst heq
      rw [h_target]
      -- target ∉ t by nodup, so g = f on tail
      have h_not_mem : target ∉ t := (List.nodup_cons.mp h_nodup).1
      -- Extract accumulator from LHS
      rw [foldl_acc_comm t g new_val]
      -- On tail, g agrees with f
      rw [foldl_congr t g f 0
        (fun x hx => h_other x (List.mem_cons_of_mem target hx)
          (fun heq => h_not_mem (heq ▸ hx)))]
      -- Extract accumulator from RHS
      rw [foldl_acc_comm t f (f target)]
      -- (f target + X) - f target + new_val = new_val + X
      -- sub_add_cancel: (a + b) - b = a => (f target + X) - f target = X
      -- But we need the subtraction to reduce first
      have h_cancel := Uint256.sub_add_cancel (f target) (List.foldl (fun a x => a + f x) 0 t)
      -- h_cancel : (f target + foldl f 0 t) - (foldl f 0 t) = f target
      -- Actually sub_add_cancel says (a + b - b) = a, so Uint256.sub_add_cancel a b : a + b - b = a
      -- We need: (f target + X) - (f target) = X
      -- That's: (X + f target) - f target = X by sub_add_cancel, after comm
      rw [Uint256.add_comm (f target) (List.foldl (fun a x => a + f x) 0 t)]
      rw [Uint256.sub_add_cancel]
      exact Uint256.add_comm new_val _
    | inr hmem =>
      have h_ne : a ≠ target := by
        intro heq
        exact (List.nodup_cons.mp h_nodup).1 (heq ▸ hmem)
      rw [h_other a (by simp) h_ne]
      rw [foldl_acc_comm t g (f a)]
      rw [foldl_acc_comm t f (f a)]
      rw [ih hmem h_nodup_t (fun x hx hne => h_other x (List.mem_cons_of_mem a hx) hne)]
      -- Goal: f a + (foldl f 0 t - f target + new_val)
      --     = (f a + foldl f 0 t) - f target + new_val
      -- Rewrite using add_sub_assoc: a + (b - c) = (a + b) - c
      -- First isolate: f a + (X - Y + Z) = (f a + X) - Y + Z
      -- = f a + ((X - Y) + Z) = ((f a + (X - Y)) + Z) = (((f a + X) - Y) + Z)
      rw [← Uint256.add_assoc (f a) _ new_val]
      rw [add_sub_assoc (f a) (List.foldl (fun a x => a + f x) 0 t) (f target)]

/-- Helper: sum changes when updating balance of existing address -/
theorem sumBalances_update_existing {slot : Nat} {addr : Address} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} {old_amount new_amount : Uint256}
    (h : addr ∈ addrs.addresses.elements)
    (h_old : balances slot addr = old_amount) :
    sumBalances slot addrs (fun s a =>
      if s == slot && a == addr then new_amount else balances s a) =
    add (sub (sumBalances slot addrs balances) old_amount) new_amount := by
  unfold sumBalances FiniteSet.sum
  -- Apply foldl_replace_one with g = updated balances, f = original balances
  -- First rewrite the LHS foldl lambda to separate slot/addr BEq
  have h_lhs_eq : ∀ acc,
    List.foldl (fun acc x => acc + if slot == slot && x == addr then new_amount else balances slot x)
      acc addrs.addresses.elements =
    List.foldl (fun acc x => acc + (fun a => if slot == slot && a == addr then new_amount else balances slot a) x)
      acc addrs.addresses.elements := by
    intro acc; rfl
  rw [h_lhs_eq 0]
  have h_result := foldl_replace_one
    addrs.addresses.elements
    (fun a => balances slot a)
    (fun a => if slot == slot && a == addr then new_amount else balances slot a)
    addr new_amount
    h addrs.addresses.nodup
    (by simp [BEq.beq])
    (fun x _ hne => by simp [BEq.beq, hne])
  -- h_result has (fun a => balances slot a) addr which beta-reduces to balances slot addr
  simp only [] at h_result
  rw [h_old] at h_result
  -- h_result uses HSub/HAdd: _ - _ + _, goal uses add (sub ...) ...
  -- These are definitionally equal
  exact h_result

/-- Helper: sumBalances equals zero when all balances are zero -/
theorem sumBalances_zero_of_all_zero {slot : Nat} {addrs : FiniteAddressSet}
    {balances : Nat → Address → Uint256} :
    (∀ addr ∈ addrs.addresses.elements, balances slot addr = 0) →
    sumBalances slot addrs balances = 0 := by
  intro h
  unfold sumBalances FiniteSet.sum
  exact foldl_add_zero_acc addrs.addresses.elements (fun addr => balances slot addr) h 0

/-- Helper: balancesFinite preserved by setMapping (deposit) -/
theorem balancesFinite_preserved_deposit {slot : Nat} (s : ContractState)
    (addr : Address) (amount : Uint256) :
    balancesFinite slot s →
    balancesFinite slot { s with
      storageMap := fun s' a =>
        if s' == slot && a == addr then amount else s.storageMap s' a,
      knownAddresses := fun s' =>
        if s' == slot then (s.knownAddresses s').insert addr
        else s.knownAddresses s' } := by
  intro h_finite
  unfold balancesFinite
  intro addr' h_not_in
  -- The new knownAddresses at slot is (s.knownAddresses slot).insert addr
  -- h_not_in : addr' ∉ (if slot == slot then ... else ...).addresses.elements
  -- Since slot == slot is true, this simplifies to addr' ∉ ((s.knownAddresses slot).insert addr).addresses.elements
  simp only [BEq.beq, decide_true, ite_true] at h_not_in
  -- By mem_elements_insert: addr' ∉ insert means addr' ≠ addr ∧ addr' ∉ original
  rw [FiniteAddressSet.insert] at h_not_in
  have h_not_or := mt (FiniteSet.mem_elements_insert addr' addr (s.knownAddresses slot).addresses).mpr h_not_in
  simp only [not_or] at h_not_or
  obtain ⟨h_ne, h_not_orig⟩ := h_not_or
  -- Since addr' ≠ addr, the storageMap if-condition evaluates to false
  simp only [BEq.beq, decide_true, Bool.true_and]
  have h_ne' : ¬(decide (addr' = addr) = true) := by simp [h_ne]
  simp [h_ne']
  -- Now the goal reduces to s.storageMap slot addr' = 0, which follows from h_finite
  exact h_finite addr' h_not_orig

end Verity.Specs.Common
