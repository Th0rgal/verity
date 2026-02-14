/-
  Uint256 Arithmetic Lemmas for Unlink Proofs

  This file contains simple arithmetic lemmas needed to complete
  the Unlink security property proofs.

  These lemmas are straightforward and well-understood - they just
  need to be stated and proven for Uint256.
-/

import DumbContracts.Core

namespace DumbContracts.Specs.Unlink

open DumbContracts
open DumbContracts.Core.Uint256

/-! ## Addition Lemmas -/

-- Lemma: Adding a positive number increases the value (when no overflow)
theorem add_pos_gt {a : Uint256} {n : Nat} (h_pos : n > 0) (h_no_overflow : a.val + n < modulus) :
    a + (ofNat n) > a := by
  simp only [GT.gt, lt_def]
  have h_mod : (ofNat n : Uint256).val = n % modulus := rfl
  have h_n_lt : n < modulus := Nat.lt_of_le_of_lt (Nat.le_add_left n a.val) (by omega)
  have h_n_eq : n % modulus = n := Nat.mod_eq_of_lt h_n_lt
  have h_bval : (ofNat n : Uint256).val = n := by rw [h_mod, h_n_eq]
  have h_overflow' : a.val + (ofNat n : Uint256).val < modulus := by rw [h_bval]; exact h_no_overflow
  have h_add := add_eq_of_lt h_overflow'
  simp only [Coe.coe] at h_add
  rw [h_add, h_bval]
  exact Nat.lt_add_of_pos_right h_pos

-- Lemma: For non-empty lists, adding length increases value (without overflow)
theorem add_length_gt {a : Uint256} {α : Type} (xs : List α)
    (h_nonempty : xs.length > 0)
    (h_no_overflow : a.val + xs.length < modulus) :
    a + (ofNat xs.length) > a := by
  exact add_pos_gt h_nonempty h_no_overflow

/-! ## Inequality Lemmas -/

-- Lemma: If a + n = b and n > 0, then b > a
theorem eq_add_pos_implies_gt {a b : Uint256} {n : Nat}
    (h_eq : b = a + (ofNat n))
    (h_pos : n > 0)
    (h_no_overflow : a.val + n < modulus) :
    b > a := by
  rw [h_eq]
  exact add_pos_gt h_pos h_no_overflow

-- Lemma: Greater than is irreflexive
theorem gt_irrefl (a : Uint256) : ¬(a > a) := by
  simp only [GT.gt, lt_def]
  exact Nat.lt_irrefl a.val

-- Lemma: Greater than implies not equal
theorem gt_implies_ne {a b : Uint256} (h : a > b) : a ≠ b := by
  intro h_eq
  rw [h_eq] at h
  exact gt_irrefl b h

/-! ## Ordering Lemmas -/

-- Lemma: a + n ≥ a (adding any natural number maintains or increases value)
theorem add_nat_ge {a : Uint256} {n : Nat} (h_no_overflow : a.val + n < modulus) :
    a + (ofNat n) ≥ a := by
  simp only [GE.ge, le_def]
  have h_n_lt : n < modulus := Nat.lt_of_le_of_lt (Nat.le_add_left n a.val) (by omega)
  have h_bval : (ofNat n : Uint256).val = n := Nat.mod_eq_of_lt h_n_lt
  have h_overflow' : a.val + (ofNat n : Uint256).val < modulus := by rw [h_bval]; exact h_no_overflow
  have h_add := add_eq_of_lt h_overflow'
  simp only [Coe.coe] at h_add
  rw [h_add, h_bval]
  exact Nat.le_add_right a.val n

-- Lemma: If a = b + n, then a ≥ b
theorem eq_add_implies_ge {a b : Uint256} {n : Nat}
    (h_eq : a = b + (ofNat n))
    (h_no_overflow : b.val + n < modulus) :
    a ≥ b := by
  rw [h_eq]
  exact add_nat_ge h_no_overflow

end DumbContracts.Specs.Unlink
