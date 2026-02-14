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
  simp [LT.lt, lt_def]
  have h_add : (a + ofNat n).val = a.val + n := by
    exact add_eq_of_lt h_no_overflow
  simp [h_add]
  exact Nat.lt_add_of_pos_right h_pos

-- Lemma: Adding List.length is positive when list is non-empty
theorem list_length_pos {α : Type} (xs : List α) (h : xs.length > 0) :
    xs.length > 0 := h

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
  simp [LT.lt, lt_def]
  exact Nat.lt_irrefl a.val

-- Lemma: Greater than implies not equal
theorem gt_implies_ne {a b : Uint256} (h : a > b) : a ≠ b := by
  intro h_eq
  rw [h_eq] at h
  exact gt_irrefl b h

end DumbContracts.Specs.Unlink
