/-
  Correctness proofs for all safe arithmetic operations in the Math stdlib.

  Covers safeAdd, safeSub, safeMul, and safeDiv: each operation returns
  the correct result when within bounds and returns none otherwise.
-/

import Verity.Core
import Verity.Stdlib.Math

namespace Verity.Proofs.Stdlib.Math

open Verity
open Verity.Stdlib.Math

/-! ## mulDiv / wad Helpers -/

private theorem modulus_eq_max_succ :
    Verity.Core.Uint256.modulus = MAX_UINT256 + 1 := by
  symm
  exact Verity.Core.Uint256.max_uint256_succ_eq_modulus

private theorem lt_modulus_of_le_max {n : Nat} (h : n ≤ MAX_UINT256) :
    n < Verity.Core.Uint256.modulus := by
  calc
    n < MAX_UINT256 + 1 := Nat.lt_succ_of_le h
    _ = Verity.Core.Uint256.modulus := by simp [modulus_eq_max_succ]

/-- `mulDivDown` agrees with exact natural-number division when the numerator does not wrap. -/
theorem mulDivDown_nat_eq (a b c : Uint256) (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) =
      if (c : Nat) = 0 then 0 else ((a : Nat) * (b : Nat)) / (c : Nat) := by
  have hMulLt : (a : Nat) * (b : Nat) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hMul
  have hProd : ((a * b : Uint256) : Nat) = (a : Nat) * (b : Nat) :=
    Verity.Core.Uint256.mul_eq_of_lt hMulLt
  by_cases hZero : (c : Nat) = 0
  · simp [mulDivDown, HDiv.hDiv, Verity.Core.Uint256.div, hZero]
  · have hCPos : 0 < (c : Nat) := Nat.pos_of_ne_zero hZero
    have hDivLt : ((a : Nat) * (b : Nat)) / (c : Nat) < Verity.Core.Uint256.modulus := by
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hMulLt
    calc
      (mulDivDown a b c : Nat)
          = (((a * b : Uint256) : Nat) / (c : Nat)) % Verity.Core.Uint256.modulus := by
              simp [mulDivDown, HDiv.hDiv, Verity.Core.Uint256.div, hZero]
      _ = (((a : Nat) * (b : Nat)) / (c : Nat)) % Verity.Core.Uint256.modulus := by
              simp [hProd]
      _ = ((a : Nat) * (b : Nat)) / (c : Nat) := Nat.mod_eq_of_lt hDivLt
      _ = dite ((c : Nat) = 0) (fun _ => 0) (fun _ => ((a : Nat) * (b : Nat)) / (c : Nat)) := by
              simp [hZero]

/-- Rounding down never overshoots the exact numerator product. -/
theorem mulDivDown_mul_le (a b c : Uint256) (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) * (c : Nat) ≤ (a : Nat) * (b : Nat) := by
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a b c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a b c hMul]
    simp [hZero]
    exact Nat.div_mul_le_self _ _

/-- `mulDivDown` is monotone in its left numerator operand when the product stays exact. -/
theorem mulDivDown_monotone_left (a₁ a₂ b c : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hMul : (a₂ : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (mulDivDown a₁ b c : Nat) ≤ (mulDivDown a₂ b c : Nat) := by
  have hMul₁ : (a₁ : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.mul_le_mul_right _ hA) hMul
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a₁ b c hMul₁, mulDivDown_nat_eq a₂ b c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a₁ b c hMul₁, mulDivDown_nat_eq a₂ b c hMul]
    simp [hZero]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hA)

/-- `mulDivDown` is monotone in its right numerator operand when the product stays exact. -/
theorem mulDivDown_monotone_right (a b₁ b₂ c : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hMul : (a : Nat) * (b₂ : Nat) ≤ MAX_UINT256) :
    (mulDivDown a b₁ c : Nat) ≤ (mulDivDown a b₂ c : Nat) := by
  have hMul₁ : (a : Nat) * (b₁ : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.mul_le_mul_left _ hB) hMul
  by_cases hZero : (c : Nat) = 0
  · rw [mulDivDown_nat_eq a b₁ c hMul₁, mulDivDown_nat_eq a b₂ c hMul]
    simp [hZero]
  · rw [mulDivDown_nat_eq a b₁ c hMul₁, mulDivDown_nat_eq a b₂ c hMul]
    simp [hZero]
    exact Nat.div_le_div_right (Nat.mul_le_mul_left _ hB)

/-- `mulDivUp` agrees with exact ceil-division when the widened numerator does not wrap. -/
theorem mulDivUp_nat_eq (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b c : Nat) = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hMulLt : (a : Nat) * (b : Nat) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hMul
  have hProd : ((a * b : Uint256) : Nat) = (a : Nat) * (b : Nat) :=
    Verity.Core.Uint256.mul_eq_of_lt hMulLt
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  have hOneLe : (1 : Nat) ≤ (c : Nat) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hCVal)
  have hSub : ((c - 1 : Uint256) : Nat) = (c : Nat) - 1 :=
    Verity.Core.Uint256.sub_eq_of_le hOneLe
  have hNumLt : (a : Nat) * (b : Nat) + ((c : Nat) - 1) < Verity.Core.Uint256.modulus :=
    lt_modulus_of_le_max hNum
  have hNumerator :
      (((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) =
        (a : Nat) * (b : Nat) + ((c : Nat) - 1) := by
    have hAdd :
        (((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) =
          ((a * b : Uint256) : Nat) + ((c - 1 : Uint256) : Nat) :=
      Verity.Core.Uint256.add_eq_of_lt (by simpa [hProd, hSub] using hNumLt)
    simpa [hProd, hSub] using hAdd
  have hDivLt :
      (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) < Verity.Core.Uint256.modulus := by
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hNumLt
  calc
    (mulDivUp a b c : Nat)
        = ((((a * b : Uint256) + (c - 1 : Uint256) : Uint256) : Nat) / (c : Nat)) %
            Verity.Core.Uint256.modulus := by
              simp [mulDivUp, HDiv.hDiv, Verity.Core.Uint256.div, hCVal]
    _ = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) % Verity.Core.Uint256.modulus := by
            simp [hNumerator]
    _ = (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat) := Nat.mod_eq_of_lt hDivLt

/-- The ceil helper never rounds below the floor helper when both are exact. -/
theorem mulDivDown_le_mulDivUp (a b c : Uint256)
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivDown a b c : Nat) ≤ (mulDivUp a b c : Nat) := by
  have hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.le_add_right _ _) hNum
  have hCVal : (c : Nat) ≠ 0 := by
    intro h
    apply hC
    exact Verity.Core.Uint256.ext (by simpa using h)
  rw [mulDivDown_nat_eq a b c hMul, mulDivUp_nat_eq a b c hC hNum]
  simp [hCVal]
  apply Nat.div_le_div_right
  exact Nat.le_add_right _ _

/-- `mulDivUp` is monotone in its left numerator operand when the widened numerator stays exact. -/
theorem mulDivUp_monotone_left (a₁ a₂ b c : Uint256)
    (hA : (a₁ : Nat) ≤ (a₂ : Nat))
    (hC : c ≠ 0)
    (hNum : (a₂ : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a₁ b c : Nat) ≤ (mulDivUp a₂ b c : Nat) := by
  have hNum₁ : (a₁ : Nat) * (b : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _) hNum
  rw [mulDivUp_nat_eq a₁ b c hC hNum₁, mulDivUp_nat_eq a₂ b c hC hNum]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _)

/-- `mulDivUp` is monotone in its right numerator operand when the widened numerator stays exact. -/
theorem mulDivUp_monotone_right (a b₁ b₂ c : Uint256)
    (hB : (b₁ : Nat) ≤ (b₂ : Nat))
    (hC : c ≠ 0)
    (hNum : (a : Nat) * (b₂ : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256) :
    (mulDivUp a b₁ c : Nat) ≤ (mulDivUp a b₂ c : Nat) := by
  have hNum₁ : (a : Nat) * (b₁ : Nat) + ((c : Nat) - 1) ≤ MAX_UINT256 := by
    exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hB) _) hNum
  rw [mulDivUp_nat_eq a b₁ c hC hNum₁, mulDivUp_nat_eq a b₂ c hC hNum]
  exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ hB) _)

/-- `wMulDown` is `mulDivDown` specialized to the canonical wad scale. -/
theorem wMulDown_nat_eq (a b : Uint256)
    (hMul : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
    (wMulDown a b : Nat) = ((a : Nat) * (b : Nat)) / (WAD : Nat) := by
  rw [wMulDown_def, mulDivDown_nat_eq a b WAD hMul]
  simp [WAD_val]

/-- `wDivUp` is `mulDivUp` specialized to the canonical wad scale. -/
theorem wDivUp_nat_eq (a b : Uint256)
    (hB : b ≠ 0)
    (hNum : (a : Nat) * (WAD : Nat) + ((b : Nat) - 1) ≤ MAX_UINT256) :
    (wDivUp a b : Nat) = (((a : Nat) * (WAD : Nat)) + ((b : Nat) - 1)) / (b : Nat) := by
  rw [wDivUp_def, mulDivUp_nat_eq a WAD b hB hNum]

/-! ## safeAdd Correctness -/

/-- safeAdd returns the sum when no overflow occurs. -/
theorem safeAdd_some (a b : Uint256) (h : (a : Nat) + (b : Nat) ≤ MAX_UINT256) :
  safeAdd a b = some (a + b) := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd returns none on overflow. -/
theorem safeAdd_none (a b : Uint256) (h : (a : Nat) + (b : Nat) > MAX_UINT256) :
  safeAdd a b = none := by
  simp [safeAdd, h]

/-- safeAdd with zero on the left returns the other operand (when within bounds). -/
theorem safeAdd_zero_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeAdd 0 b = some b := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd with zero on the right returns the other operand (when within bounds). -/
theorem safeAdd_zero_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeAdd a 0 = some a := by
  simp [safeAdd, Nat.not_lt.mpr h]

/-- safeAdd is commutative. -/
theorem safeAdd_comm (a b : Uint256) :
  safeAdd a b = safeAdd b a := by
  simp [safeAdd, Nat.add_comm]

/-- safeAdd result is always bounded by MAX_UINT256 when successful. -/
theorem safeAdd_result_bounded (a b : Uint256) (c : Uint256)
  (_h : safeAdd a b = some c) : c ≤ MAX_UINT256 :=
  Verity.Core.Uint256.val_le_max c

/-! ## safeSub Correctness -/

/-- safeSub returns the difference when no underflow occurs. -/
theorem safeSub_some (a b : Uint256) (h : (a : Nat) ≥ (b : Nat)) :
  safeSub a b = some (a - b) := by
  simp [safeSub, Nat.not_lt.mpr h]

/-- safeSub returns none on underflow. -/
theorem safeSub_none (a b : Uint256) (h : (b : Nat) > (a : Nat)) :
  safeSub a b = none := by
  simp [safeSub, h]

/-- safeSub of zero from any value is always safe. -/
theorem safeSub_zero (a : Uint256) :
  safeSub a 0 = some a := by
  simp [safeSub]

/-- safeSub of a value from itself returns zero. -/
theorem safeSub_self (a : Uint256) :
  safeSub a a = some 0 := by
  simp [safeSub]

/-- safeSub result never exceeds the minuend. -/
theorem safeSub_result_le (a b : Uint256) (c : Uint256)
  (h : safeSub a b = some c) : c ≤ a := by
  by_cases hlt : (b : Nat) > (a : Nat)
  · simp [safeSub, hlt] at h
  · have hle' : (b : Nat) ≤ (a : Nat) := Nat.not_lt.mp hlt
    simp [safeSub, hlt] at h
    have hc : a - b = c := by cases h; rfl
    have hsub : ((a - b : Uint256) : Nat) = (a : Nat) - (b : Nat) :=
      Verity.Core.Uint256.sub_eq_of_le hle'
    simp [hc.symm, hsub]

/-! ## safeMul Correctness -/

/-- safeMul returns the product when no overflow occurs. -/
theorem safeMul_some (a b : Uint256) (h : (a : Nat) * (b : Nat) ≤ MAX_UINT256) :
  safeMul a b = some (a * b) := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul returns none on overflow. -/
theorem safeMul_none (a b : Uint256) (h : (a : Nat) * (b : Nat) > MAX_UINT256) :
  safeMul a b = none := by
  simp [safeMul, h]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_left (b : Uint256) :
  safeMul 0 b = some 0 := by
  simp [safeMul]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_right (a : Uint256) :
  safeMul a 0 = some 0 := by
  simp [safeMul]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_left (b : Uint256) (h : (b : Nat) ≤ MAX_UINT256) :
  safeMul 1 b = some b := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_right (a : Uint256) (h : (a : Nat) ≤ MAX_UINT256) :
  safeMul a 1 = some a := by
  simp [safeMul, Nat.not_lt.mpr h]

/-- safeMul is commutative. -/
theorem safeMul_comm (a b : Uint256) :
  safeMul a b = safeMul b a := by
  simp [safeMul, Nat.mul_comm]

/-! ## safeDiv Correctness -/

/-- safeDiv returns the quotient when divisor is nonzero. -/
theorem safeDiv_some (a b : Uint256) (h : b ≠ 0) :
  safeDiv a b = some (a / b) := by
  have h_not : b.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  simp [safeDiv, h_not]

/-- safeDiv returns none when divisor is zero. -/
theorem safeDiv_none (a : Uint256) :
  safeDiv a 0 = none := by
  simp [safeDiv]

/-- safeDiv of zero always returns zero (when divisor is nonzero). -/
theorem safeDiv_zero_numerator (b : Uint256) (h : b ≠ 0) :
  safeDiv 0 b = some 0 := by
  have h_not : b.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  simp [safeDiv, h_not]

/-- safeDiv by one returns the numerator. -/
theorem safeDiv_by_one (a : Uint256) :
  safeDiv a 1 = some a := by
  simp [safeDiv]

/-- safeDiv of a value by itself returns 1 (when nonzero). -/
theorem safeDiv_self (a : Uint256) (h : a ≠ 0) :
  safeDiv a a = some 1 := by
  have h_not : a.val ≠ 0 := fun hv => h (Verity.Core.Uint256.ext (by simp [Verity.Core.Uint256.val_zero, hv]))
  have hpos : 0 < (a : Nat) := Nat.pos_of_ne_zero h_not
  have hlt : (1 : Nat) < Verity.Core.Uint256.modulus := by decide
  have hdiv : a / a = (1 : Uint256) := by
    apply Verity.Core.Uint256.ext
    calc (a / a).val
        = (a.val / a.val) % Verity.Core.Uint256.modulus := by
          simp [HDiv.hDiv, Verity.Core.Uint256.div, h_not, Verity.Core.Uint256.ofNat]
      _ = 1 % Verity.Core.Uint256.modulus := by simp [Nat.div_self hpos]
      _ = 1 := Nat.mod_eq_of_lt hlt
  simp [safeDiv, h_not, hdiv]

/-! ## Cross-Operation Properties -/

/-- safeMul result is always bounded by MAX_UINT256 when successful. -/
theorem safeMul_result_bounded (a b : Uint256) (c : Uint256)
  (_h : safeMul a b = some c) : c ≤ MAX_UINT256 :=
  Verity.Core.Uint256.val_le_max c

/-- safeDiv result never exceeds the numerator. -/
theorem safeDiv_result_le_numerator (a b : Uint256) (c : Uint256)
  (h_div : safeDiv a b = some c) : c ≤ a := by
  by_cases hzero : b.val = 0
  · simp [safeDiv, hzero] at h_div
  · simp [safeDiv, hzero] at h_div
    have hc : a / b = c := by cases h_div; rfl
    have hdiv_lt : (a : Nat) / (b : Nat) < Verity.Core.Uint256.modulus :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
    have hdiv : ((a / b : Uint256) : Nat) = (a : Nat) / (b : Nat) := by
      simp only [HDiv.hDiv, Verity.Core.Uint256.div, hzero, Verity.Core.Uint256.ofNat, ↓reduceIte]
      exact Nat.mod_eq_of_lt hdiv_lt
    have hcval : (c : Nat) = (a : Nat) / (b : Nat) :=
      (hdiv.symm.trans (congrArg (fun x => x.val) hc)).symm
    simp only [Verity.Core.Uint256.le_def, hcval]
    exact Nat.div_le_self _ _

/-! ## Summary

All 25 theorems fully proven with zero sorry:

safeAdd:
1. safeAdd_some — returns sum when no overflow
2. safeAdd_none — returns none on overflow
3. safeAdd_zero_left — 0 + b = b when bounded
4. safeAdd_zero_right — a + 0 = a when bounded
5. safeAdd_comm — commutativity
6. safeAdd_result_bounded — successful result ≤ MAX_UINT256

safeSub:
7. safeSub_some — returns difference when no underflow
8. safeSub_none — returns none on underflow
9. safeSub_zero — a - 0 = a always safe
10. safeSub_self — a - a = 0 always safe
11. safeSub_result_le — result never exceeds minuend

safeMul:
12. safeMul_some — returns product when no overflow
13. safeMul_none — returns none on overflow
14. safeMul_zero_left — 0 * b = 0 always safe
15. safeMul_zero_right — a * 0 = 0 always safe
16. safeMul_one_left — 1 * b = b when bounded
17. safeMul_one_right — a * 1 = a when bounded
18. safeMul_comm — commutativity
19. safeMul_result_bounded — successful result ≤ MAX_UINT256

safeDiv:
20. safeDiv_some — returns quotient when divisor nonzero
21. safeDiv_none — returns none on division by zero
22. safeDiv_zero_numerator — 0 / b = 0
23. safeDiv_by_one — a / 1 = a
24. safeDiv_self — a / a = 1
25. safeDiv_result_le_numerator — result never exceeds numerator
-/

/-! ## Fixed-point Helper Summary

26. mulDivDown_nat_eq — exact floor division when the numerator fits
27. mulDivDown_mul_le — floor result never overshoots the numerator
28. mulDivUp_nat_eq — exact ceil-style division when the widened numerator fits
29. mulDivDown_le_mulDivUp — ceil result never rounds below floor
30. wMulDown_nat_eq — wad-multiply specialization of mulDivDown
31. wDivUp_nat_eq — wad-divide specialization of mulDivUp
-/

end Verity.Proofs.Stdlib.Math
