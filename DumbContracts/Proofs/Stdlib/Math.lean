/-
  Correctness proofs for safe arithmetic operations in the Math stdlib.

  Proves that safeMul and safeDiv correctly detect overflow/division-by-zero
  and return correct results when safe, complementing the existing
  safeAdd/safeSub proofs in SafeCounter/Basic.lean.
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math

namespace DumbContracts.Proofs.Stdlib.Math

open DumbContracts
open DumbContracts.Stdlib.Math

/-! ## safeMul Correctness -/

/-- safeMul returns the product when no overflow occurs. -/
theorem safeMul_some (a b : Uint256) (h : a * b ≤ MAX_UINT256) :
  safeMul a b = some (a * b) := by
  simp only [safeMul]
  have h_not : ¬(a * b > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeMul returns none on overflow. -/
theorem safeMul_none (a b : Uint256) (h : a * b > MAX_UINT256) :
  safeMul a b = none := by
  simp only [safeMul]
  simp [h]

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_left (b : Uint256) :
  safeMul 0 b = some 0 := by
  simp only [safeMul, Nat.zero_mul]
  simp

/-- safeMul of zero is always safe and returns zero. -/
theorem safeMul_zero_right (a : Uint256) :
  safeMul a 0 = some 0 := by
  simp only [safeMul, Nat.mul_zero]
  simp

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_left (b : Uint256) (h : b ≤ MAX_UINT256) :
  safeMul 1 b = some b := by
  have h_eq : safeMul 1 b = safeMul 1 b := rfl
  simp only [safeMul, Nat.one_mul]
  have h_not : ¬(b > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeMul of one returns the other operand (when within bounds). -/
theorem safeMul_one_right (a : Uint256) (h : a ≤ MAX_UINT256) :
  safeMul a 1 = some a := by
  simp only [safeMul, Nat.mul_one]
  have h_not : ¬(a > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeMul is commutative. -/
theorem safeMul_comm (a b : Uint256) :
  safeMul a b = safeMul b a := by
  simp only [safeMul, Nat.mul_comm]

/-! ## safeDiv Correctness -/

/-- safeDiv returns the quotient when divisor is nonzero. -/
theorem safeDiv_some (a b : Uint256) (h : b ≠ 0) :
  safeDiv a b = some (a / b) := by
  simp only [safeDiv]
  have h_not : (b == 0) = false := by simp [beq_iff_eq]; exact h
  simp [h_not]

/-- safeDiv returns none when divisor is zero. -/
theorem safeDiv_none (a : Uint256) :
  safeDiv a 0 = none := by
  simp only [safeDiv]
  simp

/-- safeDiv of zero always returns zero (when divisor is nonzero). -/
theorem safeDiv_zero_numerator (b : Uint256) (h : b ≠ 0) :
  safeDiv 0 b = some 0 := by
  simp only [safeDiv]
  have h_not : (b == 0) = false := by simp [beq_iff_eq]; exact h
  simp [h_not]

/-- safeDiv by one returns the numerator. -/
theorem safeDiv_by_one (a : Uint256) :
  safeDiv a 1 = some a := by
  simp only [safeDiv]
  simp

/-- safeDiv of a value by itself returns 1 (when nonzero). -/
theorem safeDiv_self (a : Uint256) (h : a ≠ 0) :
  safeDiv a a = some 1 := by
  simp only [safeDiv]
  have h_not : (a == 0) = false := by simp [beq_iff_eq]; exact h
  simp [h_not, Nat.div_self (Nat.pos_of_ne_zero h)]

/-! ## Cross-Operation Properties -/

/-- safeMul result is always bounded by MAX_UINT256 when successful. -/
theorem safeMul_result_bounded (a b : Uint256) (c : Uint256)
  (h : safeMul a b = some c) : c ≤ MAX_UINT256 := by
  simp only [safeMul] at h
  split at h
  · contradiction
  · simp at h; exact h ▸ Nat.not_lt.mp ‹_›

/-- safeDiv result never exceeds the numerator. -/
theorem safeDiv_result_le_numerator (a b : Uint256) (c : Uint256)
  (h_div : safeDiv a b = some c) : c ≤ a := by
  simp only [safeDiv] at h_div
  split at h_div
  · contradiction
  · simp at h_div; exact h_div ▸ Nat.div_le_self a b

/-! ## Summary

All 14 theorems fully proven with zero sorry:

safeMul:
1. safeMul_some — returns product when no overflow
2. safeMul_none — returns none on overflow
3. safeMul_zero_left — 0 * b = 0 always safe
4. safeMul_zero_right — a * 0 = 0 always safe
5. safeMul_one_left — 1 * b = b when bounded
6. safeMul_one_right — a * 1 = a when bounded
7. safeMul_comm — commutativity
8. safeMul_result_bounded — successful result ≤ MAX_UINT256

safeDiv:
9. safeDiv_some — returns quotient when divisor nonzero
10. safeDiv_none — returns none on division by zero
11. safeDiv_zero_numerator — 0 / b = 0
12. safeDiv_by_one — a / 1 = a
13. safeDiv_self — a / a = 1
14. safeDiv_result_le_numerator — result never exceeds numerator
-/

end DumbContracts.Proofs.Stdlib.Math
