/-
  Correctness proofs for all safe arithmetic operations in the Math stdlib.

  Covers safeAdd, safeSub, safeMul, and safeDiv: each operation returns
  the correct result when within bounds and returns none otherwise.
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math

namespace DumbContracts.Proofs.Stdlib.Math

open DumbContracts
open DumbContracts.Stdlib.Math

/-! ## safeAdd Correctness -/

/-- safeAdd returns the sum when no overflow occurs. -/
theorem safeAdd_some (a b : Uint256) (h : a + b ≤ MAX_UINT256) :
  safeAdd a b = some (a + b) := by
  simp only [safeAdd]
  have h_not : ¬(a + b > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeAdd returns none on overflow. -/
theorem safeAdd_none (a b : Uint256) (h : a + b > MAX_UINT256) :
  safeAdd a b = none := by
  simp only [safeAdd]
  simp [h]

/-- safeAdd with zero on the left returns the other operand (when within bounds). -/
theorem safeAdd_zero_left (b : Uint256) (h : b ≤ MAX_UINT256) :
  safeAdd 0 b = some b := by
  simp only [safeAdd, Nat.zero_add]
  have h_not : ¬(b > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeAdd with zero on the right returns the other operand (when within bounds). -/
theorem safeAdd_zero_right (a : Uint256) (h : a ≤ MAX_UINT256) :
  safeAdd a 0 = some a := by
  simp only [safeAdd, Nat.add_zero]
  have h_not : ¬(a > MAX_UINT256) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeAdd is commutative. -/
theorem safeAdd_comm (a b : Uint256) :
  safeAdd a b = safeAdd b a := by
  simp only [safeAdd, Nat.add_comm]

/-- safeAdd result is always bounded by MAX_UINT256 when successful. -/
theorem safeAdd_result_bounded (a b : Uint256) (c : Uint256)
  (h : safeAdd a b = some c) : c ≤ MAX_UINT256 := by
  simp only [safeAdd] at h
  split at h
  · contradiction
  · simp at h; exact h ▸ Nat.not_lt.mp ‹_›

/-! ## safeSub Correctness -/

/-- safeSub returns the difference when no underflow occurs. -/
theorem safeSub_some (a b : Uint256) (h : a ≥ b) :
  safeSub a b = some (a - b) := by
  simp only [safeSub]
  have h_not : ¬(b > a) := Nat.not_lt.mpr h
  simp [h_not]

/-- safeSub returns none on underflow. -/
theorem safeSub_none (a b : Uint256) (h : b > a) :
  safeSub a b = none := by
  simp only [safeSub]
  simp [h]

/-- safeSub of zero from any value is always safe. -/
theorem safeSub_zero (a : Uint256) :
  safeSub a 0 = some a := by
  simp only [safeSub]
  simp

/-- safeSub of a value from itself returns zero. -/
theorem safeSub_self (a : Uint256) :
  safeSub a a = some 0 := by
  simp only [safeSub]
  simp

/-- safeSub result never exceeds the minuend. -/
theorem safeSub_result_le (a b : Uint256) (c : Uint256)
  (h : safeSub a b = some c) : c ≤ a := by
  simp only [safeSub] at h
  split at h
  · contradiction
  · simp at h; exact h ▸ Nat.sub_le a b

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

end DumbContracts.Proofs.Stdlib.Math
