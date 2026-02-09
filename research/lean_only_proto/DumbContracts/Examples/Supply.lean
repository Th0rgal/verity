import DumbContracts.Examples.TokenBase

namespace DumbContracts.Examples

open DumbContracts

-- Counterexample: list-based sums are sensitive to duplicates.

theorem sumBalances_dup (s : Store) (a : Nat) :
    sumBalances s [a, a] = s (balanceSlot a) + s (balanceSlot a) := by
  simp [sumBalances]

theorem sumBalances_dup_ne_totalSupply (s : Store) (a : Nat)
    (hsupply : totalSupply s = s (balanceSlot a)) (hpos : s (balanceSlot a) > 0) :
    sumBalances s [a, a] ≠ totalSupply s := by
  intro h
  have hsum : s (balanceSlot a) + s (balanceSlot a) = s (balanceSlot a) := by
    simpa [sumBalances, hsupply] using h
  have hx : s (balanceSlot a) + s (balanceSlot a) = s (balanceSlot a) + 0 := by
    simpa using (hsum.trans (by simp))
  have hzero : s (balanceSlot a) = 0 := by
    exact Nat.add_left_cancel hx
  exact (ne_of_gt hpos) hzero

end DumbContracts.Examples
