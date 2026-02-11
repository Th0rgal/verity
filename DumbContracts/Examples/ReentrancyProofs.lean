/-
  Complete Proofs: Vulnerable vs Safe Reentrancy

  This file contains COMPLETE PROOFS (no sorry) showing:
  1. Vulnerable contract: invariant is UNPROVABLE (proven by counterexample)
  2. Safe contract: invariant IS PROVABLE (proven constructively)
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Examples.ReentrancyProofs

open DumbContracts
open DumbContracts.EVM.Uint256

/-! ## Setup -/

def totalSupplySlot : Nat := 0
def balanceSlot : Nat := 1

-- Simplified invariant: single address case
-- totalSupply = balance[addr]
structure SimpleState where
  supply : Uint256
  balance : Uint256

def invariant (s : SimpleState) : Prop :=
  s.supply = s.balance

/-! ## Vulnerable Contract -/

/-
THEOREM: Vulnerable contract is UNPROVABLE

We prove this by showing a concrete counterexample where the invariant is violated.

The key insight: in a vulnerable contract, the external call happens BEFORE state updates.
This means a reentrant call can see stale state. We model this as:
1. First call decreases supply (from reentrant call during external call)
2. Second call ALSO decreases supply (original call continues)
3. But balance is only decremented once (from the stale read in step 1)
Result: supply is decremented twice, balance once → invariant violated
-/

-- Simpler counterexample: Use explicit state difference
-- In the vulnerable version, supply is updated twice but balance only once (from stale read)
def vulnerableStaleRead (amount : Uint256) (s : SimpleState) : SimpleState :=
  if s.balance >= amount then
    -- Both decrease supply (double decrement)
    let s1 : SimpleState := { supply := sub s.supply amount, balance := s.balance }
    ({ supply := sub s1.supply amount, balance := sub s.balance amount } : SimpleState)
  else
    s

theorem vulnerable_stale_read_is_unprovable :
  ∃ (s : SimpleState) (amount : Uint256),
    invariant s ∧
    s.balance >= amount ∧
    ¬ invariant (vulnerableStaleRead amount s) := by
  -- Counterexample: balance = 100, amount = 50
  let s_init : SimpleState := { supply := 100, balance := 100 }
  let amt : Uint256 := 50
  exists s_init, amt
  refine ⟨?_, ?_, ?_⟩
  · -- Initial invariant: 100 = 100
    rfl
  · -- Sufficient balance: 100 >= 50
    decide
  · -- Invariant violated after attack
    unfold invariant vulnerableStaleRead
    simp only [decide_True, ite_true]
    intro h_equal
    -- h_equal : sub (sub 100 50) 50 = sub 100 50
    -- Let's compute each side
    --   LHS: sub (sub 100 50) 50 = sub 50 50 = 0
    --   RHS: sub 100 50 = 50
    -- So we have 0 = 50, which is false
    -- We'll show this by norm_num on the Uint256 values
    have lhs : sub (sub 100 50) 50 = 0 := by decide
    have rhs : sub 100 50 = 50 := by decide
    rw [lhs, rhs] at h_equal
    -- Now h_equal : 0 = 50
    cases h_equal

/-! ## Safe Contract -/

-- Models safe withdraw: check, update FIRST, then external call (which can't reenter due to guard)
def safeWithdraw (amount : Uint256) (s : SimpleState) : SimpleState :=
  if s.balance >= amount then
    { supply := sub s.supply amount, balance := sub s.balance amount }
  else
    s

/-
THEOREM: Safe contract maintains invariant

Since state is updated BEFORE external call and guard prevents reentrancy,
the update is atomic.
-/

theorem safe_maintains_invariant (amount : Uint256) (s : SimpleState) :
  invariant s →
  s.balance >= amount →
  invariant (safeWithdraw amount s) := by
  intro h_inv h_sufficient
  unfold invariant at *
  unfold safeWithdraw
  simp [h_sufficient]
  -- After withdraw:
  -- supply' = sub s.supply amount
  -- balance' = sub s.balance amount
  -- Since s.supply = s.balance (by h_inv),
  -- we have sub s.supply amount = sub s.balance amount
  rw [h_inv]

/-
THEOREM: Safe deposit also maintains invariant
-/

def safeDeposit (amount : Uint256) (s : SimpleState) : SimpleState :=
  { supply := add s.supply amount, balance := add s.balance amount }

theorem safe_deposit_maintains_invariant (amount : Uint256) (s : SimpleState) :
  invariant s →
  invariant (safeDeposit amount s) := by
  intro h_inv
  unfold invariant at *
  unfold safeDeposit
  simp
  -- supply' = add s.supply amount
  -- balance' = add s.balance amount
  -- Since s.supply = s.balance, these are equal
  rw [h_inv]

/-! ## Summary

We've proven:
1. **Vulnerable contract is UNPROVABLE**: Counterexample shows invariant violation
2. **Safe contract IS PROVABLE**: Constructive proof that invariant is maintained

The key difference:
- Vulnerable: External call BEFORE state update → reentrancy → double spending
- Safe: State update BEFORE external call + guard → atomic update → invariant preserved
-/

end DumbContracts.Examples.ReentrancyProofs
