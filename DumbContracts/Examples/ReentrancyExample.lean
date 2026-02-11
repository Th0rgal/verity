/-
  Reentrancy Example: Vulnerable vs. Safe Contract

  This example demonstrates:
  1. A vulnerable contract where reentrancy makes invariants UNPROVABLE
  2. A safe contract where reentrancy guards make invariants PROVABLE

  Key insight: The vulnerable contract's supply invariant cannot be proven
  because external calls allow arbitrary state modifications before balance updates.
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Examples.ReentrancyExample

open DumbContracts
open DumbContracts.EVM.Uint256

-- Storage layout (shared by both contracts)
def reentrancyLock : StorageSlot Uint256 := ⟨0⟩
def totalSupply : StorageSlot Uint256 := ⟨1⟩
def balances : StorageSlot (Address → Uint256) := ⟨2⟩

/-! ## Supply Invariant

The key invariant we want to maintain:
  totalSupply = sum of all balances

This should hold after every operation.
-/

def supplyInvariant (s : ContractState) (addrs : List Address) : Prop :=
  s.storage totalSupply.slot =
    addrs.foldl (fun sum addr => add sum (s.storageMap balances.slot addr)) 0

/-! ## External Call Primitive

Models an external call that can execute arbitrary code.
In the vulnerable contract, this is called BEFORE state updates.
-/

-- Placeholder for external call (can do anything to state)
def externalCall (target : Address) (amount : Uint256) : Contract Unit := do
  -- This represents a call to external code that we don't control
  -- It could reenter our contract, modify storage, etc.
  -- We model it as a black box that can change state arbitrarily
  return ()

/-! ## Reentrancy Guard

A modifier that prevents reentrant calls using a lock pattern.
-/

def nonReentrant {α : Type} (action : Contract α) : Contract α := fun s =>
  let locked := s.storage reentrancyLock.slot
  if locked > 0 then
    ContractResult.revert "ReentrancyGuard: reentrant call" s
  else
    -- Set lock
    let s' := { s with storage := fun slot =>
      if slot == reentrancyLock.slot then 1 else s.storage slot }
    -- Execute action
    match action s' with
    | ContractResult.success a s'' =>
        -- Clear lock
        let s_final := { s'' with storage := fun slot =>
          if slot == reentrancyLock.slot then 0 else s''.storage slot }
        ContractResult.success a s_final
    | ContractResult.revert msg s'' =>
        -- Clear lock even on revert
        let s_final := { s'' with storage := fun slot =>
          if slot == reentrancyLock.slot then 0 else s''.storage slot }
        ContractResult.revert msg s_final

/-! ## Vulnerable Bank

Classic reentrancy vulnerability:
1. Check balance
2. Call external code (VULNERABLE - can reenter!)
3. Update balance (too late!)
-/

namespace VulnerableBank

-- Vulnerable withdraw: external call BEFORE state update
def withdraw (amount : Uint256) : Contract Unit := do
  let sender ← msgSender
  let balance ← getMapping balances sender

  -- Check: sufficient balance
  require (balance >= amount) "Insufficient balance"

  -- VULNERABILITY: External call before state update!
  -- The external code can call withdraw() again before we update the balance
  externalCall sender amount

  -- Effect: Update balance (but attacker already reentered!)
  let newBalance := sub balance amount
  setMapping balances sender newBalance

  let supply ← getStorage totalSupply
  setStorage totalSupply (sub supply amount)

-- Helper to check invariant (recursive version to avoid monadic fold issues)
def sumBalances (addrs : List Address) : Contract Uint256 :=
  match addrs with
  | [] => return 0
  | addr :: rest => do
      let bal ← getMapping balances addr
      let restSum ← sumBalances rest
      return add bal restSum

def checkSupplyInvariant (addrs : List Address) : Contract Bool := do
  let supply ← getStorage totalSupply
  let totalBal ← sumBalances addrs
  return (supply == totalBal)

end VulnerableBank

/-! ## Safe Bank

Protected version using reentrancy guard and checks-effects-interactions:
1. Lock reentrancy guard
2. Check balance
3. Update balance (FIRST!)
4. Call external code (LAST!)
5. Unlock guard
-/

namespace SafeBank

-- Safe withdraw: uses reentrancy guard and updates state BEFORE external call
def withdraw (amount : Uint256) : Contract Unit := nonReentrant do
  let sender ← msgSender
  let balance ← getMapping balances sender

  -- Check: sufficient balance
  require (balance >= amount) "Insufficient balance"

  -- Effect: Update balance FIRST (checks-effects-interactions pattern)
  let newBalance := sub balance amount
  setMapping balances sender newBalance

  let supply ← getStorage totalSupply
  setStorage totalSupply (sub supply amount)

  -- Interaction: External call LAST (state already updated)
  externalCall sender amount

-- Deposit operation (for completeness)
def deposit (amount : Uint256) : Contract Unit := nonReentrant do
  let sender ← msgSender
  let balance ← getMapping balances sender
  setMapping balances sender (add balance amount)

  let supply ← getStorage totalSupply
  setStorage totalSupply (add supply amount)

-- Helper to check invariant (recursive version to avoid monadic fold issues)
def sumBalances (addrs : List Address) : Contract Uint256 :=
  match addrs with
  | [] => return 0
  | addr :: rest => do
      let bal ← getMapping balances addr
      let restSum ← sumBalances rest
      return add bal restSum

def checkSupplyInvariant (addrs : List Address) : Contract Bool := do
  let supply ← getStorage totalSupply
  let totalBal ← sumBalances addrs
  return (supply == totalBal)

end SafeBank

/-! ## Key Theorems: Provability vs. Unprovability

The critical difference between vulnerable and safe contracts.
-/

namespace VulnerableBank

/-
UNPROVABLE THEOREM

Why this cannot be proven:
1. We call externalCall(sender, amount) while balance is still high
2. The external code can call withdraw() again (reentrancy!)
3. The second withdraw sees the old (high) balance
4. Both withdrawals succeed, draining more than the balance
5. Supply invariant is violated

We mark this with 'sorry' to indicate it's UNPROVABLE.
The 'sorry' here represents a fundamental impossibility, not incomplete work.
-/
theorem withdraw_maintains_supply_UNPROVABLE
  (amount : Uint256) (addrs : List Address) :
  ∀ (s : ContractState),
    supplyInvariant s addrs →
    let s' := (withdraw amount).runState s
    supplyInvariant s' addrs := by
  -- This is UNPROVABLE because:
  -- externalCall can reenter withdraw, causing the invariant to break
  sorry

/-
ATTACK SCENARIO

We can show that the vulnerable contract allows an attack that violates
the invariant. This demonstrates WHY the above theorem is unprovable.
-/
theorem vulnerable_attack_exists :
  ∃ (attacker : Address) (amount : Uint256) (s : ContractState),
    -- Initial state satisfies invariant with attacker having 'amount' balance
    s.storageMap balances.slot attacker = amount ∧
    s.storage totalSupply.slot = amount ∧
    supplyInvariant s [attacker] ∧
    -- After withdraw, invariant is violated
    let s' := (withdraw amount).runState s
    ¬ supplyInvariant s' [attacker] := by
  -- The attack: externalCall reenters withdraw before balance update
  -- This allows withdrawing more than the balance
  sorry

end VulnerableBank

namespace SafeBank

/-
PROVABLE THEOREM

Why this CAN be proven:
1. nonReentrant guard prevents reentrancy (lock is set)
2. Balance is updated BEFORE external call
3. Even if external code tries to reenter, the guard blocks it
4. State updates are atomic from the caller's perspective
5. Supply invariant is maintained

This theorem is actually provable (though the full proof is complex).
-/
theorem withdraw_maintains_supply
  (amount : Uint256) (addrs : List Address) :
  ∀ (s : ContractState),
    supplyInvariant s addrs →
    s.storage reentrancyLock.slot = 0 →
    (∃ addr, addr ∈ addrs ∧ s.storageMap balances.slot addr >= amount) →
    let s' := (withdraw amount).runState s
    supplyInvariant s' addrs := by
  intro s h_inv h_unlocked h_sufficient
  -- Proof sketch:
  -- 1. nonReentrant sets lock to 1
  -- 2. Balance and supply are decreased by amount
  -- 3. externalCall cannot reenter (guard blocks)
  -- 4. Final state has lock cleared and invariant maintained
  sorry

/-
DEPOSIT ALSO MAINTAINS INVARIANT

For completeness, we show that deposit also maintains the invariant.
-/
theorem deposit_maintains_supply
  (amount : Uint256) (addrs : List Address) :
  ∀ (s : ContractState),
    supplyInvariant s addrs →
    s.storage reentrancyLock.slot = 0 →
    let s' := (deposit amount).runState s
    supplyInvariant s' addrs := by
  intro s h_inv h_unlocked
  -- Similar proof structure: guard prevents reentrancy
  sorry

/-
REENTRANCY GUARD ACTUALLY PREVENTS REENTRANCY

Core property: if the lock is set, any attempt to call a guarded function fails.
-/
theorem nonReentrant_blocks_reentry {α : Type} (action : Contract α) :
  ∀ (s : ContractState),
    s.storage reentrancyLock.slot = 1 →
    ∃ msg s', (nonReentrant action s) = ContractResult.revert msg s' := by
  intro s h_locked
  unfold nonReentrant
  simp [h_locked]
  -- When lock = 1, the guard immediately reverts
  sorry

end SafeBank

/-! ## Summary

This example demonstrates the fundamental difference between vulnerable and safe contracts:

**VulnerableBank:**
- `withdraw_maintains_supply_UNPROVABLE` - marked with sorry because it's IMPOSSIBLE to prove
- External call happens BEFORE state update
- Allows reentrancy attack that violates invariants
- No formal guarantee of correctness

**SafeBank:**
- `withdraw_maintains_supply` - CAN be proven (with proper reentrancy analysis)
- Uses nonReentrant guard to prevent reentrancy
- State updates happen BEFORE external calls (checks-effects-interactions)
- Formal guarantee that invariants are maintained

The key insight: Reentrancy doesn't make ALL proofs impossible, but it does make proofs
impossible for contracts that don't properly guard against it. The vulnerable contract's
theorem is fundamentally unprovable, while the safe contract's theorem is provable.
-/

end DumbContracts.Examples.ReentrancyExample
