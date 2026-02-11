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
    addrs.foldl (fun sum addr => sum + s.storageMap balances.slot addr) 0

/-! ## External Call Primitive

We model external calls as *potentially reentrant* with a bounded depth.
This makes reentrancy behavior explicit and allows concrete proofs.
-/

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

-- Reentrant external call with bounded depth.
mutual
  def withdrawWithDepth (amount : Uint256) (depth : Nat) : Contract Unit := do
    let sender ← msgSender
    let balance ← getMapping balances sender

    -- Check: sufficient balance
    require (balance >= amount) "Insufficient balance"

    -- VULNERABILITY: Update totalSupply BEFORE external call.
    -- If reentrancy happens, totalSupply may be decremented twice while
    -- the sender balance is only decremented once (outer overwrite).
    let supply ← getStorage totalSupply
    setStorage totalSupply (sub supply amount)

    -- External call can reenter
    externalCall depth sender amount

    -- Effect: Update balance AFTER external call (too late)
    let newBalance := sub balance amount
    setMapping balances sender newBalance

  def externalCall (depth : Nat) (target : Address) (amount : Uint256) : Contract Unit := fun s =>
    match depth with
    | 0 => ContractResult.success () s
    | n + 1 =>
        -- Attempt a single reentrant call; swallow its result to model
        -- "external code may reenter, but the outer call continues".
        match withdrawWithDepth amount n s with
        | ContractResult.success _ s' => ContractResult.success () s'
        | ContractResult.revert _ s' => ContractResult.success () s'
termination_by
  withdrawWithDepth _ depth => depth
  externalCall depth _ _ => depth
end

-- Public entry point: allow a single reentrant call.
def withdraw (amount : Uint256) : Contract Unit :=
  withdrawWithDepth amount 1

-- Helper to check invariant (recursive version to avoid monadic fold issues)
def sumBalances (addrs : List Address) : Contract Uint256 :=
  match addrs with
  | [] => return 0
  | addr :: rest => do
      let bal ← getMapping balances addr
      let restSum ← sumBalances rest
      return bal + restSum

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

-- Reentrant external call with bounded depth.
mutual
  -- Safe withdraw: uses reentrancy guard and updates state BEFORE external call
  def withdrawWithDepth (amount : Uint256) (depth : Nat) : Contract Unit := nonReentrant do
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
    externalCall depth sender amount

  def externalCall (depth : Nat) (target : Address) (amount : Uint256) : Contract Unit := fun s =>
    match depth with
    | 0 => ContractResult.success () s
    | n + 1 =>
        -- Attempt reentrant call; swallow result so outer continues.
        match withdrawWithDepth amount n s with
        | ContractResult.success _ s' => ContractResult.success () s'
        | ContractResult.revert _ s' => ContractResult.success () s'
termination_by
  withdrawWithDepth _ depth => depth
  externalCall depth _ _ => depth
end

-- Public entry point: allow a single reentrant attempt.
def withdraw (amount : Uint256) : Contract Unit :=
  withdrawWithDepth amount 1

-- Deposit operation (for completeness)
def deposit (amount : Uint256) : Contract Unit := nonReentrant do
  let sender ← msgSender
  let balance ← getMapping balances sender
  setMapping balances sender (balance + amount)

  let supply ← getStorage totalSupply
  setStorage totalSupply (supply + amount)

-- Helper to check invariant (recursive version to avoid monadic fold issues)
def sumBalances (addrs : List Address) : Contract Uint256 :=
  match addrs with
  | [] => return 0
  | addr :: rest => do
      let bal ← getMapping balances addr
      let restSum ← sumBalances rest
      return bal + restSum

def checkSupplyInvariant (addrs : List Address) : Contract Bool := do
  let supply ← getStorage totalSupply
  let totalBal ← sumBalances addrs
  return (supply == totalBal)

end SafeBank

/-! ## Key Theorems: Provability vs. Unprovability

The critical difference between vulnerable and safe contracts.
-/

namespace VulnerableBank

/-! ### Helpers for Concrete Counterexample Proofs -/

private def baseState (sender : Address) (bal : Uint256) : ContractState :=
  { storage := fun slot => if slot == totalSupply.slot then bal else 0
  , storageAddr := fun _ => ""
  , storageMap := fun slot addr =>
      if slot == balances.slot && addr == sender then bal else 0
  , sender := sender
  , thisAddress := "this"
  , msgValue := 0
  , blockTimestamp := 0 }

private lemma supplyInvariant_singleton (s : ContractState) (addr : Address) :
  supplyInvariant s [addr] ↔
    s.storage totalSupply.slot = s.storageMap balances.slot addr := by
  simp [supplyInvariant]

private lemma baseState_supply (sender : Address) (bal : Uint256) :
  (baseState sender bal).storage totalSupply.slot = bal := by
  simp [baseState, totalSupply]

private lemma baseState_balance (sender : Address) (bal : Uint256) :
  (baseState sender bal).storageMap balances.slot sender = bal := by
  simp [baseState, balances]

@[simp] private lemma modulus_sub_max :
  DumbContracts.Core.Uint256.modulus - DumbContracts.EVM.MAX_UINT256 = 1 := by
  have h := DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus
  simpa [h] using (Nat.add_sub_cancel DumbContracts.EVM.MAX_UINT256 1)

/-
ATTACK SCENARIO

We can show that the vulnerable contract allows an attack that violates
the invariant. This demonstrates WHY the above theorem is unprovable.
-/
/-
COUNTEREXAMPLE: Proof that vulnerability exists

This theorem shows a concrete attack scenario where the invariant is violated.
This proves that `withdraw_maintains_supply_UNPROVABLE` is genuinely unprovable,
not just difficult to prove.
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
  -- Choose a concrete attacker and amount. We use MAX_UINT256 so that
  -- `0 - amount` wraps to 1, making the mismatch obvious.
  refine ⟨"attacker", (DumbContracts.EVM.MAX_UINT256 : Uint256),
    baseState "attacker" (DumbContracts.EVM.MAX_UINT256 : Uint256), ?_⟩
  constructor
  · exact baseState_balance "attacker" (DumbContracts.EVM.MAX_UINT256 : Uint256)
  constructor
  · exact baseState_supply "attacker" (DumbContracts.EVM.MAX_UINT256 : Uint256)
  constructor
  ·
    have h := (supplyInvariant_singleton
      (baseState "attacker" (DumbContracts.EVM.MAX_UINT256 : Uint256)) "attacker").2
    exact h (by
      simp [baseState, balances, totalSupply])
  ·
    -- Evaluate `withdraw` with a single reentrant call.
    -- The final state has: totalSupply = 1, balance[attacker] = 0.
    have h_balance :
      (baseState "attacker" (DumbContracts.EVM.MAX_UINT256 : Uint256)).storageMap
        balances.slot "attacker" >= (DumbContracts.EVM.MAX_UINT256 : Uint256) := by
      simp [baseState, balances]
    -- Unfold the let-binding and simplify the execution trace.
    dsimp
    -- After simplification, the invariant reduces to `1 = 0`, which is false.
    have h_neq : (1 : Uint256) ≠ (0 : Uint256) := by decide
    simpa [withdraw, withdrawWithDepth, externalCall, msgSender, getMapping, setMapping,
      getStorage, setStorage, require, DumbContracts.bind, Bind.bind,
      DumbContracts.pure, Pure.pure, Contract.run, ContractResult.snd, ContractResult.fst,
      h_balance, baseState, balances, totalSupply, supplyInvariant] using h_neq

/- 
UNPROVABLE THEOREM

We can now show the universal statement is FALSE by using the counterexample.
-/
theorem withdraw_maintains_supply_UNPROVABLE
  :
  ¬ (∀ (s : ContractState),
      supplyInvariant s ["attacker"] →
      let s' := (withdraw (DumbContracts.EVM.MAX_UINT256 : Uint256)).runState s
      supplyInvariant s' ["attacker"]) := by
  intro h
  rcases vulnerable_attack_exists with ⟨attacker, amount', s, h_bal, h_sup, h_inv, h_not⟩
  -- Specialize the claimed universal statement to the counterexample.
  have h' := h s h_inv
  -- Contradiction.
  exact h_not h'

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
  (amount : Uint256) :
  ∀ (s : ContractState),
    supplyInvariant s [s.sender] →
    s.storage reentrancyLock.slot = 0 →
    s.storageMap balances.slot s.sender >= amount →
    let s' := (withdraw amount).runState s
    supplyInvariant s' [s.sender] := by
  intro s h_inv h_unlocked h_balance
  -- Unfold and simplify the guarded withdraw.
  -- The external reentrant attempt is blocked by the guard.
  simp [withdraw, withdrawWithDepth, externalCall, nonReentrant, msgSender, getMapping,
    setMapping, getStorage, setStorage, require, DumbContracts.bind, Bind.bind,
    DumbContracts.pure, Pure.pure, Contract.run, ContractResult.snd, ContractResult.fst,
    h_unlocked, h_balance, supplyInvariant] at h_inv ⊢

/-
DEPOSIT ALSO MAINTAINS INVARIANT

For completeness, we show that deposit also maintains the invariant.
-/
theorem deposit_maintains_supply
  (amount : Uint256) :
  ∀ (s : ContractState),
    supplyInvariant s [s.sender] →
    s.storage reentrancyLock.slot = 0 →
    let s' := (deposit amount).runState s
    supplyInvariant s' [s.sender] := by
  intro s h_inv h_unlocked
  simp [deposit, nonReentrant, msgSender, getMapping, setMapping, getStorage, setStorage,
    DumbContracts.bind, Bind.bind, DumbContracts.pure, Pure.pure, Contract.run,
    ContractResult.snd, ContractResult.fst, h_unlocked, supplyInvariant] at h_inv ⊢

/-
REENTRANCY GUARD ACTUALLY PREVENTS REENTRANCY

Core property: if the lock is set, any attempt to call a guarded function fails.
-/
theorem nonReentrant_blocks_reentry {α : Type} (action : Contract α) :
  ∀ (s : ContractState),
    s.storage reentrancyLock.slot = 1 →
    ∃ msg s', (nonReentrant action s) = ContractResult.revert msg s' := by
  intro s h_locked
  -- When lock = 1, the guard condition (locked > 0) is true and we revert.
  refine ⟨"ReentrancyGuard: reentrant call", s, ?_⟩
  unfold nonReentrant
  simp [h_locked]

end SafeBank

/-! ## Summary

This example demonstrates the fundamental difference between vulnerable and safe contracts:

**VulnerableBank:**
- `withdraw_maintains_supply_UNPROVABLE` - proven false via concrete counterexample
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
