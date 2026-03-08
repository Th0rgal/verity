/-
  Reentrancy Example: Vulnerable vs. Safe Contract

  This example demonstrates:
  1. A vulnerable contract where reentrancy makes an invariant FALSE
  2. A safe contract where the same invariant is PROVABLE
-/

import Verity.Core
import Verity.Core.Semantics
import Verity.EVM.Uint256

namespace Contracts.ReentrancyExample

open Verity
open Verity.EVM.Uint256

-- Storage layout (shared by both contracts)
def reentrancyLock : StorageSlot Uint256 := ⟨0⟩
def totalSupply : StorageSlot Uint256 := ⟨1⟩
def balances : StorageSlot (Address → Uint256) := ⟨2⟩

/-! ## Supply Invariant

The key invariant we want to maintain:
  totalSupply = sum of all balances
-/

def supplyInvariant (s : ContractState) (addrs : List Address) : Prop :=
  s.storage totalSupply.slot =
    addrs.foldl (fun sum addr => sum + s.storageMap balances.slot addr) 0

-- Minimal state updates (pure helpers)
def setStorageSlot (slot : StorageSlot Uint256) (val : Uint256) (s : ContractState) : ContractState :=
  { s with storage := fun n => if n == slot.slot then val else s.storage n }

def setMappingSlot (slot : StorageSlot (Address → Uint256)) (addr : Address) (val : Uint256)
  (s : ContractState) : ContractState :=
  { s with storageMap := fun n a => if n == slot.slot && a == addr then val else s.storageMap n a }

@[simp] theorem modulus_sub_max :
  Verity.Core.Uint256.modulus - Verity.EVM.MAX_UINT256 = 1 := by
  have h : Verity.Core.Uint256.modulus = Verity.EVM.MAX_UINT256 + 1 := by
    symm
    exact Verity.Core.Uint256.max_uint256_succ_eq_modulus
  -- (MAX + 1) - MAX = 1
  calc
    Verity.Core.Uint256.modulus - Verity.EVM.MAX_UINT256
        = (Verity.EVM.MAX_UINT256 + 1) - Verity.EVM.MAX_UINT256 := by
            simp [h]
    _ = 1 := by
            exact Nat.add_sub_cancel_left Verity.EVM.MAX_UINT256 1

/-! ## Vulnerable Bank

External call happens before balance update. We model a single reentrant call
by subtracting totalSupply twice while only decrementing balance once.
-/

namespace VulnerableBank

-- Deposit (mirrors SafeBank — reentrancy is only relevant on withdraw)
def deposit (amount : Uint256) : Contract Unit := fun s =>
  let bal := s.storageMap balances.slot s.sender
  let supply := s.storage totalSupply.slot
  let s1 := setMappingSlot balances s.sender (bal + amount) s
  let s2 := setStorageSlot totalSupply (supply + amount) s1
  ContractResult.success () s2

def withdrawWithEnv (env : Verity.Env) (amount : Uint256) : Contract Unit := fun s =>
  let bal := s.storageMap balances.slot s.sender
  if decide (bal ≥ amount) then
    let supply := s.storage totalSupply.slot
    let s1 := setStorageSlot totalSupply (sub supply amount) s
    let didReenter := env.callOracle "VulnerableBank.withdraw" [amount, bal, supply]
    -- Reentrant call effect (oracle-controlled): totalSupply decremented again
    let s2 :=
      if didReenter == 0 then s1
      else
        let supply2 := s1.storage totalSupply.slot
        setStorageSlot totalSupply (sub supply2 amount) s1
    -- Balance updated once (using the original balance)
    let s3 := setMappingSlot balances s.sender (sub bal amount) s2
    ContractResult.success () s3
  else
    ContractResult.revert "Insufficient balance" s

def withdraw (amount : Uint256) : Contract Unit := fun s =>
  (withdrawWithEnv (Verity.Env.ofWorld s) amount) s

/-
COUNTEREXAMPLE: Proof that vulnerability exists
-/

theorem vulnerable_attack_exists :
  ∃ (s : ContractState) (env : Verity.Env),
    s.storageMap balances.slot 0xA77AC = (Verity.EVM.MAX_UINT256 : Uint256) ∧
    s.storage totalSupply.slot = (Verity.EVM.MAX_UINT256 : Uint256) ∧
    supplyInvariant s [0xA77AC] ∧
    let s' := (withdrawWithEnv env (Verity.EVM.MAX_UINT256 : Uint256)).runState s;
    ¬ supplyInvariant s' [0xA77AC] := by
  -- Choose a concrete attacker and amount. We use MAX_UINT256 so that
  -- `0 - amount` wraps to 1, making the mismatch obvious.
  let s : ContractState :=
    { storage := fun slot => if slot == totalSupply.slot then (Verity.EVM.MAX_UINT256 : Uint256) else 0
    , storageAddr := fun _ => 0
    , storageMap := fun slot addr =>
        if slot == balances.slot && addr == 0xA77AC then (Verity.EVM.MAX_UINT256 : Uint256) else 0
    , storageMapUint := fun _ _ => 0
    , storageMap2 := fun _ _ _ => 0
    , sender := 0xA77AC
    , thisAddress := 0x7415
    , msgValue := 0
    , blockTimestamp := 0
    , knownAddresses := fun _ => Core.FiniteAddressSet.empty }
  let env : Verity.Env :=
    { sender := s.sender
    , thisAddress := s.thisAddress
    , msgValue := s.msgValue
    , blockTimestamp := s.blockTimestamp
    , blockNumber := s.blockNumber
    , callOracle := fun _ _ => 1 }
  refine ⟨s, env, ?_⟩
  constructor
  · simp [s, balances]
  constructor
  · simp [s, totalSupply]
  constructor
  · simp [s, supplyInvariant, balances, totalSupply]
  ·
    have h_neq : (1 : Uint256) ≠ (0 : Uint256) := by decide
    -- After simplification, the invariant reduces to `1 = 0`, which is false.
    simp [supplyInvariant, balances, totalSupply, s, env]
    exact h_neq

/-
UNPROVABLE THEOREM

We can show the universal statement is FALSE by using the counterexample.
-/

theorem withdraw_maintains_supply_UNPROVABLE :
  ¬ (∀ (s : ContractState) (env : Verity.Env),
      supplyInvariant s [0xA77AC] →
      let s' := (withdrawWithEnv env (Verity.EVM.MAX_UINT256 : Uint256)).runState s;
      supplyInvariant s' [0xA77AC]) := by
  intro h
  rcases vulnerable_attack_exists with ⟨s, env, _h_bal, _h_sup, h_inv, h_not⟩
  have h' := h s env h_inv
  exact h_not h'

end VulnerableBank

/-! ## Safe Bank

State updates happen before any external interaction. We model the external call
as a no-op, so the invariant is preserved.
-/

namespace SafeBank

def withdrawWithEnv (env : Verity.Env) (amount : Uint256) : Contract Unit := fun s =>
  let bal := s.storageMap balances.slot s.sender
  if decide (bal ≥ amount) then
    let supply := s.storage totalSupply.slot
    let s1 := setMappingSlot balances s.sender (sub bal amount) s
    let s2 := setStorageSlot totalSupply (sub supply amount) s1
    let _ := env.callOracle "SafeBank.withdraw" [amount, bal, supply]
    ContractResult.success () s2
  else
    ContractResult.revert "Insufficient balance" s

def withdraw (amount : Uint256) : Contract Unit := fun s =>
  (withdrawWithEnv (Verity.Env.ofWorld s) amount) s

-- Deposit (for completeness)
def deposit (amount : Uint256) : Contract Unit := fun s =>
  let bal := s.storageMap balances.slot s.sender
  let supply := s.storage totalSupply.slot
  let s1 := setMappingSlot balances s.sender (bal + amount) s
  let s2 := setStorageSlot totalSupply (supply + amount) s1
  ContractResult.success () s2

/-
PROVABLE THEOREM
-/

theorem withdraw_maintains_supply (amount : Uint256) :
  ∀ (s : ContractState),
    supplyInvariant s [s.sender] →
    s.storageMap balances.slot s.sender ≥ amount →
    let s' := (withdraw amount).runState s;
    supplyInvariant s' [s.sender] := by
  intro s h_inv h_bal
  have h_eq : s.storage totalSupply.slot = s.storageMap balances.slot s.sender := by
    simp [supplyInvariant] at h_inv
    exact h_inv
  have h_cond2 : amount.val ≤ (s.storageMap 2 s.sender).val := by
    simpa [balances] using h_bal
  -- Unfold the effect of withdraw and use the pre-state equality.
  have h_left :
      ((withdraw amount).runState s).storage totalSupply.slot =
        sub (s.storage totalSupply.slot) amount := by
    simp [Contract.runState, withdraw, withdrawWithEnv, h_cond2, setStorageSlot, setMappingSlot, balances, totalSupply]
  have h_right :
      ((withdraw amount).runState s).storageMap balances.slot s.sender =
        sub (s.storageMap balances.slot s.sender) amount := by
    simp [Contract.runState, withdraw, withdrawWithEnv, h_cond2, setStorageSlot, setMappingSlot, balances, totalSupply]
  -- Reduce to the same subtraction on both sides.
  have h_mid : sub (s.storage totalSupply.slot) amount =
      sub (s.storageMap balances.slot s.sender) amount := by
    simp [h_eq]
  -- Conclude the invariant for the post-state.
  have h_result :
      ((withdraw amount).runState s).storage totalSupply.slot =
        ((withdraw amount).runState s).storageMap balances.slot s.sender := by
    calc
      ((withdraw amount).runState s).storage totalSupply.slot
          = sub (s.storage totalSupply.slot) amount := h_left
      _ = sub (s.storageMap balances.slot s.sender) amount := h_mid
      _ = ((withdraw amount).runState s).storageMap balances.slot s.sender := by
            symm; exact h_right
  simpa [supplyInvariant, Contract.runState_eq_snd_run] using h_result

/-
DEPOSIT ALSO MAINTAINS INVARIANT
-/

theorem deposit_maintains_supply (amount : Uint256) :
  ∀ (s : ContractState),
    supplyInvariant s [s.sender] →
    let s' := (deposit amount).runState s;
    supplyInvariant s' [s.sender] := by
  intro s h_inv
  have h_eq : s.storage totalSupply.slot = s.storageMap balances.slot s.sender := by
    simp [supplyInvariant] at h_inv
    exact h_inv
  -- Unfold the effect of deposit and use the pre-state equality.
  have h_left :
      ((deposit amount).runState s).storage totalSupply.slot =
        (s.storage totalSupply.slot) + amount := by
    simp [Contract.runState, deposit, setStorageSlot, setMappingSlot, balances, totalSupply]
  have h_right :
      ((deposit amount).runState s).storageMap balances.slot s.sender =
        (s.storageMap balances.slot s.sender) + amount := by
    simp [Contract.runState, deposit, setStorageSlot, setMappingSlot, balances, totalSupply]
  have h_mid : (s.storage totalSupply.slot) + amount =
      (s.storageMap balances.slot s.sender) + amount := by
    simp [h_eq]
  have h_result :
      ((deposit amount).runState s).storage totalSupply.slot =
        ((deposit amount).runState s).storageMap balances.slot s.sender := by
    calc
      ((deposit amount).runState s).storage totalSupply.slot
          = (s.storage totalSupply.slot) + amount := h_left
      _ = (s.storageMap balances.slot s.sender) + amount := h_mid
      _ = ((deposit amount).runState s).storageMap balances.slot s.sender := by
            symm; exact h_right
  simpa [supplyInvariant, Contract.runState_eq_snd_run] using h_result

end SafeBank

/-! ## Guard Primitive Demonstration

These theorems exercise the first-class `nonReentrant` primitive directly:
- unlocked execution succeeds
- nested entry into the same lock is blocked
-/
namespace GuardPrimitive

theorem nonReentrant_blocks_when_locked (s : ContractState)
    (hLocked : s.storage reentrancyLock.slot ≠ 0) :
    (nonReentrant reentrancyLock (Verity.pure ())).run s =
      ContractResult.revert "ReentrancyGuard: reentrant call" s := by
  simpa using nonReentrant_locked_reverts reentrancyLock (Verity.pure ()) s hLocked

end GuardPrimitive

end Contracts.ReentrancyExample
