/-
  Compiler.Proofs.Automation

  Helper lemmas and automation for proving specification correctness.

  This module provides proven lemmas for Contract monad operations,
  storage operations, and common proof patterns.

  Status: Foundational lemmas - many require additional list reasoning.
  These lemmas establish the patterns needed for filling in Layer 1 proofs.
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math
import Compiler.Proofs.SpecInterpreter

namespace Compiler.Proofs.Automation

open DumbContracts
open Compiler.Proofs

/-!
## Contract Result Lemmas
-/

-- Lemmas for isSuccess
@[simp]
theorem isSuccess_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).isSuccess = true := by rfl

@[simp]
theorem isSuccess_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).isSuccess = false := by rfl

-- Lemmas for getState
@[simp]
theorem getState_success {α : Type} (a : α) (s : ContractState) :
    (ContractResult.success a s).getState = s := by rfl

@[simp]
theorem getState_revert {α : Type} (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).getState = s := by rfl

/-!
## Basic Storage Operation Lemmas
-/

-- getStorage preserves state
theorem getStorage_runState (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runState state = state := by
  simp [getStorage, Contract.runState]

-- setStorage updates the state
theorem setStorage_runState (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (setStorage slot value).runState state =
      { state with storage := fun s => if s == slot.slot then value else state.storage s } := by
  simp [setStorage, Contract.runState]

-- getStorage returns correct value
theorem getStorage_runValue (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runValue state = state.storage slot.slot := by
  simp [getStorage, Contract.runValue]

-- After setStorage, getStorage returns the value
theorem setStorage_getStorage (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (getStorage slot).runValue ((setStorage slot value).runState state) = value := by
  simp [setStorage, getStorage, Contract.runState, Contract.runValue]

-- getStorage for different slot is unchanged after setStorage
theorem setStorage_getStorage_diff (slot1 slot2 : StorageSlot Uint256) (value : Uint256) (state : ContractState)
    (h : slot1.slot ≠ slot2.slot) :
    (getStorage slot2).runValue ((setStorage slot1 value).runState state) =
    state.storage slot2.slot := by
  unfold setStorage getStorage Contract.runState Contract.runValue
  by_cases h_eq : slot2.slot = slot1.slot
  · exact (h h_eq.symm).elim
  · simp [h_eq]

/-!
## Monadic Composition Lemmas

These lemmas help with proving correctness of functions that use bind (>>=).
-/

-- Lemma for getStorage >> setStorage pattern (the most common pattern)
@[simp]
theorem bind_getStorage_setStorage_runState (slot : StorageSlot Uint256) (f : Uint256 → Uint256) (state : ContractState) :
    (DumbContracts.bind (getStorage slot) (fun val => setStorage slot (f val))).runState state =
      { state with storage := fun s => if s == slot.slot then f (state.storage slot.slot) else state.storage s } := by
  unfold DumbContracts.bind getStorage setStorage Contract.runState
  simp

-- Bind success propagation: if bind succeeds, first action succeeded
theorem bind_isSuccess_left {α β : Type} (m1 : Contract α) (m2 : α → Contract β) (state : ContractState) :
    ((DumbContracts.bind m1 m2).run state).isSuccess = true →
    (m1.run state).isSuccess = true := by
  intro h_success
  -- Strategy: case analysis on m1 state
  -- Note: Contract.run is just function application, so m1.run state = m1 state
  cases h_result : m1 state
  case success val s' =>
    -- When m1 succeeds, isSuccess is trivially true
    simp [Contract.run, h_result, ContractResult.isSuccess]
  case revert msg s' =>
    -- When m1 reverts, bind also reverts, so isSuccess = false
    -- This contradicts h_success
    unfold DumbContracts.bind Contract.run at h_success
    simp [h_result, ContractResult.isSuccess] at h_success

/-!
## Address Storage Lemmas
-/

-- getStorageAddr preserves state
theorem getStorageAddr_runState (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runState state = state := by
  simp [getStorageAddr, Contract.runState]

-- setStorageAddr updates the state
theorem setStorageAddr_runState (slot : StorageSlot Address) (value : Address) (state : ContractState) :
    (setStorageAddr slot value).runState state =
      { state with storageAddr := fun s => if s == slot.slot then value else state.storageAddr s } := by
  simp [setStorageAddr, Contract.runState]

-- getStorageAddr returns correct value
theorem getStorageAddr_runValue (slot : StorageSlot Address) (state : ContractState) :
    (getStorageAddr slot).runValue state = state.storageAddr slot.slot := by
  simp [getStorageAddr, Contract.runValue]

/-!
## Mapping Operation Lemmas
-/

-- getMapping preserves state
theorem getMapping_runState (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runState state = state := by
  simp [getMapping, Contract.runState]

-- getMapping returns correct value
theorem getMapping_runValue (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runValue state = state.storageMap slot.slot key := by
  simp [getMapping, Contract.runValue]

/-!
## msgSender Lemmas
-/

-- msgSender preserves state
theorem msgSender_runState (state : ContractState) :
    msgSender.runState state = state := by
  simp [msgSender, Contract.runState]

-- msgSender returns sender
theorem msgSender_runValue (state : ContractState) :
    msgSender.runValue state = state.sender := by
  simp [msgSender, Contract.runValue]

/-!
## require Lemmas
-/

-- require with true condition is success
theorem require_true_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = true) :
    ((require cond msg).run state).isSuccess = true := by
  simp [require, h]

-- require with false condition is not success
theorem require_false_isSuccess (cond : Bool) (msg : String) (state : ContractState)
    (h : cond = false) :
    ((require cond msg).run state).isSuccess = false := by
  simp [require, h]

-- If require succeeds, the condition must have been true (reverse direction)
theorem require_success_implies_cond (cond : Bool) (msg : String) (state : ContractState) :
    ((require cond msg).run state).isSuccess = true →
    cond = true := by
  intro h_success
  -- Strategy: case analysis on cond
  cases cond
  case false =>
    -- When cond = false, require returns revert, which has isSuccess = false
    -- This contradicts h_success
    unfold require Contract.run at h_success
    simp [ContractResult.isSuccess] at h_success
  case true =>
    -- When cond = true, we're done
    rfl

/-!
## Address Equality Lemmas
-/

-- Address beq reflects equality (Address is String)
theorem address_beq_eq_true_iff_eq (a b : Address) :
    (a == b) = true ↔ a = b := by
  -- Address is String, so we can use String's BEq properties
  -- Use the decidable equality property
  simp only [beq_iff_eq]

/-!
## SpecStorage Lemmas

These lemmas about SpecStorage operations are currently placeholders.
They require more sophisticated reasoning about List operations.
-/

-- getSlot from setSlot (same slot)
theorem SpecStorage_getSlot_setSlot_same (storage : SpecStorage) (slot : Nat) (value : Nat) :
    (storage.setSlot slot value).getSlot slot = value := by
  -- After unfolding: List.lookup slot ((slot, value) :: filtered) = some value
  -- This is immediate since lookup finds (slot, value) at head
  unfold SpecStorage.getSlot SpecStorage.setSlot
  simp [List.lookup]

theorem lookup_filter_ne {β : Type} (k k' : Nat) (h : k ≠ k') (xs : List (Nat × β)) :
    (xs.filter (fun kv => kv.1 ≠ k')).lookup k = xs.lookup k := by
  induction xs with
  | nil =>
      simp
  | cons kv xs ih =>
      cases kv with
      | mk k0 v0 =>
          by_cases hk0 : k0 = k'
          · -- Filter drops this head.
            have hk0ne : k ≠ k0 := by
              intro hkk
              exact h (hkk.trans hk0)
            calc
              (List.filter (fun kv => kv.1 ≠ k') ((k0, v0) :: xs)).lookup k
                  = (List.filter (fun kv => kv.1 ≠ k') xs).lookup k := by
                      simp [List.filter, hk0]
              _ = xs.lookup k := ih
              _ = ((k0, v0) :: xs).lookup k := by
                      have hk0false : (k == k0) = false := by
                        exact (beq_eq_false_iff_ne.mpr hk0ne)
                      simp [List.lookup, hk0false]
          · -- Filter keeps this head.
            by_cases hk : k = k0
            · simp [List.filter, List.lookup, hk0, beq_iff_eq, hk]
            · calc
                (List.filter (fun kv => kv.1 ≠ k') ((k0, v0) :: xs)).lookup k
                    = (List.filter (fun kv => kv.1 ≠ k') xs).lookup k := by
                        have hkfalse : (k == k0) = false := by
                          exact (beq_eq_false_iff_ne.mpr hk)
                        simp [List.filter, List.lookup, hk0, hkfalse]
                _ = xs.lookup k := ih
                _ = ((k0, v0) :: xs).lookup k := by
                        have hkfalse : (k == k0) = false := by
                          exact (beq_eq_false_iff_ne.mpr hk)
                        simp [List.lookup, hkfalse]

-- lookup skips head when key is different
theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α]
    (k k' : α) (v : β) (xs : List (α × β)) (h : k ≠ k') :
    (List.lookup k ((k', v) :: xs)) = List.lookup k xs := by
  have hfalse : (k == k') = false := by
    exact (beq_eq_false_iff_ne.mpr h)
  simp [List.lookup, hfalse]

-- getSlot from setSlot (different slot)
theorem SpecStorage_getSlot_setSlot_diff (storage : SpecStorage) (slot1 slot2 : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setSlot slot1 value).getSlot slot2 = storage.getSlot slot2 := by
  -- After unfolding: List.lookup slot2 ((slot1, value) :: filtered)
  -- Since slot2 ≠ slot1, lookup skips head and searches in filtered list
  -- Key lemma needed: List.lookup k (List.filter (·.1 ≠ k') xs) = List.lookup k xs when k ≠ k'
  unfold SpecStorage.getSlot SpecStorage.setSlot
  have h' : slot2 ≠ slot1 := by
    intro h2
    exact h h2.symm
  have hfalse : (slot2 == slot1) = false := by
    exact (beq_eq_false_iff_ne.mpr h')
  have hpred : (fun x : Nat × Nat => !decide (x.1 = slot1)) = (fun x : Nat × Nat => decide (x.1 ≠ slot1)) := by
    funext x
    simp [decide_not]
  simp [List.lookup, hfalse, hpred, lookup_filter_ne slot2 slot1 h']

-- getMapping from setMapping (same slot and key) - requires proof
theorem SpecStorage_getMapping_setMapping_same (storage : SpecStorage) (slot : Nat) (key : Nat) (value : Nat) :
    (storage.setMapping slot key value).getMapping slot key = value := by
  unfold SpecStorage.getMapping SpecStorage.setMapping
  simp [List.lookup, beq_iff_eq, lookup_filter_ne]

-- getMapping preserves other slots - requires proof
theorem SpecStorage_getMapping_setMapping_diff_slot (storage : SpecStorage) (slot1 slot2 : Nat) (key : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setMapping slot1 key value).getMapping slot2 key = storage.getMapping slot2 key := by
  unfold SpecStorage.getMapping SpecStorage.setMapping
  have h' : slot2 ≠ slot1 := by
    intro h2
    exact h h2.symm
  have hfalse : (slot2 == slot1) = false := by
    exact (beq_eq_false_iff_ne.mpr h')
  have hpred : (fun x : Nat × List (Nat × Nat) => !decide (x.1 = slot1)) =
      (fun x : Nat × List (Nat × Nat) => decide (x.1 ≠ slot1)) := by
    funext x
    simp [decide_not]
  simp [List.lookup, hfalse, hpred, lookup_filter_ne slot2 slot1 h']

/-!
## Safe Arithmetic Lemmas

Helper lemmas for reasoning about safe arithmetic operations (safeAdd, safeSub).
-/

-- safeSub returns Some iff no underflow
theorem safeSub_some_iff_ge (a b : DumbContracts.Core.Uint256) :
    (DumbContracts.Stdlib.Math.safeSub a b).isSome ↔ (a : Nat) ≥ (b : Nat) := by
  unfold DumbContracts.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- safeSub returns None iff underflow
theorem safeSub_none_iff_lt (a b : DumbContracts.Core.Uint256) :
    (DumbContracts.Stdlib.Math.safeSub a b).isNone ↔ (a : Nat) < (b : Nat) := by
  unfold DumbContracts.Stdlib.Math.safeSub
  split
  · simp; rename_i h; omega
  · simp; rename_i h; omega

-- When safeSub succeeds, it returns the correct value
theorem safeSub_some_val (a b : DumbContracts.Core.Uint256) (h : (a : Nat) ≥ (b : Nat)) :
    DumbContracts.Stdlib.Math.safeSub a b = some (a - b) := by
  unfold DumbContracts.Stdlib.Math.safeSub
  have h_not : ¬((b : Nat) > (a : Nat)) := by omega
  simp [h_not]

-- safeAdd returns Some iff no overflow
theorem safeAdd_some_iff_le (a b : DumbContracts.Core.Uint256) :
    (DumbContracts.Stdlib.Math.safeAdd a b).isSome ↔
    (a : Nat) + (b : Nat) ≤ DumbContracts.Stdlib.Math.MAX_UINT256 := by
  unfold DumbContracts.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > DumbContracts.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro h_some
      simp [h] at h_some
    · intro h_le
      omega
  case neg =>
    constructor
    · intro _
      omega
    · intro _
      simp [h]

-- safeAdd returns None iff overflow
theorem safeAdd_none_iff_gt (a b : DumbContracts.Core.Uint256) :
    (DumbContracts.Stdlib.Math.safeAdd a b).isNone ↔
    (a : Nat) + (b : Nat) > DumbContracts.Stdlib.Math.MAX_UINT256 := by
  unfold DumbContracts.Stdlib.Math.safeAdd
  by_cases h : (a : Nat) + (b : Nat) > DumbContracts.Stdlib.Math.MAX_UINT256
  case pos =>
    constructor
    · intro _; exact h
    · intro _; simp [h]
  case neg =>
    constructor
    · intro h_none
      simp [h] at h_none
    · intro h_gt
      exact absurd h_gt h

-- When safeAdd succeeds, it returns the correct value
theorem safeAdd_some_val (a b : DumbContracts.Core.Uint256)
    (h : (a : Nat) + (b : Nat) ≤ DumbContracts.Stdlib.Math.MAX_UINT256) :
    DumbContracts.Stdlib.Math.safeAdd a b = some (a + b) := by
  unfold DumbContracts.Stdlib.Math.safeAdd
  have h_not : ¬((a : Nat) + (b : Nat) > DumbContracts.Stdlib.Math.MAX_UINT256) := by omega
  simp [h_not]

/-!
## Modular Arithmetic Wraparound Lemmas

These lemmas handle the case where modular addition causes wraparound at MAX_UINT256.
-/

-- Addition by 1 preserves order iff no overflow occurs
theorem add_one_preserves_order_iff_no_overflow (a : DumbContracts.Core.Uint256) :
    ((DumbContracts.Core.Uint256.add a 1) : Nat) > (a : Nat) ↔
    (a : Nat) < DumbContracts.Core.MAX_UINT256 := by
  -- Strategy: case split on whether a is at max or not
  by_cases h : (a : Nat) = DumbContracts.Core.MAX_UINT256
  case pos =>
    -- When a = MAX_UINT256, overflow occurs
    -- (MAX_UINT256 + 1) mod 2^256 = 0, and 0 ≯ MAX_UINT256
    constructor
    · intro h_gt
      -- Show contradiction: (a + 1).val = 0, so 0 > MAX_UINT256 is false
      unfold DumbContracts.Core.Uint256.add at h_gt
      simp [DumbContracts.Core.Uint256.ofNat, DumbContracts.Core.Uint256.val] at h_gt
      rw [h] at h_gt
      -- Now: (MAX_UINT256 + 1) % modulus > MAX_UINT256
      have h_mod : (DumbContracts.Core.MAX_UINT256 + 1) % DumbContracts.Core.Uint256.modulus = 0 := by
        have h_eq : DumbContracts.Core.MAX_UINT256 + 1 = DumbContracts.Core.Uint256.modulus := by
          exact DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus
        rw [h_eq]
        simp [Nat.mod_self]
      rw [h_mod] at h_gt
      -- Now: 0 > MAX_UINT256, which is false
      have h_max_pos : DumbContracts.Core.MAX_UINT256 > 0 := by
        unfold DumbContracts.Core.MAX_UINT256
        omega
      omega
    · intro h_lt
      -- a.val < MAX_UINT256 contradicts h : a.val = MAX_UINT256
      rw [h] at h_lt
      omega
  case neg =>
    -- When a < MAX_UINT256, no overflow occurs
    -- (a + 1) mod 2^256 = a + 1, so (a + 1) > a
    constructor
    · intro _
      -- From a.val ≤ MAX_UINT256 and a.val ≠ MAX_UINT256, we get a.val < MAX_UINT256
      have h_le : (a : Nat) ≤ DumbContracts.Core.MAX_UINT256 := by
        exact DumbContracts.Core.Uint256.val_le_max a
      omega
    · intro h_lt
      -- Show (a + 1).val > a.val when no overflow
      unfold DumbContracts.Core.Uint256.add
      simp [DumbContracts.Core.Uint256.ofNat, DumbContracts.Core.Uint256.val]
      -- Need to show: (a.val + 1) % modulus > a.val
      -- Since a.val < MAX_UINT256, we have a.val + 1 < modulus
      have h_sum_lt : (a : Nat) + 1 < DumbContracts.Core.Uint256.modulus := by
        have h_max : (a : Nat) < DumbContracts.Core.MAX_UINT256 := h_lt
        calc
          (a : Nat) + 1 < DumbContracts.Core.MAX_UINT256 + 1 := by omega
          _ = DumbContracts.Core.Uint256.modulus := by
            exact DumbContracts.Core.Uint256.max_uint256_succ_eq_modulus
      -- When a.val + 1 < modulus, the mod is identity
      have h_mod : ((a : Nat) + 1) % DumbContracts.Core.Uint256.modulus = (a : Nat) + 1 := by
        exact Nat.mod_eq_of_lt h_sum_lt
      rw [h_mod]
      omega

/-!
## Notes on Completing These Proofs

To fill in the `sorry` placeholders above, we need:

1. **List Lemmas**: Lemmas about `List.lookup`, `List.filter`, and their interactions
2. **SpecStorage Reasoning**: Understanding how the nested list structure works
3. **Case Analysis**: Systematic case splitting on list operations

The proven lemmas above (without `sorry`) provide the foundation for:
- Simple storage proofs (SimpleStorage, Counter)
- Address storage proofs (Owned, OwnedCounter, SimpleToken)
- Mapping proofs will require the SpecStorage lemmas to be completed

Recommended approach:
1. Start with SimpleStorage proofs using the basic storage lemmas
2. Develop list reasoning library for SpecStorage
3. Complete mapping-based contract proofs (Ledger, SimpleToken)
-/

end Compiler.Proofs.Automation
