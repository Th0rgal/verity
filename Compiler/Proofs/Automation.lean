/-
  Compiler.Proofs.Automation

  Helper lemmas and automation for proving specification correctness.

  This module provides proven lemmas for Contract monad operations,
  storage operations, and common proof patterns.

  Status: Foundational lemmas - many require additional list reasoning.
  These lemmas establish the patterns needed for filling in Layer 1 proofs.
-/

import DumbContracts.Core
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
  sorry  -- Requires case analysis on if-then-else

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

/-!
## SpecStorage Lemmas

These lemmas about SpecStorage operations are currently placeholders.
They require more sophisticated reasoning about List operations.
-/

-- getSlot from setSlot (same slot) - requires proof
theorem SpecStorage_getSlot_setSlot_same (storage : SpecStorage) (slot : Nat) (value : Nat) :
    (storage.setSlot slot value).getSlot slot = value := by
  sorry  -- Requires list reasoning

-- getSlot from setSlot (different slot) - requires proof
theorem SpecStorage_getSlot_setSlot_diff (storage : SpecStorage) (slot1 slot2 : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setSlot slot1 value).getSlot slot2 = storage.getSlot slot2 := by
  sorry  -- Requires list reasoning

-- getMapping from setMapping (same slot and key) - requires proof
theorem SpecStorage_getMapping_setMapping_same (storage : SpecStorage) (slot : Nat) (key : Nat) (value : Nat) :
    (storage.setMapping slot key value).getMapping slot key = value := by
  sorry  -- Requires nested list reasoning

-- getMapping preserves other slots - requires proof
theorem SpecStorage_getMapping_setMapping_diff_slot (storage : SpecStorage) (slot1 slot2 : Nat) (key : Nat) (value : Nat)
    (h : slot1 ≠ slot2) :
    (storage.setMapping slot1 key value).getMapping slot2 key = storage.getMapping slot2 key := by
  sorry  -- Requires list reasoning

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
