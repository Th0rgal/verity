/-
  Verity.Proofs.Stdlib.MappingAutomation

  Extended automation lemmas for mapping operations.
  These lemmas help prove properties about getMapping, setMapping, getMapping2,
  setMapping2, getMappingUint, and setMappingUint.

  ## Sections

  - Address-Keyed Mapping Lemmas: get/set/preservation for (Address → Uint256)
  - Uint256-Keyed Mapping Lemmas: get/set/preservation for (Uint256 → Uint256)
  - Double Mapping Lemmas: get/set/preservation for (Address → Address → Uint256)

  Status: All lemmas fully proven with zero sorry.
-/

import Verity.Proofs.Stdlib.Automation

namespace Verity.Proofs.Stdlib.MappingAutomation

open Verity
open Verity.Proofs.Stdlib.Automation

/-!
## Address-Keyed Mapping Lemmas (Address → Uint256)
-/

theorem getMapping_runState (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runState state = state :=
  Automation.getMapping_runState slot key state

theorem getMapping_runValue (slot : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
    (getMapping slot key).runValue state = state.storageMap slot.slot key :=
  Automation.getMapping_runValue slot key state

/-- setMapping updates storageMap and knownAddresses. -/
theorem setMapping_runState (slot : StorageSlot (Address → Uint256)) (key : Address)
    (value : Uint256) (state : ContractState) :
    (setMapping slot key value).runState state =
      { state with
        storageMap := fun s addr =>
          if s == slot.slot && addr == key then value
          else state.storageMap s addr,
        knownAddresses := fun s =>
          if s == slot.slot then
            (state.knownAddresses s).insert key
          else
            state.knownAddresses s } := by
  simp [setMapping, Contract.runState]

/-- After setMapping, getMapping on the same key returns the set value. -/
theorem setMapping_getMapping_same (slot : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (state : ContractState) :
    (getMapping slot key).runValue ((setMapping slot key value).runState state) = value := by
  simp [getMapping, setMapping, Contract.runState, Contract.runValue]

/-- setMapping on one key preserves getMapping on a different key (same slot). -/
theorem setMapping_getMapping_diff (slot : StorageSlot (Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) (h : key1 ≠ key2) :
    (getMapping slot key2).runValue ((setMapping slot key1 value).runState state) =
    state.storageMap slot.slot key2 := by
  simp only [getMapping, setMapping, Contract.runState, Contract.runValue]
  have : (key2 == key1) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- setMapping preserves storageMap on a different slot. -/
theorem setMapping_preserves_other_slot (slot1 : StorageSlot (Address → Uint256))
    (slot2 : Nat) (key : Address) (value : Uint256) (state : ContractState)
    (h : slot1.slot ≠ slot2) :
    ((setMapping slot1 key value).runState state).storageMap slot2 =
    state.storageMap slot2 := by
  simp only [setMapping, Contract.runState]
  funext addr
  have h_slot : (slot2 == slot1.slot) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [h_slot]

/-!
## Uint256-Keyed Mapping Lemmas (Uint256 → Uint256)
-/

theorem getMappingUint_runState (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
    (getMappingUint slot key).runState state = state := by
  simp [getMappingUint, Contract.runState]

theorem getMappingUint_runValue (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
    (getMappingUint slot key).runValue state = state.storageMapUint slot.slot key := by
  simp [getMappingUint, Contract.runValue]

/-- setMappingUint updates storageMapUint. -/
theorem setMappingUint_runState (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (value : Uint256) (state : ContractState) :
    (setMappingUint slot key value).runState state =
      { state with
        storageMapUint := fun s k =>
          if s == slot.slot && k == key then value
          else state.storageMapUint s k } := by
  simp [setMappingUint, Contract.runState]

/-- After setMappingUint, getMappingUint on the same key returns the set value. -/
theorem setMappingUint_getMappingUint_same (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    (getMappingUint slot key).runValue ((setMappingUint slot key value).runState state) = value := by
  simp [getMappingUint, setMappingUint, Contract.runState, Contract.runValue]

/-- setMappingUint on one key preserves getMappingUint on a different key (same slot). -/
theorem setMappingUint_getMappingUint_diff (slot : StorageSlot (Uint256 → Uint256))
    (key1 key2 : Uint256) (value : Uint256) (state : ContractState) (h : key1 ≠ key2) :
    (getMappingUint slot key2).runValue ((setMappingUint slot key1 value).runState state) =
    state.storageMapUint slot.slot key2 := by
  simp only [getMappingUint, setMappingUint, Contract.runState, Contract.runValue]
  have : (key2 == key1) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- setMappingUint preserves uint256 storage. -/
theorem setMappingUint_preserves_storage (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.storage = state.storage := by
  simp [setMappingUint]

/-- setMappingUint preserves address storage. -/
theorem setMappingUint_preserves_storageAddr (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.storageAddr = state.storageAddr := by
  simp [setMappingUint]

/-- setMappingUint preserves address-keyed mapping storage. -/
theorem setMappingUint_preserves_storageMap (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.storageMap = state.storageMap := by
  simp [setMappingUint]

/-- setMappingUint preserves double mapping storage. -/
theorem setMappingUint_preserves_storageMap2 (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.storageMap2 = state.storageMap2 := by
  simp [setMappingUint]

/-- setMappingUint preserves sender. -/
theorem setMappingUint_preserves_sender (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.sender = state.sender := by
  simp [setMappingUint]

/-- setMappingUint preserves contract address. -/
theorem setMappingUint_preserves_thisAddress (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.thisAddress = state.thisAddress := by
  simp [setMappingUint]

/-- setMappingUint preserves known addresses. -/
theorem setMappingUint_preserves_knownAddresses (slot : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (value : Uint256) (state : ContractState) :
    ((setMappingUint slot key value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [setMappingUint]

/-!
## Double Mapping Lemmas (Address → Address → Uint256)
-/

theorem getMapping2_runState (slot : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
    (getMapping2 slot key1 key2).runState state = state := by
  simp [getMapping2, Contract.runState]

theorem getMapping2_runValue (slot : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
    (getMapping2 slot key1 key2).runValue state = state.storageMap2 slot.slot key1 key2 := by
  simp [getMapping2, Contract.runValue]

/-- setMapping2 updates storageMap2. -/
theorem setMapping2_runState (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    (setMapping2 slot key1 key2 value).runState state =
      { state with
        storageMap2 := fun s addr1 addr2 =>
          if s == slot.slot && addr1 == key1 && addr2 == key2 then value
          else state.storageMap2 s addr1 addr2 } := by
  simp [setMapping2, Contract.runState]

/-- After setMapping2, getMapping2 on the same keys returns the set value. -/
theorem setMapping2_getMapping2_same (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    (getMapping2 slot key1 key2).runValue ((setMapping2 slot key1 key2 value).runState state) = value := by
  simp [getMapping2, setMapping2, Contract.runState, Contract.runValue]

/-- setMapping2 with different first key preserves getMapping2. -/
theorem setMapping2_getMapping2_diff_key1 (slot : StorageSlot (Address → Address → Uint256))
    (k1 k1' k2 k2' : Address) (value : Uint256) (state : ContractState) (h : k1 ≠ k1') :
    (getMapping2 slot k1' k2').runValue ((setMapping2 slot k1 k2 value).runState state) =
    state.storageMap2 slot.slot k1' k2' := by
  simp only [getMapping2, setMapping2, Contract.runState, Contract.runValue]
  have : (k1' == k1) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- setMapping2 with different second key preserves getMapping2. -/
theorem setMapping2_getMapping2_diff_key2 (slot : StorageSlot (Address → Address → Uint256))
    (k1 k2 k2' : Address) (value : Uint256) (state : ContractState) (h : k2 ≠ k2') :
    (getMapping2 slot k1 k2').runValue ((setMapping2 slot k1 k2 value).runState state) =
    state.storageMap2 slot.slot k1 k2' := by
  simp only [getMapping2, setMapping2, Contract.runState, Contract.runValue]
  have : (k2' == k2) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
  simp [this]

/-- setMapping2 preserves uint256 storage. -/
theorem setMapping2_preserves_storage (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.storage = state.storage := by
  simp [setMapping2]

/-- setMapping2 preserves address storage. -/
theorem setMapping2_preserves_storageAddr (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.storageAddr = state.storageAddr := by
  simp [setMapping2]

/-- setMapping2 preserves address-keyed mapping storage. -/
theorem setMapping2_preserves_storageMap (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.storageMap = state.storageMap := by
  simp [setMapping2]

/-- setMapping2 preserves uint256-keyed mapping storage. -/
theorem setMapping2_preserves_storageMapUint (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.storageMapUint = state.storageMapUint := by
  simp [setMapping2]

/-- setMapping2 preserves sender. -/
theorem setMapping2_preserves_sender (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.sender = state.sender := by
  simp [setMapping2]

/-- setMapping2 preserves contract address. -/
theorem setMapping2_preserves_thisAddress (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.thisAddress = state.thisAddress := by
  simp [setMapping2]

/-- setMapping2 preserves known addresses. -/
theorem setMapping2_preserves_knownAddresses (slot : StorageSlot (Address → Address → Uint256))
    (key1 key2 : Address) (value : Uint256) (state : ContractState) :
    ((setMapping2 slot key1 key2 value).run state).snd.knownAddresses = state.knownAddresses := by
  simp [setMapping2]

/-!
## Cross-Type Preservation: setMapping vs other storage types
-/

/-- setMapping preserves uint256-keyed mapping storage. -/
theorem setMapping_preserves_storageMapUint (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storageMapUint = state.storageMapUint := by
  simp [setMapping]

/-- setMapping preserves double mapping storage. -/
theorem setMapping_preserves_storageMap2 (slot : StorageSlot (Address → Uint256))
    (key : Address) (value : Uint256) (state : ContractState) :
    ((setMapping slot key value).run state).snd.storageMap2 = state.storageMap2 := by
  simp [setMapping]

/-!
## Cross-Type Preservation: setStorage vs additional mapping types
-/

/-- setStorage preserves uint256-keyed mapping storage. -/
theorem setStorage_preserves_storageMapUint (slot : StorageSlot Uint256)
    (value : Uint256) (state : ContractState) :
    ((setStorage slot value).run state).snd.storageMapUint = state.storageMapUint := by
  simp [setStorage]

/-- setStorage preserves double mapping storage. -/
theorem setStorage_preserves_storageMap2 (slot : StorageSlot Uint256)
    (value : Uint256) (state : ContractState) :
    ((setStorage slot value).run state).snd.storageMap2 = state.storageMap2 := by
  simp [setStorage]

/-- setStorageAddr preserves uint256-keyed mapping storage. -/
theorem setStorageAddr_preserves_storageMapUint (slot : StorageSlot Address)
    (value : Address) (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storageMapUint = state.storageMapUint := by
  simp [setStorageAddr]

/-- setStorageAddr preserves double mapping storage. -/
theorem setStorageAddr_preserves_storageMap2 (slot : StorageSlot Address)
    (value : Address) (state : ContractState) :
    ((setStorageAddr slot value).run state).snd.storageMap2 = state.storageMap2 := by
  simp [setStorageAddr]

end Verity.Proofs.Stdlib.MappingAutomation
