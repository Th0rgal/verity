/-
  Verity.Proofs.Stdlib.MappingAutomation

  Extended automation lemmas for mapping operations.
  These lemmas help prove properties about getMapping, setMapping, getMapping2, and setMapping2.

  Status: All lemmas fully proven with zero sorry.
-/

import Verity.Core
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

theorem setMapping_getMapping_same (slot : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (state : ContractState) :
    (getMapping slot key).runValue ((setMapping slot key value).runState state) = value := by
  simp [getMapping, setMapping, Contract.runState, Contract.runValue]

/-!
## Uint256-Keyed Mapping Lemmas (Uint256 → Uint256)
-/

theorem getMappingUint_runState (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
    (getMappingUint slot key).runState state = state := by
  simp [getMappingUint, Contract.runState]

theorem getMappingUint_runValue (slot : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
    (getMappingUint slot key).runValue state = state.storageMapUint slot.slot key := by
  simp [getMappingUint, Contract.runValue]

/-!
## Double Mapping Lemmas (Address → Address → Uint256)
-/

theorem getMapping2_runState (slot : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
    (getMapping2 slot key1 key2).runState state = state := by
  simp [getMapping2, Contract.runState]

theorem getMapping2_runValue (slot : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
    (getMapping2 slot key1 key2).runValue state = state.storageMap2 slot.slot key1 key2 := by
  simp [getMapping2, Contract.runValue]

end Verity.Proofs.Stdlib.MappingAutomation
