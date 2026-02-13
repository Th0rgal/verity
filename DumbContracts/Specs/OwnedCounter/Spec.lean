/-
  Formal specifications for OwnedCounter contract operations.

  OwnedCounter composes ownership and counter patterns:
  - Slot 0 (Address): owner
  - Slot 1 (Uint256): count
  - Owner-only guard on increment/decrement/transferOwnership
  - Public reads for getCount and getOwner
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.OwnedCounter

namespace DumbContracts.Specs.OwnedCounter

open DumbContracts
open DumbContracts.Examples.OwnedCounter
open DumbContracts.EVM.Uint256

/-! ## Operation Specifications -/

/-- Constructor: sets owner, does not touch count slot -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

/-- getCount: returns count from slot 1, no state change -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns owner from addr slot 0, no state change -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- increment (when owner): count increases by 1, owner unchanged, context preserved -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = add (s.storage 1) 1 ∧
  storageUnchangedExcept 1 s s' ∧
  sameAddrMapContext s s'

/-- decrement (when owner): count decreases by 1, owner unchanged, context preserved -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = sub (s.storage 1) 1 ∧
  storageUnchangedExcept 1 s s' ∧
  sameAddrMapContext s s'

/-- transferOwnership (when owner): changes owner, count unchanged -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = newOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

end DumbContracts.Specs.OwnedCounter
