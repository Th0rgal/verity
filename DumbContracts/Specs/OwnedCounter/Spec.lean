/-
  Formal specifications for OwnedCounter contract operations.

  OwnedCounter composes ownership and counter patterns:
  - Slot 0 (Address): owner
  - Slot 1 (Uint256): count
  - Owner-only guard on increment/decrement/transferOwnership
  - Public reads for getCount and getOwner
-/

import DumbContracts.Core
import DumbContracts.Examples.OwnedCounter

namespace DumbContracts.Specs.OwnedCounter

open DumbContracts
open DumbContracts.Examples.OwnedCounter

/-! ## Operation Specifications -/

/-- Constructor: sets owner, does not touch count slot -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  s'.storage = s.storage ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot) ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- getCount: returns count from slot 1, no state change -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns owner from addr slot 0, no state change -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- increment (when owner): count increases by 1, owner unchanged, context preserved -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = s.storage 1 + 1 ∧
  (∀ slot : Nat, slot ≠ 1 → s'.storage slot = s.storage slot) ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- decrement (when owner): count decreases by 1, owner unchanged, context preserved -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = s.storage 1 - 1 ∧
  (∀ slot : Nat, slot ≠ 1 → s'.storage slot = s.storage slot) ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- transferOwnership (when owner): changes owner, count unchanged -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = newOwner ∧
  (∀ slot : Nat, slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot) ∧
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

end DumbContracts.Specs.OwnedCounter
