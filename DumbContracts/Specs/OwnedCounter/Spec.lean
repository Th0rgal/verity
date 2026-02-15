/-
  Formal specifications for OwnedCounter operations.
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

/-- Constructor: sets owner -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

/-- getCount: returns current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns current owner -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- increment: increases count by 1 (owner only) -/
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = add (s.storage 1) 1 ∧
  storageUnchangedExcept 1 s s' ∧
  sameAddrMapContext s s'

/-- decrement: decreases count by 1 (owner only) -/
def decrement_spec (s s' : ContractState) : Prop :=
  s'.storage 1 = sub (s.storage 1) 1 ∧
  storageUnchangedExcept 1 s s' ∧
  sameAddrMapContext s s'

/-- transferOwnership: changes owner (owner only) -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = newOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

end DumbContracts.Specs.OwnedCounter
