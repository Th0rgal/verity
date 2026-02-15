/-
  Formal specifications for Owned operations.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.Examples.Owned

namespace DumbContracts.Specs.Owned

open DumbContracts
open DumbContracts.Examples.Owned

/-! ## Operation Specifications -/

/-- Constructor: sets the owner to the provided address -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = initialOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

/-- getOwner: returns the current owner address -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- transferOwnership: updates owner to new address (owner only) -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = newOwner ∧
  storageAddrUnchangedExcept 0 s s' ∧
  sameStorageMapContext s s'

/-- isOwner: returns true if sender equals current owner -/
def isOwner_spec (result : Bool) (s : ContractState) : Prop :=
  result = (s.sender == s.storageAddr 0)

/-! ## Combined Specifications -/

/-- Constructor followed by getOwner returns the initial owner -/
def constructor_getOwner_spec (initialOwner : Address) (_s : ContractState) (result : Address) : Prop :=
  result = initialOwner

/-- TransferOwnership followed by getOwner returns the new owner -/
def transfer_getOwner_spec (newOwner : Address) (_s : ContractState) (result : Address) : Prop :=
  result = newOwner

end DumbContracts.Specs.Owned
