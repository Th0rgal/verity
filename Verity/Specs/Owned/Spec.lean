/-
  Formal specifications for Owned operations.
-/

import Verity.Core
import Verity.Specs.Common
import Verity.Examples.Owned

namespace Verity.Specs.Owned

open Verity
open Verity.Examples.Owned

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

end Verity.Specs.Owned
