/-
  Formal specifications for Owned operations.
-/

import Verity.Specs.Common
import Contracts.MacroContracts.Core

namespace Contracts.Owned.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.Owned

/-! ## Operation Specifications -/

/-- Constructor: sets the owner to the provided address -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  storageAddrUpdateSpec 0 (fun _ => initialOwner) sameStorageMapContext s s'

/-- getOwner: returns the current owner address -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- transferOwnership: updates owner to new address (owner only) -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  storageAddrUpdateSpec 0 (fun _ => newOwner) sameStorageMapContext s s'

/-- isOwner: returns true if sender equals current owner -/
def isOwner_spec (result : Bool) (s : ContractState) : Prop :=
  result = (s.sender == s.storageAddr 0)

end Contracts.Owned.Spec
