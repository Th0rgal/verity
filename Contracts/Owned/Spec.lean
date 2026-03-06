/-
  Formal specifications for Owned operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Contracts.MacroContracts.Core

namespace Contracts.Owned.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.Owned

/-! ## Operation Specifications -/

-- Constructor: sets the owner to the provided address.
#gen_spec_addr constructor_spec for (initialOwner : Address) (0, (fun _ => initialOwner), sameStorageMapContext)

/-- getOwner: returns the current owner address -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

-- transferOwnership: updates owner to new address (owner only).
#gen_spec_addr transferOwnership_spec for (newOwner : Address) (0, (fun _ => newOwner), sameStorageMapContext)

/-- isOwner: returns true if sender equals current owner -/
def isOwner_spec (result : Bool) (s : ContractState) : Prop :=
  result = (s.sender == s.storageAddr 0)

end Contracts.Owned.Spec
