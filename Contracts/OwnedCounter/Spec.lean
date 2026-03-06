/-
  Formal specifications for OwnedCounter operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Contracts.OwnedCounter.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.OwnedCounter
open Verity.EVM.Uint256

/-! ## Operation Specifications -/

-- Constructor: sets owner.
#gen_spec_addr constructor_spec for (initialOwner : Address) (0, (fun _ => initialOwner), sameStorageMapContext)

/-- getCount: returns current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns current owner -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

-- increment: increases count by 1 (owner only)
#gen_spec increment_spec (1, (fun st => add (st.storage 1) 1), sameAddrMapContext)

-- decrement: decreases count by 1 (owner only)
#gen_spec decrement_spec (1, (fun st => sub (st.storage 1) 1), sameAddrMapContext)

-- transferOwnership: changes owner (owner only).
#gen_spec_addr transferOwnership_spec for (newOwner : Address) (0, (fun _ => newOwner), sameStorageMapContext)

end Contracts.OwnedCounter.Spec
