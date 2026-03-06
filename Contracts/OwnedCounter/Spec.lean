/-
  Formal specifications for OwnedCounter operations.
-/

import Verity.Specs.Common
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Contracts.OwnedCounter.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.OwnedCounter
open Verity.EVM.Uint256

/-! ## Operation Specifications -/

/-- Constructor: sets owner -/
def constructor_spec (initialOwner : Address) (s s' : ContractState) : Prop :=
  storageAddrUpdateSpec 0 (fun _ => initialOwner) sameStorageMapContext s s'

/-- getCount: returns current count -/
def getCount_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

/-- getOwner: returns current owner -/
def getOwner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

/-- increment: increases count by 1 (owner only) -/
def increment_spec (s s' : ContractState) : Prop :=
  storageUpdateSpec 1 (fun st => add (st.storage 1) 1) sameAddrMapContext s s'

/-- decrement: decreases count by 1 (owner only) -/
def decrement_spec (s s' : ContractState) : Prop :=
  storageUpdateSpec 1 (fun st => sub (st.storage 1) 1) sameAddrMapContext s s'

/-- transferOwnership: changes owner (owner only) -/
def transferOwnership_spec (newOwner : Address) (s s' : ContractState) : Prop :=
  storageAddrUpdateSpec 0 (fun _ => newOwner) sameStorageMapContext s s'

end Contracts.OwnedCounter.Spec
