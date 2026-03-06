/-
  Formal specifications for SimpleStorage operations.
-/

import Verity.Specs.Common
import Verity.Macro
import Contracts.MacroContracts.Core

namespace Contracts.SimpleStorage.Spec

open Verity
open Verity.Specs

-- Store: updates the storage at slot 0.
#gen_spec store_spec for (value : Uint256) (0, (fun _ => value), sameAddrMapContext)

/-- Retrieve: returns the value at slot 0 -/
def retrieve_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

/-- Store then retrieve returns the stored value -/
def store_retrieve_roundtrip (value : Uint256) (s : ContractState) : Prop :=
  ∀ s_after_store : ContractState,
    store_spec value s s_after_store →
    retrieve_spec value s_after_store

end Contracts.SimpleStorage.Spec
