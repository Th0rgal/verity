/-
  State invariants for SimpleStorage contract.
-/

import Verity.Specs.Common

namespace Verity.Specs.SimpleStorage

open Verity

/-- Basic well-formedness: addresses are nonzero -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0

/-- Storage slot isolation: operations on slot 0 don't affect other slots -/
def storage_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 0 → s'.storage slot = s.storage slot

/-- Address storage unchanged by Uint256 storage operations -/
abbrev addr_storage_unchanged := Specs.sameStorageAddr

/-- Mapping storage unchanged by Uint256 storage operations -/
abbrev map_storage_unchanged := Specs.sameStorageMap

/-- Context preservation -/
abbrev context_preserved := Specs.sameContext

end Verity.Specs.SimpleStorage
