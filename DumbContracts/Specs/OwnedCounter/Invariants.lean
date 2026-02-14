/-
  State invariants for OwnedCounter contract.

  Key property: ownership and counter storage are independent —
  owner operations don't touch count, and count operations don't touch owner.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.OwnedCounter

open DumbContracts

/-! ## State Invariants -/

/-- Well-formed state after construction -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""
  owner_nonempty : s.storageAddr 0 ≠ ""

/-- Storage isolation: count operations don't touch owner -/
def count_preserves_owner (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

/-- Storage isolation: owner operations don't touch count -/
def owner_preserves_count (s s' : ContractState) : Prop :=
  s'.storage = s.storage

/-- Context preserved across all operations -/
abbrev context_preserved := Specs.sameContext

end DumbContracts.Specs.OwnedCounter
