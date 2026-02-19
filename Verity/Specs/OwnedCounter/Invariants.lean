/-
  State invariants for OwnedCounter contract.

  Key property: ownership and counter storage are independent —
  owner operations don't touch count, and count operations don't touch owner.
-/

import Verity.Specs.Common

namespace Verity.Specs.OwnedCounter

open Verity

/-! ## State Invariants -/

/-- Well-formed state after construction -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr 0 ≠ 0

/-- Storage isolation: count operations don't touch owner -/
def count_preserves_owner (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

/-- Storage isolation: owner operations don't touch count -/
def owner_preserves_count (s s' : ContractState) : Prop :=
  s'.storage = s.storage

/-- Context preserved across all operations -/
abbrev context_preserved := Specs.sameContext

end Verity.Specs.OwnedCounter
