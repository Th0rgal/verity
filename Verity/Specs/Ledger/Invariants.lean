/-
  State invariants for Ledger contract.
-/

import Verity.Specs.Common

namespace Verity.Specs.Ledger

open Verity

/-! ## State Invariants -/

/-- Well-formed state -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0

/-- Context preserved across operations -/
abbrev context_preserved := Specs.sameContext

/-- Non-mapping storage unchanged by all Ledger operations -/
abbrev non_mapping_storage_unchanged (s s' : ContractState) :=
  Specs.sameStorage s s' ∧ Specs.sameStorageAddr s s'

end Verity.Specs.Ledger
