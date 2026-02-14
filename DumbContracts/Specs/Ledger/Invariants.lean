/-
  State invariants for Ledger contract.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.Ledger

open DumbContracts

/-! ## State Invariants -/

/-- Well-formed state -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

/-- Context preserved across operations -/
abbrev context_preserved := Specs.sameContext

/-- Non-mapping storage unchanged by all Ledger operations -/
def non_mapping_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧ s'.storageAddr = s.storageAddr

end DumbContracts.Specs.Ledger
