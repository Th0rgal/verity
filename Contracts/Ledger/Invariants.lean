/-
  State invariants for Ledger contract.
-/

import DumbContracts.Core

namespace Contracts.Ledger.Invariants

open DumbContracts

/-! ## State Invariants -/

/-- Well-formed state -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

/-- Context preserved across operations -/
def context_preserved (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Non-mapping storage unchanged by all Ledger operations -/
def non_mapping_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧ s'.storageAddr = s.storageAddr

end Contracts.Ledger.Invariants
