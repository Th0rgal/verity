/-
  State invariants for Owned contract.

  Defines properties that should always hold, regardless of operations.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.Owned

open DumbContracts

/-! ## State Invariants

Properties that should be maintained by all operations.
-/

/-- Well-formed contract state:
    - Sender address is non-empty
    - Contract address is non-empty
    - Owner address is non-empty (after construction)
-/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""
  owner_nonempty : s.storageAddr 0 ≠ ""

/-- Storage isolation: Operations on owner slot don't affect other address slots -/
def addr_storage_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot

/-- Uint256 storage unchanged: Owner operations don't touch Uint256 storage -/
def uint_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storage = s.storage

/-- Mapping storage unchanged: Owner operations don't touch mapping storage -/
def map_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

/-- Contract context preserved: Operations don't change sender or contract address -/
abbrev context_preserved := Specs.sameContext

/-- Complete state preservation except for owner:
    Everything except owner slot remains unchanged
-/
def state_preserved_except_owner (s s' : ContractState) : Prop :=
  addr_storage_isolated s s' 0 ∧
  uint_storage_unchanged s s' ∧
  map_storage_unchanged s s' ∧
  context_preserved s s'

/-- Access control invariant: Only the owner should be able to change ownership
    This is enforced by the onlyOwner guard in transferOwnership
-/
def access_control_enforced (s : ContractState) : Prop :=
  s.sender = s.storageAddr 0

end DumbContracts.Specs.Owned
