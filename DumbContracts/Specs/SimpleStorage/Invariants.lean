/-
  SimpleStorage: State Invariants

  This file defines properties that should hold for all valid
  ContractState instances used with SimpleStorage.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common

namespace DumbContracts.Specs.SimpleStorage

open DumbContracts

-- Basic well-formedness of ContractState
-- (In SimpleStorage, this is trivial since we don't have complex invariants)
structure WellFormedState (s : ContractState) : Prop where
  -- Sender is not empty (basic sanity check)
  sender_nonempty : s.sender ≠ ""
  -- Contract address is not empty
  contract_nonempty : s.thisAddress ≠ ""

-- Storage slot isolation: operations on slot 0 don't affect other slots
def storage_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 0 → s'.storage slot = s.storage slot

-- Address storage unchanged by Uint256 storage operations
def addr_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr

-- Mapping storage unchanged by Uint256 storage operations
def map_storage_unchanged (s s' : ContractState) : Prop :=
  s'.storageMap = s.storageMap

-- Context preservation: operations don't change sender/address
abbrev context_preserved := Specs.sameContext

end DumbContracts.Specs.SimpleStorage
