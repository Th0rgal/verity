/-
  SimpleStorage: Formal Specification

  This file defines the formal specification of what SimpleStorage
  should do, separate from how it's implemented.
-/

import DumbContracts.Core

namespace DumbContracts.Specs.SimpleStorage

open DumbContracts

-- What store should do: update the storage at slot 0
def store_spec (value : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 0 = value ∧
  -- Other storage slots unchanged
  (∀ slot : Nat, slot ≠ 0 → s'.storage slot = s.storage slot) ∧
  -- Context unchanged
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  -- Other storage types unchanged
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap

-- What retrieve should do: return the value at slot 0
def retrieve_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

-- Combined property: store then retrieve returns the stored value
def store_retrieve_roundtrip (value : Uint256) (s : ContractState) : Prop :=
  ∀ s_after_store : ContractState,
    store_spec value s s_after_store →
    retrieve_spec value s_after_store

end DumbContracts.Specs.SimpleStorage
