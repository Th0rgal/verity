/-
  State invariants for SimpleToken

  This file defines properties that should hold in any valid SimpleToken state.
  These invariants are crucial for proving correctness of token operations.
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Specs.SimpleToken

open DumbContracts
open DumbContracts.EVM.Uint256

/-! ## State Invariants

Properties that should always hold in a well-formed SimpleToken state.
-/

/-- Basic well-formedness: addresses are non-empty -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""
  owner_nonempty : s.storageAddr 0 ≠ ""

/-- All balances are non-negative
    Note: In our Uint256 model, this is implicit, but we state it for clarity
-/
def balances_non_negative (s : ContractState) : Prop :=
  ∀ addr : Address, s.storageMap 1 addr ≥ 0

/-- Total supply is non-negative -/
def supply_non_negative (s : ContractState) : Prop :=
  s.storage 2 ≥ 0

/-- Total supply equals sum of all balances
    Note: This is the key invariant for token correctness.
    In a finite model, this would be: totalSupply = Σ addr, balance[addr]

    For our infinite address space model, we express this differently:
    "Any finite subset of addresses has balances that don't exceed total supply"
-/
def sum_balances (s : ContractState) (addrs : List Address) : Uint256 :=
  (addrs.map (fun addr => s.storageMap 1 addr)).sum

def supply_bounds_balances (s : ContractState) : Prop :=
  ∀ addrs : List Address, sum_balances s addrs ≤ s.storage 2

-- Scoped helper for future total-supply proofs.
private def supply_equals_sum (s : ContractState) (addrs : List Address) : Prop :=
  s.storage 2 = sum_balances s addrs

/-- Owner cannot change except through transferOwnership (which doesn't exist yet) -/
def owner_stable (s s' : ContractState) : Prop :=
  s'.storageAddr 0 = s.storageAddr 0

/-- Total supply storage isolation -/
def supply_storage_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 2 → s'.storage slot = s.storage slot

/-- Balance mapping isolation -/
def balance_mapping_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 1 → ∀ addr : Address, s'.storageMap slot addr = s.storageMap slot addr

/-- Owner address isolation -/
def owner_addr_isolated (s s' : ContractState) (slot : Nat) : Prop :=
  slot ≠ 0 → s'.storageAddr slot = s.storageAddr slot

/-- Context preservation (sender, contract address unchanged) -/
def context_preserved (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- State preserved except for specific modifications -/
def state_preserved_except (s s' : ContractState)
  (modified_addr_slots : List Nat)
  (modified_uint_slots : List Nat)
  (modified_map_slots : List Nat) : Prop :=
  (∀ slot : Nat, slot ∉ modified_addr_slots → s'.storageAddr slot = s.storageAddr slot) ∧
  (∀ slot : Nat, slot ∉ modified_uint_slots → s'.storage slot = s.storage slot) ∧
  (∀ slot : Nat, slot ∉ modified_map_slots → ∀ addr : Address, s'.storageMap slot addr = s.storageMap slot addr) ∧
  context_preserved s s'

/-- Transfer preserves total supply -/
def transfer_preserves_supply (s s' : ContractState) : Prop :=
  s'.storage 2 = s.storage 2

/-- Mint increases total supply by exactly the minted amount -/
def mint_increases_supply (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 2 = add (s.storage 2) amount

/-- Access control: only owner can mint
    Note: This requires modeling of the require/onlyOwner guard
-/
def only_owner_can_mint (s : ContractState) : Prop :=
  s.sender = s.storageAddr 0

end DumbContracts.Specs.SimpleToken
