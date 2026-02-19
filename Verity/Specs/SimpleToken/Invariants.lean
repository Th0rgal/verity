/-
  State invariants for SimpleToken contract.
-/

import Verity.Core
import Verity.Specs.Common
import Verity.EVM.Uint256

namespace Verity.Specs.SimpleToken

open Verity
open Verity.EVM.Uint256

/-! ## State Invariants -/

/-- Basic well-formedness: addresses are non-empty -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""
  owner_nonempty : s.storageAddr 0 ≠ ""

/-- All balances are non-negative (implicit in Uint256 model) -/
def balances_non_negative (s : ContractState) : Prop :=
  ∀ addr : Address, s.storageMap 1 addr ≥ 0

/-- Total supply is non-negative -/
def supply_non_negative (s : ContractState) : Prop :=
  s.storage 2 ≥ 0

/-- Sum balances over a list of addresses -/
def sum_balances (s : ContractState) (addrs : List Address) : Uint256 :=
  (addrs.map (fun addr => s.storageMap 1 addr)).sum

/-- Total supply bounds all finite subsets of balances -/
def supply_bounds_balances (s : ContractState) : Prop :=
  ∀ addrs : List Address, sum_balances s addrs ≤ s.storage 2

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
abbrev context_preserved := Specs.sameContext

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

/-- Access control: only owner can mint -/
def only_owner_can_mint (s : ContractState) : Prop :=
  s.sender = s.storageAddr 0

end Verity.Specs.SimpleToken
