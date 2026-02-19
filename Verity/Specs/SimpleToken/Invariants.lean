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

/-- Sum balances over a list of addresses -/
def sum_balances (s : ContractState) (addrs : List Address) : Uint256 :=
  (addrs.map (fun addr => s.storageMap 1 addr)).sum

/-- Total supply bounds all finite subsets of balances -/
def supply_bounds_balances (s : ContractState) : Prop :=
  ∀ addrs : List Address, sum_balances s addrs ≤ s.storage 2

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
