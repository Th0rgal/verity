/-
  State invariants for the ERC20 foundation scaffold.
-/

import Verity.Specs.Common
import Verity.Specs.Common.Sum

namespace Verity.Specs.ERC20

open Verity
open Verity.Specs.Common (sumBalances balancesFinite)

/-! ## State Invariants -/

/-- Basic well-formedness constraints for contract context and owner slot. -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  owner_nonzero : s.storageAddr 0 ≠ 0

/-- Total tracked balance at balances slot (slot 2). -/
def totalBalance (s : ContractState) : Uint256 :=
  sumBalances 2 (s.knownAddresses 2) s.storageMap

/-- Global supply matches tracked balances over known addresses. -/
def supply_matches_balances (s : ContractState) : Prop :=
  totalBalance s = s.storage 1

/-- Mapping isolation for balances slot updates. -/
def balances_slot_isolated (s s' : ContractState) : Prop :=
  ∀ slot : Nat, slot ≠ 2 → ∀ addr : Address, s'.storageMap slot addr = s.storageMap slot addr

/-- Mapping isolation for allowances slot updates. -/
def allowances_slot_isolated (s s' : ContractState) : Prop :=
  ∀ slot : Nat, slot ≠ 3 →
    ∀ ownerAddr spender : Address, s'.storageMap2 slot ownerAddr spender = s.storageMap2 slot ownerAddr spender

/-- Context fields are preserved by state transitions. -/
abbrev context_preserved := Specs.sameContext

/-- Sum-preservation statement for transfer operations. -/
def transfer_preserves_total (s s' : ContractState) : Prop :=
  totalBalance s' = totalBalance s

/-- Approve only updates allowance map and not balances or total supply. -/
def approve_is_balance_neutral (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap

end Verity.Specs.ERC20
