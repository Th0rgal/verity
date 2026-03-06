/-
  Formal specifications for Ledger operations.
-/

import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.EVM.Uint256
import Contracts.MacroContracts.Core

namespace Contracts.Ledger.Spec

open Verity
open Verity.Specs
open Contracts.MacroContracts.Ledger
open Verity.EVM.Uint256
open Verity.Specs.Common (sumBalances balancesFinite)

/-! ## Operation Specifications -/

/-- deposit: increases sender's balance by amount -/
def deposit_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  storageMapUpdateSpec
    0 s.sender
    (fun st => add (st.storageMap 0 st.sender) amount)
    sameStorageAddrContext
    s s'

/-- withdraw (when sufficient balance): decreases sender's balance by amount -/
def withdraw_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  storageMapUpdateSpec
    0 s.sender
    (fun st => sub (st.storageMap 0 st.sender) amount)
    sameStorageAddrContext
    s s'

/-- transfer: moves amount from sender to recipient -/
def transfer_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  storageMapTransferSpec 0 s.sender to amount sameStorageAddrContext s s'

/-- getBalance: returns balance at given address, no state change -/
def getBalance_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 0 addr

/-! ## Sum Properties -/

/-- The sum of all balances at slot 0 -/
def totalBalance (s : ContractState) : Uint256 :=
  sumBalances 0 (s.knownAddresses 0) s.storageMap

/-- Spec: deposit increases total balance by amount -/
def deposit_sum_equation (amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = add (totalBalance s) amount

/-- Spec: withdraw decreases total balance by amount -/
def withdraw_sum_equation (amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = sub (totalBalance s) amount

/-- Spec: transfer preserves total balance -/
def transfer_sum_preservation (_to : Address) (_amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = totalBalance s

end Contracts.Ledger.Spec
