/-
  Formal specifications for Ledger operations.
-/

import Verity.Core
import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.EVM.Uint256
import Verity.Examples.Ledger

namespace Verity.Specs.Ledger

open Verity
open Verity.Examples.Ledger
open Verity.EVM.Uint256
open Verity.Specs.Common (sumBalances balancesFinite)

/-! ## Operation Specifications -/

/-- deposit: increases sender's balance by amount -/
def deposit_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = add (s.storageMap 0 s.sender) amount ∧
  storageMapUnchangedExceptKeyAtSlot 0 s.sender s s' ∧
  sameStorageAddrContext s s'

/-- withdraw (when sufficient balance): decreases sender's balance by amount -/
def withdraw_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = sub (s.storageMap 0 s.sender) amount ∧
  storageMapUnchangedExceptKeyAtSlot 0 s.sender s s' ∧
  sameStorageAddrContext s s'

/-- transfer: moves amount from sender to recipient -/
def transfer_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  (if s.sender == to
    then s'.storageMap 0 s.sender = s.storageMap 0 s.sender
    else s'.storageMap 0 s.sender = sub (s.storageMap 0 s.sender) amount) ∧
  (if s.sender == to
    then s'.storageMap 0 to = s.storageMap 0 to
    else s'.storageMap 0 to = add (s.storageMap 0 to) amount) ∧
  (if s.sender == to
    then storageMapUnchangedExceptKeyAtSlot 0 s.sender s s'
    else storageMapUnchangedExceptKeysAtSlot 0 s.sender to s s') ∧
  sameStorageAddrContext s s'

/-- getBalance: returns balance at given address, no state change -/
def getBalance_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 0 addr

/-! ## Sum Properties -/

/-- The sum of all balances at slot 0 -/
def totalBalance (s : ContractState) : Uint256 :=
  sumBalances 0 (s.knownAddresses 0) s.storageMap

/-- Spec: deposit increases total balance by amount -/
def Spec_deposit_sum_equation (amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = add (totalBalance s) amount

/-- Spec: withdraw decreases total balance by amount -/
def Spec_withdraw_sum_equation (amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = sub (totalBalance s) amount

/-- Spec: transfer preserves total balance -/
def Spec_transfer_sum_preservation (_to : Address) (_amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = totalBalance s

end Verity.Specs.Ledger
