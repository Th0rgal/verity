/-
  Formal specifications for Ledger contract operations.

  Ledger uses mapping storage (slot 0: Address → Uint256) for balances.
  Operations: deposit, withdraw, transfer, getBalance.
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.Specs.Common.Sum
import DumbContracts.EVM.Uint256
import DumbContracts.Examples.Ledger

namespace DumbContracts.Specs.Ledger

open DumbContracts
open DumbContracts.Examples.Ledger
open DumbContracts.EVM.Uint256
open DumbContracts.Specs.Common (sumBalances balancesFinite)

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

/-- transfer (when sufficient balance):
    decreases sender balance, increases recipient balance
    (if sender == recipient, balances are unchanged) -/
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

/-! ## Sum Properties

These properties relate the total supply (sum of all balances) across operations.
They require finite address tracking via knownAddresses field.
-/

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
def Spec_transfer_sum_preservation (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  totalBalance s' = totalBalance s

/-- Spec: Sum of balances for singleton set containing only sender after deposit -/
def Spec_deposit_sum_singleton_sender (amount : Uint256) (s s' : ContractState) : Prop :=
  (∀ addr, addr ≠ s.sender → s.storageMap 0 addr = 0) →
    totalBalance s' = add (s.storageMap 0 s.sender) amount

/-- Spec: Sum preserved for deposit followed by withdraw.
    Note: This is derivable from the sum equations by add/sub cancellation,
    but documents the important round-trip property. -/
def Spec_deposit_withdraw_sum_cancel (amount : Uint256) (s s' s'' : ContractState) : Prop :=
  Spec_deposit_sum_equation amount s s' →
  Spec_withdraw_sum_equation amount s' s'' →
  totalBalance s'' = totalBalance s

/-- Spec: Sum of balances for singleton set after withdraw -/
def Spec_withdraw_sum_singleton_sender (amount : Uint256) (s s' : ContractState) : Prop :=
  (∀ addr, addr ≠ s.sender → s.storageMap 0 addr = 0) →
    totalBalance s' = sub (s.storageMap 0 s.sender) amount

/-- Spec: Transfer preserves sum for unique addresses -/
def Spec_transfer_sum_preserved_unique (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender ≠ to →
  totalBalance s' = totalBalance s

end DumbContracts.Specs.Ledger
