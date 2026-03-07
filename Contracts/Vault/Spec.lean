import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.Macro
import Verity.EVM.Uint256
import Contracts.Vault.Vault

namespace Contracts.Vault.Spec

open Verity
open Verity.Specs
open Contracts.Vault
open Verity.EVM.Uint256
open Verity.Specs.Common (sumBalances balancesFinite)

def storageUnchangedExceptAssetSlots (s s' : ContractState) : Prop :=
  ∀ slotIdx : Nat, slotIdx ≠ 0 → slotIdx ≠ 1 → s'.storage slotIdx = s.storage slotIdx

def sameStorageExceptAssetSlots (s s' : ContractState) : Prop :=
  storageUnchangedExceptAssetSlots s s' ∧
  Specs.sameStorageAddr s s' ∧
  Specs.sameContext s s'

def deposit_spec (assets : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 2 s.sender = add (s.storageMap 2 s.sender) assets ∧
  s'.storage 0 = add (s.storage 0) assets ∧
  s'.storage 1 = add (s.storage 1) assets ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 2 s.sender s s' ∧
  sameStorageExceptAssetSlots s s'

def withdraw_spec (shares : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 2 s.sender = sub (s.storageMap 2 s.sender) shares ∧
  s'.storage 0 = sub (s.storage 0) shares ∧
  s'.storage 1 = sub (s.storage 1) shares ∧
  Specs.storageMapUnchangedExceptKeyAtSlot 2 s.sender s s' ∧
  sameStorageExceptAssetSlots s s'

def balanceOf_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 2 addr

def totalAssets_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

def totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

def totalShares (s : ContractState) : Uint256 :=
  sumBalances 2 (s.knownAddresses 2) s.storageMap

def deposit_share_sum_equation (assets : Uint256) (s s' : ContractState) : Prop :=
  totalShares s' = add (totalShares s) assets

def withdraw_share_sum_equation (shares : Uint256) (s s' : ContractState) : Prop :=
  totalShares s' = sub (totalShares s) shares

def assets_supply_synced (s : ContractState) : Prop :=
  s.storage 0 = s.storage 1

end Contracts.Vault.Spec
