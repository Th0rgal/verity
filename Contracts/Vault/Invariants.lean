import Verity.Specs.Common
import Contracts.Vault.Spec

namespace Contracts.Vault.Invariants

open Verity
open Contracts.Vault.Spec

structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  assets_eq_supply : assets_supply_synced s

abbrev context_preserved := Specs.sameContext

abbrev share_storage_unchanged (s s' : ContractState) :=
  ∀ addr : Address, s'.storageMap 2 addr = s.storageMap 2 addr

end Contracts.Vault.Invariants
