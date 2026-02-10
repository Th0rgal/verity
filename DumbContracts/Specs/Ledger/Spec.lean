/-
  Formal specifications for Ledger contract operations.

  Ledger uses mapping storage (slot 0: Address → Uint256) for balances.
  Operations: deposit, withdraw, transfer, getBalance.
-/

import DumbContracts.Core
import DumbContracts.Examples.Ledger

namespace DumbContracts.Specs.Ledger

open DumbContracts
open DumbContracts.Examples.Ledger

/-! ## Operation Specifications -/

/-- deposit: increases sender's balance by amount -/
def deposit_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender + amount ∧
  (∀ addr : Address, addr ≠ s.sender → s'.storageMap 0 addr = s.storageMap 0 addr) ∧
  (∀ slot : Nat, slot ≠ 0 → ∀ addr, s'.storageMap slot addr = s.storageMap slot addr) ∧
  s'.storage = s.storage ∧
  s'.storageAddr = s.storageAddr ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- withdraw (when sufficient balance): decreases sender's balance by amount -/
def withdraw_spec (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender - amount ∧
  (∀ addr : Address, addr ≠ s.sender → s'.storageMap 0 addr = s.storageMap 0 addr) ∧
  (∀ slot : Nat, slot ≠ 0 → ∀ addr, s'.storageMap slot addr = s.storageMap slot addr) ∧
  s'.storage = s.storage ∧
  s'.storageAddr = s.storageAddr ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- transfer (when sufficient balance, sender ≠ to):
    decreases sender balance, increases recipient balance -/
def transfer_spec (to : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap 0 s.sender = s.storageMap 0 s.sender - amount ∧
  s'.storageMap 0 to = s.storageMap 0 to + amount ∧
  (∀ addr : Address, addr ≠ s.sender → addr ≠ to → s'.storageMap 0 addr = s.storageMap 0 addr) ∧
  (∀ slot : Nat, slot ≠ 0 → ∀ addr, s'.storageMap slot addr = s.storageMap slot addr) ∧
  s'.storage = s.storage ∧
  s'.storageAddr = s.storageAddr ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress

/-- getBalance: returns balance at given address, no state change -/
def getBalance_spec (addr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 0 addr

end DumbContracts.Specs.Ledger
