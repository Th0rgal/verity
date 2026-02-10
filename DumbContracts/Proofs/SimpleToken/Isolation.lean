/-
  Storage isolation proofs for SimpleToken.

  Proves that each operation only touches its intended storage slots:
  - supply_storage_isolated: Uint256 storage unchanged except slot 2
  - balance_mapping_isolated: Mapping storage unchanged except slot 1
  - owner_addr_isolated: Address storage unchanged except slot 0

  These prove that the three storage types (Uint256, Address, Mapping) are
  fully independent. No operation corrupts unrelated storage.
-/

import DumbContracts.Core
import DumbContracts.Examples.SimpleToken
import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants
import DumbContracts.Proofs.SimpleToken.Basic

namespace DumbContracts.Proofs.SimpleToken.Isolation

open DumbContracts
open DumbContracts.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open DumbContracts.Specs.SimpleToken hiding owner balances totalSupply
open DumbContracts.Proofs.SimpleToken

/-! ## Constructor Isolation -/

/-- Constructor only writes Uint256 slot 2 (supply). -/
theorem constructor_supply_storage_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  supply_storage_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold supply_storage_isolated; intro h_ne
  simp only [constructor, setStorageAddr, setStorage,
    Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply,
    DumbContracts.bind, Bind.bind, Contract.run, ContractResult.snd]
  split
  · next h => simp [beq_iff_eq] at h; exact absurd h h_ne
  · rfl

/-- Constructor doesn't write any mapping slot. -/
theorem constructor_balance_mapping_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  balance_mapping_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold balance_mapping_isolated; intro _h_ne addr
  simp only [constructor, setStorageAddr, setStorage,
    Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply,
    DumbContracts.bind, Bind.bind, Contract.run, ContractResult.snd]

/-- Constructor only writes Address slot 0 (owner). -/
theorem constructor_owner_addr_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  owner_addr_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold owner_addr_isolated; intro h_ne
  simp only [constructor, setStorageAddr, setStorage,
    Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply,
    DumbContracts.bind, Bind.bind, Contract.run, ContractResult.snd]
  split
  · next h => simp [beq_iff_eq] at h; exact absurd h h_ne
  · rfl

/-! ## Mint Isolation -/

/-- Mint only writes Uint256 slot 2. -/
theorem mint_supply_storage_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  supply_storage_isolated s ((mint to amount).run s).snd slot := by
  unfold supply_storage_isolated; intro h_ne
  simp only [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_owner, beq_iff_eq, h_ne]

/-- Mint only writes Mapping slot 1. -/
theorem mint_balance_mapping_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  balance_mapping_isolated s ((mint to amount).run s).snd slot := by
  unfold balance_mapping_isolated; intro h_ne addr
  simp only [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_owner, beq_iff_eq, h_ne]

/-- Mint doesn't write any Address slot (owner unchanged). -/
theorem mint_owner_addr_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  owner_addr_isolated s ((mint to amount).run s).snd slot := by
  unfold owner_addr_isolated; intro _h_ne
  simp only [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_owner]

/-! ## Transfer Isolation -/

/-- Transfer doesn't write any Uint256 slot (supply unchanged). -/
theorem transfer_supply_storage_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (_h_ne : s.sender ≠ to) (slot : Nat) :
  supply_storage_isolated s ((transfer to amount).run s).snd slot := by
  unfold supply_storage_isolated; intro _h_ne_slot
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance]

/-- Transfer only writes Mapping slot 1. -/
theorem transfer_balance_mapping_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (_h_ne : s.sender ≠ to) (slot : Nat) :
  balance_mapping_isolated s ((transfer to amount).run s).snd slot := by
  unfold balance_mapping_isolated; intro h_ne_slot addr
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance, beq_iff_eq, h_ne_slot]

/-- Transfer doesn't write any Address slot (owner unchanged). -/
theorem transfer_owner_addr_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (_h_ne : s.sender ≠ to) (slot : Nat) :
  owner_addr_isolated s ((transfer to amount).run s).snd slot := by
  unfold owner_addr_isolated; intro _h_ne_slot
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance]

/-! ## Summary

All 9 theorems fully proven with zero sorry:

Constructor isolation:
1. constructor_supply_storage_isolated — only writes Uint256 slot 2
2. constructor_balance_mapping_isolated — doesn't write any mapping slot
3. constructor_owner_addr_isolated — only writes Address slot 0

Mint isolation (when owner):
4. mint_supply_storage_isolated — only writes Uint256 slot 2
5. mint_balance_mapping_isolated — only writes Mapping slot 1
6. mint_owner_addr_isolated — doesn't write any Address slot

Transfer isolation (when sufficient balance, sender ≠ to):
7. transfer_supply_storage_isolated — doesn't write any Uint256 slot
8. transfer_balance_mapping_isolated — only writes Mapping slot 1
9. transfer_owner_addr_isolated — doesn't write any Address slot
-/

end DumbContracts.Proofs.SimpleToken.Isolation
