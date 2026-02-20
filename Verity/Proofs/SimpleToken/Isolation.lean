/-
  Storage isolation proofs for SimpleToken.

  Proves that each operation only touches its intended storage slots:
  - supply_storage_isolated: Uint256 storage unchanged except slot 2
  - balance_mapping_isolated: Mapping storage unchanged except slot 1
  - owner_addr_isolated: Address storage unchanged except slot 0

  These prove that the three storage types (Uint256, Address, Mapping) are
  fully independent. No operation corrupts unrelated storage.
-/

import Verity.Proofs.SimpleToken.Basic

namespace Verity.Proofs.SimpleToken.Isolation

open Verity
open Verity.Stdlib.Math (safeAdd requireSomeUint)
open Verity.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open Verity.Specs.SimpleToken
open Verity.Proofs.Stdlib.Automation (uint256_ge_val_le)
open Verity.Proofs.SimpleToken

/-! ## Constructor Isolation -/

-- All three constructor isolation properties share the same simp reduction.
-- Constructor writes Uint256 slot 2 and Address slot 0; it never writes mappings.
private theorem constructor_isolation (s : ContractState) (initialOwner : Address) (slot : Nat) :
  (slot ≠ 2 → ((constructor initialOwner).run s).snd.storage slot = s.storage slot) ∧
  (∀ addr, ((constructor initialOwner).run s).snd.storageMap slot addr = s.storageMap slot addr) ∧
  (slot ≠ 0 → ((constructor initialOwner).run s).snd.storageAddr slot = s.storageAddr slot) := by
  simp only [constructor, setStorageAddr, setStorage,
    Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd]
  refine ⟨fun h_ne => ?_, fun _ => trivial, fun h_ne => ?_⟩ <;>
    simp [beq_iff_eq, h_ne]

/-- Constructor only writes Uint256 slot 2 (supply). -/
theorem constructor_supply_storage_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  supply_storage_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold supply_storage_isolated; exact (constructor_isolation s initialOwner slot).1

/-- Constructor doesn't write any mapping slot. -/
theorem constructor_balance_mapping_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  balance_mapping_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold balance_mapping_isolated; intro _; exact (constructor_isolation s initialOwner slot).2.1

/-- Constructor only writes Address slot 0 (owner). -/
theorem constructor_owner_addr_isolated (s : ContractState) (initialOwner : Address)
  (slot : Nat) :
  owner_addr_isolated s ((constructor initialOwner).run s).snd slot := by
  unfold owner_addr_isolated; exact (constructor_isolation s initialOwner slot).2.2

/-! ## Mint Isolation -/

-- All three mint isolation properties share the same proof structure:
-- unfold mint, case-split on both safeAdd calls, simp in each branch.
private theorem mint_isolation (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  (slot ≠ 2 → ((mint to amount).run s).snd.storage slot = s.storage slot) ∧
  (slot ≠ 1 → ∀ addr, ((mint to amount).run s).snd.storageMap slot addr = s.storageMap slot addr) ∧
  (slot ≠ 0 → ((mint to amount).run s).snd.storageAddr slot = s.storageAddr slot) := by
  simp only [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd,
    h_owner, beq_self_eq_true, ite_true]
  unfold Stdlib.Math.requireSomeUint
  cases safeAdd (s.storageMap 1 to) amount <;>
    simp_all [Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure, beq_iff_eq]
  cases safeAdd (s.storage 2) amount <;>
    simp_all [Verity.require, Verity.pure, Verity.bind]

/-- Mint only writes Uint256 slot 2. -/
theorem mint_supply_storage_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  supply_storage_isolated s ((mint to amount).run s).snd slot := by
  unfold supply_storage_isolated; exact (mint_isolation s to amount h_owner slot).1

/-- Mint only writes Mapping slot 1. -/
theorem mint_balance_mapping_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  balance_mapping_isolated s ((mint to amount).run s).snd slot := by
  unfold balance_mapping_isolated; exact (mint_isolation s to amount h_owner slot).2.1

/-- Mint doesn't write any Address slot (owner unchanged). -/
theorem mint_owner_addr_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) (slot : Nat) :
  owner_addr_isolated s ((mint to amount).run s).snd slot := by
  unfold owner_addr_isolated; exact (mint_isolation s to amount h_owner slot).2.2

/-! ## Transfer Isolation -/

-- All three transfer isolation properties share the same proof structure:
-- case-split on sender = to, then simp in each branch.
private theorem transfer_isolation (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (slot : Nat) :
  (((transfer to amount).run s).snd.storage slot = s.storage slot) ∧
  (slot ≠ 1 → ∀ addr, ((transfer to amount).run s).snd.storageMap slot addr = s.storageMap slot addr) ∧
  (((transfer to amount).run s).snd.storageAddr slot = s.storageAddr slot) := by
  by_cases h_eq : s.sender = to
  · have h_balance' := uint256_ge_val_le (h_eq ▸ h_balance)
    simp [transfer, Examples.SimpleToken.balances,
      msgSender, getMapping,
      Verity.require, Verity.pure, Verity.bind, Bind.bind,
      Contract.run, ContractResult.snd, h_balance', h_eq]
  · refine ⟨?_, fun h_ne_slot addr => ?_, ?_⟩
    all_goals simp [transfer, Examples.SimpleToken.balances,
        msgSender, getMapping, setMapping, requireSomeUint,
        Verity.require, Verity.bind, Bind.bind, Pure.pure,
        Contract.run, ContractResult.snd,
        h_balance, h_eq, beq_iff_eq]
    all_goals cases safeAdd (s.storageMap 1 to) amount <;>
        simp_all [Verity.require, Verity.pure, Verity.bind]

/-- Transfer doesn't write any Uint256 slot (supply unchanged). -/
theorem transfer_supply_storage_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (slot : Nat) :
  supply_storage_isolated s ((transfer to amount).run s).snd slot := by
  unfold supply_storage_isolated; intro _; exact (transfer_isolation s to amount h_balance slot).1

/-- Transfer only writes Mapping slot 1. -/
theorem transfer_balance_mapping_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (slot : Nat) :
  balance_mapping_isolated s ((transfer to amount).run s).snd slot := by
  unfold balance_mapping_isolated; exact (transfer_isolation s to amount h_balance slot).2.1

/-- Transfer doesn't write any Address slot (owner unchanged). -/
theorem transfer_owner_addr_isolated (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) (slot : Nat) :
  owner_addr_isolated s ((transfer to amount).run s).snd slot := by
  unfold owner_addr_isolated; intro _; exact (transfer_isolation s to amount h_balance slot).2.2

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

Transfer isolation (when sufficient balance):
7. transfer_supply_storage_isolated — doesn't write any Uint256 slot
8. transfer_balance_mapping_isolated — only writes Mapping slot 1
9. transfer_owner_addr_isolated — doesn't write any Address slot
-/

end Verity.Proofs.SimpleToken.Isolation
