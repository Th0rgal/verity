/-
  Basic correctness proofs for SimpleToken operations

  This file proves fundamental properties about SimpleToken operations:
  - Constructor correctness
  - Mint operation correctness
  - Transfer operation correctness
  - Read operations (balanceOf, getTotalSupply, getOwner)
  - Invariant preservation
-/

import DumbContracts.Examples.SimpleToken
import DumbContracts.Specs.SimpleToken.Spec
import DumbContracts.Specs.SimpleToken.Invariants

namespace DumbContracts.Proofs.SimpleToken

open DumbContracts
open DumbContracts.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open DumbContracts.Specs.SimpleToken hiding owner balances totalSupply

/-! ## Basic Lemmas for Storage Operations -/

/-- setStorageAddr updates the owner address -/
theorem setStorageAddr_updates_owner (s : ContractState) (addr : Address) :
  let slot : StorageSlot Address := Examples.SimpleToken.owner
  let s' := ((setStorageAddr slot addr).run s).snd
  s'.storageAddr 0 = addr := by
  simp [setStorageAddr, Examples.SimpleToken.owner]

/-- setStorage updates the total supply -/
theorem setStorage_updates_supply (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := Examples.SimpleToken.totalSupply
  let s' := ((setStorage slot value).run s).snd
  s'.storage 2 = value := by
  simp [setStorage, Examples.SimpleToken.totalSupply]

/-- setMapping updates a balance -/
theorem setMapping_updates_balance (s : ContractState) (addr : Address) (value : Uint256) :
  let slot : StorageSlot (Address → Uint256) := Examples.SimpleToken.balances
  let s' := ((setMapping slot addr value).run s).snd
  s'.storageMap 1 addr = value := by
  simp [setMapping, Examples.SimpleToken.balances]

/-- getMapping reads a balance -/
theorem getMapping_reads_balance (s : ContractState) (addr : Address) :
  let slot : StorageSlot (Address → Uint256) := Examples.SimpleToken.balances
  let result := ((getMapping slot addr).run s).fst
  result = s.storageMap 1 addr := by
  simp [getMapping, Examples.SimpleToken.balances]

/-- getStorage reads total supply -/
theorem getStorage_reads_supply (s : ContractState) :
  let slot : StorageSlot Uint256 := Examples.SimpleToken.totalSupply
  let result := ((getStorage slot).run s).fst
  result = s.storage 2 := by
  simp [getStorage, Examples.SimpleToken.totalSupply]

/-- getStorageAddr reads owner -/
theorem getStorageAddr_reads_owner (s : ContractState) :
  let slot : StorageSlot Address := Examples.SimpleToken.owner
  let result := ((getStorageAddr slot).run s).fst
  result = s.storageAddr 0 := by
  simp [getStorageAddr, Examples.SimpleToken.owner]

/-- setMapping preserves other addresses -/
theorem setMapping_preserves_other_addresses (s : ContractState) (slot_val : StorageSlot (Address → Uint256))
  (addr value : _) (other_addr : Address) (h : other_addr ≠ addr) :
  let s' := ((setMapping slot_val addr value).run s).snd
  s'.storageMap slot_val.slot other_addr = s.storageMap slot_val.slot other_addr := by
  simp [setMapping, h]

/-! ## Constructor Correctness -/

theorem constructor_meets_spec (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  constructor_spec initialOwner s s' := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro slot h_neq
    simp only [constructor, setStorageAddr, setStorage, Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd]
    split
    · next h =>
      have : slot = 0 := by simp [beq_iff_eq] at h; exact h
      exact absurd this h_neq
    · rfl
  constructor
  · intro slot h_neq
    simp only [constructor, setStorageAddr, setStorage, Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd]
    split
    · next h =>
      have : slot = 2 := by simp [beq_iff_eq] at h; exact h
      exact absurd this h_neq
    · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  s'.storageAddr 0 = initialOwner := by
  have h := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h
  exact h.1

theorem constructor_sets_supply_zero (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  s'.storage 2 = 0 := by
  have h := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h
  exact h.2.1

/-! ## Mint Correctness

These proofs show that when the caller is the current owner,
mint correctly updates balances and total supply. With ContractResult,
the onlyOwner guard is fully modeled and all proofs are complete.
-/

-- Helper: isOwner returns true when sender is owner
theorem isOwner_true_when_owner (s : ContractState) (h : s.sender = s.storageAddr 0) :
  ((isOwner).run s).fst = true := by
  simp only [isOwner, msgSender, getStorageAddr, Examples.SimpleToken.owner, bind, Bind.bind, Contract.run, pure, Pure.pure, ContractResult.fst]
  simp [h]

-- Shared unfolding definitions for mint and transfer proofs
private abbrev unfold_defs := [``mint, ``transfer,
  ``DumbContracts.Examples.SimpleToken.onlyOwner, ``isOwner,
  ``Examples.SimpleToken.owner, ``Examples.SimpleToken.balances, ``Examples.SimpleToken.totalSupply,
  ``msgSender, ``getStorageAddr, ``setStorageAddr, ``getStorage, ``setStorage, ``getMapping, ``setMapping,
  ``DumbContracts.require, ``DumbContracts.pure, ``DumbContracts.bind, ``Bind.bind, ``Pure.pure,
  ``Contract.run, ``ContractResult.snd, ``ContractResult.fst]

-- Helper: unfold mint when owner guard passes
private theorem mint_unfold (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  (mint to amount).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 2) = true then s.storage 2 + amount else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 1 && addr == to) = true then s.storageMap 1 to + amount
        else s.storageMap slot addr,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  simp only [mint, DumbContracts.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_owner]

-- Mint correctness when caller is owner
theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  mint_spec to amount s s' := by
  have h_unfold := mint_unfold s to amount h_owner
  simp only [Contract.run, ContractResult.snd, mint_spec]
  rw [show (mint to amount) s = (mint to amount).run s from rfl, h_unfold]
  simp only [ContractResult.snd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp -- balance of 'to' updated
  · simp -- supply updated
  · intro addr h_neq; simp [h_neq] -- other balances preserved
  · trivial -- owner preserved
  · intro slot h_neq; intro addr; simp [h_neq] -- other mapping slots
  · intro slot h_neq; simp [h_neq] -- other uint storage
  · trivial -- sender preserved
  · trivial -- thisAddress preserved

theorem mint_increases_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  s'.storageMap 1 to = s.storageMap 1 to + amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner
  simp [mint_spec] at h
  exact h.1

theorem mint_increases_supply (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0) :
  let s' := ((mint to amount).run s).snd
  s'.storage 2 = s.storage 2 + amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner
  simp [mint_spec] at h
  exact h.2.1

/-! ## Transfer Correctness

These proofs show that when the sender has sufficient balance,
transfer correctly updates balances and preserves total supply.
The require guard for balance sufficiency is fully modeled.
-/

-- Helper: Nat.ble is equivalent to ≤ for the >= check
private theorem ble_true_of_ge {a b : Nat} (h : a ≥ b) : (b <= a) = true := by
  simp [Nat.ble_eq]
  exact h

-- Helper lemma: after unfolding transfer with sufficient balance, we get the concrete result state
private theorem transfer_unfold (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  (transfer to amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 1 && addr == to) = true then s.storageMap 1 to + amount
        else if (slot == 1 && addr == s.sender) = true then s.storageMap 1 s.sender - amount
        else s.storageMap slot addr,
      sender := s.sender,
      thisAddress := s.thisAddress } := by
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    DumbContracts.require, DumbContracts.pure, DumbContracts.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp [h_balance]

theorem transfer_meets_spec_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  transfer_spec s.sender to amount s s' := by
  have h_unfold := transfer_unfold s to amount h_balance
  simp only [Contract.run, ContractResult.snd, transfer_spec]
  rw [show (transfer to amount) s = (transfer to amount).run s from rfl, h_unfold]
  simp only [ContractResult.snd]
  refine ⟨h_balance, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sender balance decreased: the 'to' branch doesn't match sender
    have h_ne' : (s.sender == to) = false := by
      simp [beq_iff_eq]; exact h_ne
    simp [h_ne']
  · -- recipient balance increased
    simp
  · -- uint storage preserved
    trivial
  · -- other balances preserved
    intro addr h_ne_sender h_ne_to; simp [h_ne_sender, h_ne_to]
  · -- owner preserved
    trivial
  · -- other mapping slots preserved
    intro slot h_neq addr'; simp [h_neq]
  · -- uint storage by slot
    intro slot; trivial
  · -- addr storage by slot
    intro slot; trivial
  · trivial -- sender
  · trivial -- thisAddress

theorem transfer_preserves_supply_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storage 2 = s.storage 2 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_ne
  simp [transfer_spec] at h
  exact h.2.2.2.1

theorem transfer_decreases_sender_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 1 s.sender = s.storageMap 1 s.sender - amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_ne
  simp [transfer_spec] at h
  exact h.2.1

theorem transfer_increases_recipient_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 1 to = s.storageMap 1 to + amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_ne
  simp [transfer_spec] at h
  exact h.2.2.1

/-! ## Read Operations Correctness -/

theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
  let result := ((balanceOf addr).run s).fst
  balanceOf_spec addr result s := by
  simp [balanceOf, balanceOf_spec, getMapping, Examples.SimpleToken.balances]

theorem balanceOf_returns_balance (s : ContractState) (addr : Address) :
  let result := ((balanceOf addr).run s).fst
  result = s.storageMap 1 addr := by
  have h := balanceOf_meets_spec s addr
  simp [balanceOf_spec] at h
  exact h

theorem balanceOf_preserves_state (s : ContractState) (addr : Address) :
  let s' := ((balanceOf addr).run s).snd
  s' = s := by
  simp [balanceOf, getMapping]

theorem getTotalSupply_meets_spec (s : ContractState) :
  let result := ((getTotalSupply).run s).fst
  getTotalSupply_spec result s := by
  simp [getTotalSupply, getTotalSupply_spec, getStorage, Examples.SimpleToken.totalSupply]

theorem getTotalSupply_returns_supply (s : ContractState) :
  let result := ((getTotalSupply).run s).fst
  result = s.storage 2 := by
  have h := getTotalSupply_meets_spec s
  simp [getTotalSupply_spec] at h
  exact h

theorem getTotalSupply_preserves_state (s : ContractState) :
  let s' := ((getTotalSupply).run s).snd
  s' = s := by
  simp [getTotalSupply, getStorage]

theorem getOwner_meets_spec (s : ContractState) :
  let result := ((getOwner).run s).fst
  getOwner_spec result s := by
  simp [getOwner, getOwner_spec, getStorageAddr, Examples.SimpleToken.owner]

theorem getOwner_returns_owner (s : ContractState) :
  let result := ((getOwner).run s).fst
  result = s.storageAddr 0 := by
  have h := getOwner_meets_spec s
  simp [getOwner_spec] at h
  exact h

theorem getOwner_preserves_state (s : ContractState) :
  let s' := ((getOwner).run s).snd
  s' = s := by
  simp [getOwner, getStorageAddr]

/-! ## Composition Properties -/

theorem constructor_getTotalSupply_correct (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  let result := ((getTotalSupply).run s').fst
  constructor_getTotalSupply_spec initialOwner s result := by
  have h_constr := constructor_sets_supply_zero s initialOwner
  have h_get := getTotalSupply_returns_supply (((constructor initialOwner).run s).snd)
  simp [constructor_getTotalSupply_spec]
  rw [h_get, h_constr]

theorem constructor_getOwner_correct (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  let result := ((getOwner).run s').fst
  result = initialOwner := by
  simp only [constructor, getOwner, setStorageAddr, setStorage, getStorageAddr, Examples.SimpleToken.owner, Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd, ContractResult.fst]
  rfl

/-! ## Invariant Preservation -/

theorem constructor_preserves_wellformedness (s : ContractState) (initialOwner : Address)
  (h : WellFormedState s) (h_owner : initialOwner ≠ "") :
  let s' := ((constructor initialOwner).run s).snd
  WellFormedState s' := by
  have h_spec := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h_spec
  obtain ⟨h_owner_set, h_supply_set, h_other_addr, h_other_uint, h_map, h_sender, h_this⟩ := h_spec
  constructor
  · exact h_sender ▸ h.sender_nonempty
  · exact h_this ▸ h.contract_nonempty
  · exact h_owner_set ▸ h_owner

theorem balanceOf_preserves_wellformedness (s : ContractState) (addr : Address) (h : WellFormedState s) :
  let s' := ((balanceOf addr).run s).snd
  WellFormedState s' := by
  have h_pres := balanceOf_preserves_state s addr
  rw [h_pres]
  exact h

theorem getTotalSupply_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getTotalSupply).run s).snd
  WellFormedState s' := by
  have h_pres := getTotalSupply_preserves_state s
  rw [h_pres]
  exact h

theorem getOwner_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getOwner).run s).snd
  WellFormedState s' := by
  have h_pres := getOwner_preserves_state s
  rw [h_pres]
  exact h

/-! ## Documentation

All 33 theorems in this file are fully proven with zero sorry.

Guard-dependent proofs (now complete):
1. mint_meets_spec_when_owner - ✅ onlyOwner guard fully verified
2. mint_increases_balance - ✅ Derived from mint_meets_spec
3. mint_increases_supply - ✅ Derived from mint_meets_spec
4. transfer_meets_spec_when_sufficient - ✅ balance guard fully verified
5. transfer_preserves_supply_when_sufficient - ✅ Derived from transfer_meets_spec
6. transfer_decreases_sender_balance - ✅ Derived from transfer_meets_spec
7. transfer_increases_recipient_balance - ✅ Derived from transfer_meets_spec

Proof technique: Full unfolding of do-notation chains through
bind/pure/Contract.run/ContractResult.snd, with simp [h_owner] or
simp [h_balance] to resolve the guard condition, then refine for
each conjunct of the spec.
-/

end DumbContracts.Proofs.SimpleToken
