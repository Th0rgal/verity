/-
  Basic correctness proofs for SimpleToken operations

  This file proves fundamental properties about SimpleToken operations:
  - Constructor correctness
  - Mint operation correctness
  - Transfer operation correctness
  - Read operations (balanceOf, getTotalSupply, getOwner)
  - Invariant preservation
-/

import Verity.Examples.SimpleToken
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.Automation
import Verity.Specs.SimpleToken.Spec
import Verity.Specs.SimpleToken.Invariants

-- Proof scripts intentionally provide broader simp sets for stability across refactors.
set_option linter.unusedSimpArgs false

namespace Verity.Proofs.SimpleToken

open Verity
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math (safeAdd_some safeAdd_none)
open Verity.Proofs.Stdlib.Automation (address_beq_false_of_ne uint256_ge_val_le wf_of_state_eq)
open Verity.Examples.SimpleToken (constructor mint transfer balanceOf getTotalSupply getOwner isOwner)
open Verity.Specs.SimpleToken

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro slot h_neq
    simp only [constructor, setStorageAddr, setStorage, Examples.SimpleToken.owner,
      Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd]
    split
    · next h =>
      have : slot = 0 := beq_iff_eq.mp h
      exact absurd this h_neq
    · rfl
  · intro slot h_neq
    simp only [constructor, setStorageAddr, setStorage, Examples.SimpleToken.owner,
      Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd]
    split
    · next h =>
      have : slot = 2 := beq_iff_eq.mp h
      exact absurd this h_neq
    · rfl
  · rfl
  ·
    simp [Specs.sameContext, constructor, setStorageAddr, setStorage, Examples.SimpleToken.owner,
      Examples.SimpleToken.totalSupply, bind, Bind.bind, Contract.run, ContractResult.snd]

theorem constructor_sets_owner (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  s'.storageAddr 0 = initialOwner := by
  have h := constructor_meets_spec s initialOwner; simp [constructor_spec] at h; exact h.1

theorem constructor_sets_supply_zero (s : ContractState) (initialOwner : Address) :
  let s' := ((constructor initialOwner).run s).snd
  s'.storage 2 = 0 := by
  have h := constructor_meets_spec s initialOwner; simp [constructor_spec] at h; exact h.2.1

/-! ## Mint Correctness

These proofs show that when the caller is the current owner and
no overflow occurs, mint correctly updates balances and total supply.
With ContractResult, the onlyOwner guard and overflow checks via
safeAdd/requireSomeUint are fully modeled. The mint operation reverts
on overflow, matching Solidity ^0.8 checked arithmetic semantics.
-/

-- Helper: isOwner returns true when sender is owner
theorem isOwner_true_when_owner (s : ContractState) (h : s.sender = s.storageAddr 0) :
  ((isOwner).run s).fst = true := by
  simp [isOwner, msgSender, getStorageAddr, Examples.SimpleToken.owner, bind, Bind.bind, Contract.run, pure, Pure.pure, ContractResult.fst, h]

-- Helper: unfold mint when owner guard passes and no overflow
private theorem mint_unfold (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  (mint to amount).run s = ContractResult.success ()
    { storage := fun slot => if (slot == 2) = true then EVM.Uint256.add (s.storage 2) amount else s.storage slot,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 1 && addr == to) = true then EVM.Uint256.add (s.storageMap 1 to) amount
        else s.storageMap slot addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := fun slot =>
        if slot == 1 then (s.knownAddresses slot).insert to
        else s.knownAddresses slot,
      events := s.events } := by
  have h_safe_bal := safeAdd_some (s.storageMap 1 to) amount h_no_bal_overflow
  have h_safe_sup := safeAdd_some (s.storage 2) amount h_no_sup_overflow
  -- Unfold mint (checks-before-effects ordering: both requireSomeUint before mutations)
  simp only [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_owner, beq_self_eq_true, ite_true]
  -- Unfold and rewrite safeAdd results for both checks
  unfold requireSomeUint
  rw [h_safe_bal]
  simp only [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
    getStorage, Contract.run, ContractResult.snd, ContractResult.fst]
  rw [h_safe_sup]
  simp only [Verity.pure, Pure.pure, Verity.bind, Bind.bind,
    setMapping, setStorage,
    Contract.run, ContractResult.snd, ContractResult.fst]
  simp only [HAdd.hAdd, Add.add, h_owner]

-- Mint correctness when caller is owner and no overflow
theorem mint_meets_spec_when_owner (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  mint_spec to amount s s' := by
  have h_unfold := mint_unfold s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp only [Contract.run, ContractResult.snd, mint_spec]
  rw [show (mint to amount) s = (mint to amount).run s from rfl, h_unfold]
  simp only [ContractResult.snd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp -- balance of 'to' updated
  · simp -- supply updated
  · refine ⟨?_, ?_⟩
    · intro addr h_neq; simp [h_neq] -- other balances preserved
    · intro slot h_neq; intro addr; simp [h_neq] -- other mapping slots
  · trivial -- owner preserved
  · intro slot h_neq; simp [h_neq] -- other uint storage
  · exact Specs.sameContext_rfl _

theorem mint_increases_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  s'.storageMap 1 to = EVM.Uint256.add (s.storageMap 1 to) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp [mint_spec] at h; exact h.1

theorem mint_increases_supply (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_no_sup_overflow : (s.storage 2 : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((mint to amount).run s).snd
  s'.storage 2 = EVM.Uint256.add (s.storage 2) amount := by
  have h := mint_meets_spec_when_owner s to amount h_owner h_no_bal_overflow h_no_sup_overflow
  simp [mint_spec] at h; exact h.2.1

-- Mint reverts on balance overflow
theorem mint_reverts_balance_overflow (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) > MAX_UINT256) :
  ∃ msg, (mint to amount).run s = ContractResult.revert msg s := by
  have h_none := safeAdd_none (s.storageMap 1 to) amount h_overflow
  simp [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner, requireSomeUint,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_none, h_owner]

-- Mint reverts on supply overflow (even if balance doesn't overflow).
-- With checks-before-effects ordering, the revert happens before any state
-- mutations, so the revert state equals the original state `s`.
theorem mint_reverts_supply_overflow (s : ContractState) (to : Address) (amount : Uint256)
  (h_owner : s.sender = s.storageAddr 0)
  (h_no_bal_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256)
  (h_overflow : (s.storage 2 : Nat) + (amount : Nat) > MAX_UINT256) :
  ∃ msg, (mint to amount).run s = ContractResult.revert msg s := by
  have h_safe_bal := safeAdd_some (s.storageMap 1 to) amount h_no_bal_overflow
  have h_none := safeAdd_none (s.storage 2) amount h_overflow
  simp only [mint, Verity.Examples.SimpleToken.onlyOwner, isOwner, requireSomeUint,
    Examples.SimpleToken.owner, Examples.SimpleToken.balances, Examples.SimpleToken.totalSupply,
    msgSender, getStorageAddr, setStorageAddr, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_safe_bal, h_none, h_owner, beq_self_eq_true, ite_true]
  exact ⟨_, rfl⟩

/-! ## Transfer Correctness

These proofs show that when the sender has sufficient balance and
no recipient overflow occurs, transfer correctly updates balances
and preserves total supply. Both the require guard for balance
sufficiency and the safeAdd/requireSomeUint overflow check are
fully modeled, matching Solidity ^0.8 checked arithmetic semantics.
-/

-- Helper lemma: after unfolding transfer with sufficient balance and self-transfer, state is unchanged
private theorem transfer_unfold_self (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_eq : s.sender = to) :
  (transfer to amount).run s = ContractResult.success () s := by
  have h_balance' := uint256_ge_val_le (h_eq ▸ h_balance)
  simp [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_balance', h_eq, beq_iff_eq]

-- Helper lemma: after unfolding transfer with sufficient balance, distinct recipient, and no overflow
private theorem transfer_unfold_other (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  (transfer to amount).run s = ContractResult.success ()
    { storage := s.storage,
      storageAddr := s.storageAddr,
      storageMap := fun slot addr =>
        if (slot == 1 && addr == to) = true then EVM.Uint256.add (s.storageMap 1 to) amount
        else if (slot == 1 && addr == s.sender) = true then EVM.Uint256.sub (s.storageMap 1 s.sender) amount
        else s.storageMap slot addr,
      storageMapUint := s.storageMapUint,
      storageMap2 := s.storageMap2,
      sender := s.sender,
      thisAddress := s.thisAddress,
      msgValue := s.msgValue,
      blockTimestamp := s.blockTimestamp,
      knownAddresses := fun slot =>
        if slot == 1 then ((s.knownAddresses slot).insert s.sender).insert to
        else s.knownAddresses slot,
      events := s.events } := by
  have h_balance' := uint256_ge_val_le h_balance
  have h_safe := safeAdd_some (s.storageMap 1 to) amount h_no_overflow
  simp only [transfer, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    requireSomeUint,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_balance, h_ne, beq_iff_eq, h_safe, ge_iff_le, decide_eq_true_eq,
    h_balance', ite_true, ite_false, HAdd.hAdd, Add.add]
  congr 1
  -- The two ContractState records differ in storageMap and knownAddresses
  congr 1
  -- knownAddresses: simplify nested if slot = 1
  funext slot
  split <;> simp [*]

theorem transfer_meets_spec_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_no_overflow : s.sender ≠ to → (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  transfer_spec s.sender to amount s s' := by
  by_cases h_eq : s.sender = to
  · have h_unfold := transfer_unfold_self s to amount h_balance h_eq
    simp only [Contract.run, ContractResult.snd, transfer_spec]
    rw [show (transfer to amount) s = (transfer to amount).run s from rfl, h_unfold]
    refine ⟨h_balance, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_eq, beq_iff_eq]
    · simp [h_eq, beq_iff_eq]
    · simp [h_eq, beq_iff_eq, Specs.storageMapUnchangedExceptKeyAtSlot,
        Specs.storageMapUnchangedExceptKey, Specs.storageMapUnchangedExceptSlot]
    · rfl
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameContext]
  · have h_unfold := transfer_unfold_other s to amount h_balance h_eq (h_no_overflow h_eq)
    simp only [Contract.run, ContractResult.snd, transfer_spec]
    rw [show (transfer to amount) s = (transfer to amount).run s from rfl, h_unfold]
    simp only [ContractResult.snd]
    have h_ne' := address_beq_false_of_ne s.sender to h_eq
    refine ⟨h_balance, ?_, ?_, ?_, ?_, ?_⟩
    · simp [h_ne'] -- sender balance decreased
    · simp [h_ne'] -- recipient balance increased
    · simp [h_ne'] -- other balances/slots preserved
      refine ⟨?_, ?_⟩
      · intro addr h_ne_sender h_ne_to; simp [h_ne_sender, h_ne_to]
      · intro slot h_neq addr'; simp [h_neq]
    · -- owner preserved
      trivial
    · simp [Specs.sameStorageAddrContext, Specs.sameStorage, Specs.sameStorageAddr, Specs.sameContext]

theorem transfer_preserves_supply_when_sufficient (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_no_overflow : s.sender ≠ to → (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storage 2 = s.storage 2 := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance h_no_overflow
  simp [transfer_spec, Specs.sameStorage] at h
  simpa using congrArg (fun f => f 2) h.2.2.2.2.2.1

theorem transfer_decreases_sender_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 1 s.sender = EVM.Uint256.sub (s.storageMap 1 s.sender) amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h; exact h.2.1

theorem transfer_increases_recipient_balance (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to)
  (h_no_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) ≤ MAX_UINT256) :
  let s' := ((transfer to amount).run s).snd
  s'.storageMap 1 to = EVM.Uint256.add (s.storageMap 1 to) amount := by
  have h := transfer_meets_spec_when_sufficient s to amount h_balance (fun _ => h_no_overflow)
  simp [transfer_spec, h_ne, beq_iff_eq] at h; exact h.2.2.1

theorem transfer_self_preserves_balance (s : ContractState) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount) :
  let s' := ((transfer s.sender amount).run s).snd
  s'.storageMap 1 s.sender = s.storageMap 1 s.sender := by
  have h := transfer_meets_spec_when_sufficient s s.sender amount h_balance (fun h => absurd rfl h)
  simp [transfer_spec, beq_iff_eq] at h; exact h.2.1

-- Transfer reverts on recipient balance overflow
theorem transfer_reverts_recipient_overflow (s : ContractState) (to : Address) (amount : Uint256)
  (h_balance : s.storageMap 1 s.sender ≥ amount)
  (h_ne : s.sender ≠ to)
  (h_overflow : (s.storageMap 1 to : Nat) + (amount : Nat) > MAX_UINT256) :
  ∃ msg, (transfer to amount).run s = ContractResult.revert msg s := by
  have h_balance' := uint256_ge_val_le h_balance
  have h_none := safeAdd_none (s.storageMap 1 to) amount h_overflow
  simp [transfer, requireSomeUint, Examples.SimpleToken.balances,
    msgSender, getMapping, setMapping,
    Verity.require, Verity.pure, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd, ContractResult.fst,
    h_balance', h_ne, beq_iff_eq, h_none]

/-! ## Read Operations Correctness -/

theorem balanceOf_meets_spec (s : ContractState) (addr : Address) :
  let result := ((balanceOf addr).run s).fst
  balanceOf_spec addr result s := by
  simp [balanceOf, balanceOf_spec, getMapping, Examples.SimpleToken.balances]

theorem balanceOf_returns_balance (s : ContractState) (addr : Address) :
  let result := ((balanceOf addr).run s).fst
  result = s.storageMap 1 addr := by
  simpa [balanceOf_spec] using balanceOf_meets_spec s addr

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
  simpa [getTotalSupply_spec] using getTotalSupply_meets_spec s

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
  simpa [getOwner_spec] using getOwner_meets_spec s

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
  (h : WellFormedState s) (h_owner : initialOwner ≠ 0) :
  let s' := ((constructor initialOwner).run s).snd
  WellFormedState s' := by
  have h_spec := constructor_meets_spec s initialOwner
  simp [constructor_spec] at h_spec
  obtain ⟨h_owner_set, h_supply_set, h_other_addr, h_other_uint, h_map, h_sender, h_this, _h_value, _h_time⟩ := h_spec
  exact ⟨h_sender ▸ h.sender_nonzero, h_this ▸ h.contract_nonzero, h_owner_set ▸ h_owner⟩

theorem balanceOf_preserves_wellformedness (s : ContractState) (addr : Address) (h : WellFormedState s) :
  let s' := ((balanceOf addr).run s).snd
  WellFormedState s' :=
  wf_of_state_eq _ _ _ (balanceOf_preserves_state s addr) h

theorem getTotalSupply_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getTotalSupply).run s).snd
  WellFormedState s' :=
  wf_of_state_eq _ _ _ (getTotalSupply_preserves_state s) h

theorem getOwner_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getOwner).run s).snd
  WellFormedState s' :=
  wf_of_state_eq _ _ _ (getOwner_preserves_state s) h

/-! ## Documentation

All 37 theorems in this file are fully proven with zero sorry.

Guard-dependent proofs (now complete):
1. mint_meets_spec_when_owner - ✅ onlyOwner + overflow guards fully verified
2. mint_increases_balance - ✅ Derived from mint_meets_spec
3. mint_increases_supply - ✅ Derived from mint_meets_spec
4. mint_reverts_balance_overflow - ✅ Reverts when balance would overflow
5. mint_reverts_supply_overflow - ✅ Reverts when supply would overflow
6. transfer_meets_spec_when_sufficient - ✅ balance + overflow guards fully verified
7. transfer_preserves_supply_when_sufficient - ✅ Derived from transfer_meets_spec
8. transfer_decreases_sender_balance - ✅ Derived from transfer_meets_spec
9. transfer_increases_recipient_balance - ✅ Derived from transfer_meets_spec
10. transfer_self_preserves_balance - ✅ Self-transfer leaves balance unchanged
11. transfer_reverts_recipient_overflow - ✅ Reverts when recipient balance would overflow

Proof technique: Full unfolding of do-notation chains through
bind/pure/Contract.run/ContractResult.snd, with simp [h_owner] or
simp [h_balance] to resolve the guard condition, then refine for
each conjunct of the spec. Overflow checks use safeAdd/requireSomeUint
with safeAdd_some/safeAdd_none helpers to resolve the Option matching.
-/

end Verity.Proofs.SimpleToken
