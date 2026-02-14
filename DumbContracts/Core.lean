/-
  Dumb Contracts: Minimal EDSL Core

  This module defines the essential types and primitives for smart contracts.
  Philosophy: Keep it minimal - only add what examples actually need.

  Version 2: Added explicit ContractResult for guard modeling
  Version 3: Added FiniteAddressSet for sum property proofs
-/

import DumbContracts.Core.Uint256
import DumbContracts.Core.FiniteSet

namespace DumbContracts

open DumbContracts.Core (FiniteAddressSet)

-- Basic Ethereum types
abbrev Address := String
abbrev Uint256 := DumbContracts.Core.Uint256
abbrev Bool' := Bool
abbrev Bytes := List Nat

-- Storage key-value abstraction
structure StorageSlot (α : Type) where
  slot : Nat
  deriving Repr

-- State monad for contract execution
structure ContractState where
  storage : Nat → Uint256                -- Uint256 storage mapping
  storageAddr : Nat → Address            -- Address storage mapping
  storageMap : Nat → Address → Uint256  -- Mapping storage (Address → Uint256)
  sender : Address
  thisAddress : Address
  msgValue : Uint256
  blockTimestamp : Uint256
  knownAddresses : Nat → FiniteAddressSet  -- Tracked addresses per storage slot (for sum properties)

-- Repr instance for ContractState (simplified for readability)
instance : Repr ContractState where
  reprPrec s _ := s!"ContractState(sender={s.sender}, thisAddress={s.thisAddress})"

-- Contract execution result (explicit success/failure)
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α
  deriving Repr

namespace ContractResult

-- Projections for backward compatibility with proofs
-- fst extracts the value from success; for revert, uses default
-- (proofs that use fst always show the result is success)
def fst {α : Type} [Inhabited α] : ContractResult α → α
  | success a _ => a
  | revert _ _ => default

def snd {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s  -- Return original state on revert

end ContractResult

-- The contract monad with explicit success/failure
abbrev Contract (α : Type) := ContractState → ContractResult α

-- Monad operations for Contract
def pure {α : Type} (a : α) : Contract α :=
  fun s => ContractResult.success a s

def bind {α β : Type} (ma : Contract α) (f : α → Contract β) : Contract β :=
  fun s => match ma s with
    | ContractResult.success a s' => f a s'
    | ContractResult.revert msg s' => ContractResult.revert msg s'

-- Convenience: run a Contract and extract result/state
def Contract.run {α : Type} (c : Contract α) (s : ContractState) : ContractResult α :=
  c s

-- Helper: check if result is success
def ContractResult.isSuccess {α : Type} : ContractResult α → Bool
  | success _ _ => true
  | revert _ _ => false

-- Helper: extract value from success (unsafe, for testing)
def ContractResult.getValue? {α : Type} : ContractResult α → Option α
  | success a _ => some a
  | revert _ _ => none

-- Helper: extract state from result
def ContractResult.getState {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s

-- Backward compatibility helpers for proofs (extracts from success case)
-- These helpers assume the contract succeeds and extract the result/state
namespace Contract

def runValue {α : Type} [Inhabited α] (c : Contract α) (s : ContractState) : α :=
  match c s with
  | ContractResult.success a _ => a
  | ContractResult.revert _ _ => default

def runState {α : Type} (c : Contract α) (s : ContractState) : ContractState :=
  match c s with
  | ContractResult.success _ s' => s'
  | ContractResult.revert _ s' => s'

end Contract

-- Storage operations for Uint256
def getStorage (s : StorageSlot Uint256) : Contract Uint256 :=
  fun state => ContractResult.success (state.storage s.slot) state

def setStorage (s : StorageSlot Uint256) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  }

-- Simp lemmas for storage operations
@[simp] theorem getStorage_run_fst (s : StorageSlot Uint256) (state : ContractState) :
  ((getStorage s).run state).fst = state.storage s.slot := by rfl

@[simp] theorem getStorage_run_snd (s : StorageSlot Uint256) (state : ContractState) :
  ((getStorage s).run state).snd = state := by rfl

@[simp] theorem setStorage_run_snd (s : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
  ((setStorage s value).run state).snd = { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  } := by rfl

-- Storage operations for Address
def getStorageAddr (s : StorageSlot Address) : Contract Address :=
  fun state => ContractResult.success (state.storageAddr s.slot) state

def setStorageAddr (s : StorageSlot Address) (value : Address) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  }

-- Simp lemmas for address storage operations
@[simp] theorem getStorageAddr_run_fst (s : StorageSlot Address) (state : ContractState) :
  ((getStorageAddr s).run state).fst = state.storageAddr s.slot := by rfl

@[simp] theorem getStorageAddr_run_snd (s : StorageSlot Address) (state : ContractState) :
  ((getStorageAddr s).run state).snd = state := by rfl

@[simp] theorem setStorageAddr_run_snd (s : StorageSlot Address) (value : Address) (state : ContractState) :
  ((setStorageAddr s value).run state).snd = { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  } := by rfl

-- Mapping operations (Address → Uint256)
def getMapping (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Uint256 :=
  fun state => ContractResult.success (state.storageMap s.slot key) state

def setMapping (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storageMap := fun slot addr =>
      if slot == s.slot && addr == key then value
      else state.storageMap slot addr,
    knownAddresses := fun slot =>
      if slot == s.slot then
        (state.knownAddresses slot).insert key
      else
        state.knownAddresses slot
  }

-- Simp lemmas for mapping operations
@[simp] theorem getMapping_run_fst (s : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
  ((getMapping s key).run state).fst = state.storageMap s.slot key := by rfl

@[simp] theorem getMapping_run_snd (s : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
  ((getMapping s key).run state).snd = state := by rfl

@[simp] theorem setMapping_run_snd (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (state : ContractState) :
  ((setMapping s key value).run state).snd = { state with
    storageMap := fun slot addr =>
      if slot == s.slot && addr == key then value
      else state.storageMap slot addr,
    knownAddresses := fun slot =>
      if slot == s.slot then
        (state.knownAddresses slot).insert key
      else
        state.knownAddresses slot
  } := by rfl

-- Read-only context accessors
def msgSender : Contract Address :=
  fun state => ContractResult.success state.sender state

def contractAddress : Contract Address :=
  fun state => ContractResult.success state.thisAddress state

def msgValue : Contract Uint256 :=
  fun state => ContractResult.success state.msgValue state

def blockTimestamp : Contract Uint256 :=
  fun state => ContractResult.success state.blockTimestamp state

-- Simp lemmas for context accessors
@[simp] theorem msgSender_run_fst (state : ContractState) :
  (msgSender.run state).fst = state.sender := by rfl

@[simp] theorem msgSender_run_snd (state : ContractState) :
  (msgSender.run state).snd = state := by rfl

@[simp] theorem contractAddress_run_fst (state : ContractState) :
  (contractAddress.run state).fst = state.thisAddress := by rfl

@[simp] theorem contractAddress_run_snd (state : ContractState) :
  (contractAddress.run state).snd = state := by rfl

@[simp] theorem msgValue_run_fst (state : ContractState) :
  (msgValue.run state).fst = state.msgValue := by rfl

@[simp] theorem msgValue_run_snd (state : ContractState) :
  (msgValue.run state).snd = state := by rfl

@[simp] theorem blockTimestamp_run_fst (state : ContractState) :
  (blockTimestamp.run state).fst = state.blockTimestamp := by rfl

@[simp] theorem blockTimestamp_run_snd (state : ContractState) :
  (blockTimestamp.run state).snd = state := by rfl

-- Require guard (explicit failure on condition = false)
def require (condition : Bool) (message : String) : Contract Unit :=
  fun s => if condition
           then ContractResult.success () s
           else ContractResult.revert message s

-- Simp lemmas for require
@[simp] theorem require_true (msg : String) (s : ContractState) :
  (require true msg).run s = ContractResult.success () s := by rfl

@[simp] theorem require_false (msg : String) (s : ContractState) :
  (require false msg).run s = ContractResult.revert msg s := by rfl

theorem require_succeeds (cond : Bool) (msg : String) (s : ContractState) :
  cond = true → (require cond msg).run s = ContractResult.success () s := by
  intro h; subst h; rfl

-- Monad instance for do-notation
instance : Monad Contract where
  pure := pure
  bind := bind

end DumbContracts
