/-
  Verity: Minimal EDSL Core

  This module defines the essential types and primitives for smart contracts.
  Philosophy: Keep it minimal - only add what examples actually need.
-/

import Verity.Core.Uint256
import Verity.Core.FiniteSet

namespace Verity

open Verity.Core (FiniteAddressSet)

-- Basic Ethereum types
abbrev Address := String
abbrev Uint256 := Verity.Core.Uint256

-- Storage key-value abstraction
structure StorageSlot (α : Type) where
  slot : Nat
  deriving Repr

-- Event type for ERC20/ERC721 compliance (#153)
structure Event where
  name : String
  args : List Uint256           -- Unindexed data arguments
  indexedArgs : List Uint256    -- Indexed topic arguments
  deriving Repr

-- State monad for contract execution
structure ContractState where
  storage : Nat → Uint256                -- Uint256 storage mapping
  storageAddr : Nat → Address            -- Address storage mapping
  storageMap : Nat → Address → Uint256  -- Mapping storage (Address → Uint256)
  storageMapUint : Nat → Uint256 → Uint256  -- Uint256-keyed mapping storage (#154)
  storageMap2 : Nat → Address → Address → Uint256  -- Double mapping storage (#154)
  sender : Address
  thisAddress : Address
  msgValue : Uint256
  blockTimestamp : Uint256
  knownAddresses : Nat → FiniteAddressSet  -- Tracked addresses per storage slot (for sum properties)
  events : List Event := []  -- Emitted events, append-only log (#153)

-- Default zero state — all storage zero, empty addresses, no events.
-- Use `{ defaultState with sender := "0xAlice" }` to customize individual fields.
def defaultState : ContractState where
  storage := fun _ => 0
  storageAddr := fun _ => ""
  storageMap := fun _ _ => 0
  storageMapUint := fun _ _ => 0
  storageMap2 := fun _ _ _ => 0
  sender := ""
  thisAddress := ""
  msgValue := 0
  blockTimestamp := 0
  knownAddresses := fun _ => Core.FiniteAddressSet.empty

-- Repr instance for ContractState (simplified for readability)
instance : Repr ContractState where
  reprPrec s _ := s!"ContractState(sender={s.sender}, thisAddress={s.thisAddress})"

-- Contract execution result (explicit success/failure)
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α
  deriving Repr

namespace ContractResult

-- Projections for backward compatibility with proofs.
-- WARNING: `fst` returns `default` on revert — proofs using `fst` must
-- independently establish that the result is `success`.
-- Prefer `getValue?` for new code.
def fst {α : Type} [Inhabited α] : ContractResult α → α
  | success a _ => a
  | revert _ _ => default

-- WARNING: On revert, returns the state at the point of revert, which may
-- include mutations from operations that executed before the revert.
-- This differs from EVM semantics where REVERT discards all state changes.
-- Contracts MUST follow the checks-before-effects pattern (all `require`
-- guards before any `setStorage`/`setMapping` calls) to ensure the revert
-- state equals the original input state. See issue #254 for details.
def snd {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s

-- Reduction rules for projections applied to constructors.
-- These ensure that when simp produces `ContractResult.success ...`, further
-- `.fst`/`.snd` applications are automatically reduced.
@[simp] theorem fst_success [Inhabited α] (a : α) (s : ContractState) :
  (ContractResult.success a s).fst = a := by rfl

@[simp] theorem snd_success (a : α) (s : ContractState) :
  (ContractResult.success a s).snd = s := by rfl

@[simp] theorem snd_revert (msg : String) (s : ContractState) :
  (ContractResult.revert (α := α) msg s).snd = s := by rfl

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

@[simp] theorem pure_run (a : α) (state : ContractState) :
  (pure a : Contract α).run state = ContractResult.success a state := by rfl

-- Helper: check if result is success
def ContractResult.isSuccess {α : Type} : ContractResult α → Bool
  | success _ _ => true
  | revert _ _ => false

-- Helper: extract value from success (unsafe, for testing)
def ContractResult.getValue? {α : Type} : ContractResult α → Option α
  | success a _ => some a
  | revert _ _ => none

-- Helper: extract state from result (see `snd` warning re: revert state).
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

-- Full-result simp lemmas: prove success + value + state in one shot.
-- These subsume the `_fst` and `_snd` variants below. Prefer these for new proofs.
@[simp] theorem getStorage_run (s : StorageSlot Uint256) (state : ContractState) :
  (getStorage s).run state = ContractResult.success (state.storage s.slot) state := by rfl

@[simp] theorem setStorage_run (s : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
  (setStorage s value).run state = ContractResult.success () { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  } := by rfl

-- Legacy projection lemmas (derive from the full-result versions above).
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

-- Full-result simp lemmas for address storage
@[simp] theorem getStorageAddr_run (s : StorageSlot Address) (state : ContractState) :
  (getStorageAddr s).run state = ContractResult.success (state.storageAddr s.slot) state := by rfl

@[simp] theorem setStorageAddr_run (s : StorageSlot Address) (value : Address) (state : ContractState) :
  (setStorageAddr s value).run state = ContractResult.success () { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  } := by rfl

-- Legacy projection lemmas
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

-- Full-result simp lemmas for mapping operations
@[simp] theorem getMapping_run (s : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
  (getMapping s key).run state = ContractResult.success (state.storageMap s.slot key) state := by rfl

@[simp] theorem setMapping_run (s : StorageSlot (Address → Uint256)) (key : Address) (value : Uint256) (state : ContractState) :
  (setMapping s key value).run state = ContractResult.success () { state with
    storageMap := fun slot addr =>
      if slot == s.slot && addr == key then value
      else state.storageMap slot addr,
    knownAddresses := fun slot =>
      if slot == s.slot then
        (state.knownAddresses slot).insert key
      else
        state.knownAddresses slot
  } := by rfl

-- Legacy projection lemmas
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

-- Double mapping operations (Address → Address → Uint256) (#154)
def getMapping2 (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) : Contract Uint256 :=
  fun state => ContractResult.success (state.storageMap2 s.slot key1 key2) state

def setMapping2 (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storageMap2 := fun slot addr1 addr2 =>
      if slot == s.slot && addr1 == key1 && addr2 == key2 then value
      else state.storageMap2 slot addr1 addr2
  }

-- Full-result simp lemmas for double mappings
@[simp] theorem getMapping2_run (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (state : ContractState) :
  (getMapping2 s key1 key2).run state = ContractResult.success (state.storageMap2 s.slot key1 key2) state := by rfl

@[simp] theorem setMapping2_run (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (value : Uint256) (state : ContractState) :
  (setMapping2 s key1 key2 value).run state = ContractResult.success () { state with
    storageMap2 := fun slot addr1 addr2 =>
      if slot == s.slot && addr1 == key1 && addr2 == key2 then value
      else state.storageMap2 slot addr1 addr2
  } := by rfl

-- Uint256-keyed mapping operations (#154)
def getMappingUint (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) : Contract Uint256 :=
  fun state => ContractResult.success (state.storageMapUint s.slot key) state

def setMappingUint (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storageMapUint := fun slot k =>
      if slot == s.slot && k == key then value
      else state.storageMapUint slot k
  }

-- Full-result simp lemmas for uint mappings
@[simp] theorem getMappingUint_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (state : ContractState) :
  (getMappingUint s key).run state = ContractResult.success (state.storageMapUint s.slot key) state := by rfl

@[simp] theorem setMappingUint_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Uint256) (state : ContractState) :
  (setMappingUint s key value).run state = ContractResult.success () { state with
    storageMapUint := fun slot k =>
      if slot == s.slot && k == key then value
      else state.storageMapUint slot k
  } := by rfl

-- Event emission (#153)
def emitEvent (name : String) (args : List Uint256) (indexedArgs : List Uint256 := []) : Contract Unit :=
  fun state => ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
  }

@[simp] theorem emitEvent_run (name : String) (args : List Uint256) (indexedArgs : List Uint256) (state : ContractState) :
  (emitEvent name args indexedArgs).run state = ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
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

-- Full-result simp lemmas for context accessors
@[simp] theorem msgSender_run (state : ContractState) :
  msgSender.run state = ContractResult.success state.sender state := by rfl

@[simp] theorem contractAddress_run (state : ContractState) :
  contractAddress.run state = ContractResult.success state.thisAddress state := by rfl

@[simp] theorem msgValue_run (state : ContractState) :
  msgValue.run state = ContractResult.success state.msgValue state := by rfl

@[simp] theorem blockTimestamp_run (state : ContractState) :
  blockTimestamp.run state = ContractResult.success state.blockTimestamp state := by rfl

-- Legacy projection lemmas
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

/-!
## Contract Monad Laws

The Contract monad satisfies all three monad laws, ensuring that do-notation
rewrites performed by Lean during elaboration preserve program semantics.
This eliminates a trust assumption noted in issue #146.
-/

-- Left identity: bind (pure a) f = f a
@[simp] theorem Contract.bind_pure_left (a : α) (f : α → Contract β) :
    bind (pure a) f = f a := by rfl

-- Right identity: bind m pure = m
@[simp] theorem Contract.bind_pure_right (m : Contract α) :
    bind m pure = m := by
  funext s
  simp only [bind, pure]
  cases m s with
  | success a s' => rfl
  | revert msg s' => rfl

-- Associativity: bind (bind m f) g = bind m (fun x => bind (f x) g)
@[simp] theorem Contract.bind_assoc (m : Contract α) (f : α → Contract β) (g : β → Contract γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext s
  simp only [bind]
  cases m s with
  | success a s' => rfl
  | revert msg s' => rfl

end Verity
