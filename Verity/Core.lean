/-
  Verity: Minimal EDSL Core

  This module defines the essential types and primitives for smart contracts.
  Philosophy: Keep it minimal - only add what examples actually need.
-/

import Verity.Core.Address
import Verity.Core.Int256
import Verity.Core.Uint256
import Verity.Core.FiniteSet

namespace Verity

open Verity.Core (FiniteAddressSet)

-- Basic Ethereum types
abbrev Address := Verity.Core.Address
abbrev Int256 := Verity.Core.Int256
abbrev Uint256 := Verity.Core.Uint256

@[simp] def toInt256 (value : Uint256) : Int256 :=
  Verity.Core.Int256.ofUint256 value

@[simp] def toUint256 (value : Int256) : Uint256 :=
  Verity.Core.Int256.toUint256 value

@[simp] def zeroAddress : Address := 0

@[simp] def addressToWord (a : Address) : Uint256 :=
  (a.toNat : Uint256)

@[simp] def wordToAddress (w : Uint256) : Address :=
  Verity.Core.Address.ofNat (w : Nat)

@[simp] def isZeroAddress (a : Address) : Bool :=
  a == zeroAddress

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
  transientStorage : Nat → Uint256       -- EIP-1153 transient storage mapping
  storageAddr : Nat → Address            -- Address storage mapping
  storageMap : Nat → Address → Uint256  -- Mapping storage (Address → Uint256)
  storageMapUint : Nat → Uint256 → Uint256  -- Uint256-keyed mapping storage (#154)
  storageMap2 : Nat → Address → Address → Uint256  -- Double mapping storage (#154)
  storageArray : Nat → List Uint256  -- Dynamic-array storage grouped by base slot (#1571)
  sender : Address
  thisAddress : Address
  msgValue : Uint256
  blockTimestamp : Uint256
  blockNumber : Uint256 := 0
  chainId : Uint256 := 0
  blobBaseFee : Uint256 := 0
  calldataSize : Uint256 := 0
  knownAddresses : Nat → FiniteAddressSet  -- Tracked addresses per storage slot (for sum properties)
  events : List Event := []  -- Emitted events, append-only log (#153)

-- Default zero state — all storage zero, empty addresses, no events.
-- Use `{ defaultState with sender := "0xAlice" }` to customize individual fields.
def defaultState : ContractState where
  storage := fun _ => 0
  transientStorage := fun _ => 0
  storageAddr := fun _ => 0
  storageMap := fun _ _ => 0
  storageMapUint := fun _ _ => 0
  storageMap2 := fun _ _ _ => 0
  storageArray := fun _ => []
  sender := 0
  thisAddress := 0
  msgValue := 0
  blockTimestamp := 0
  blockNumber := 0
  chainId := 0
  knownAddresses := fun _ => Core.FiniteAddressSet.empty

-- Repr instance for ContractState (simplified for readability)
instance : Repr ContractState where
  reprPrec s _ := s!"ContractState(sender={repr s.sender}, thisAddress={repr s.thisAddress})"

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

-- On revert, returns the state carried in the `ContractResult`.
-- When results are produced via `Contract.run`, this is always the original
-- pre-call snapshot (rollback-by-construction; see issue #254).
def snd {α : Type} : ContractResult α → ContractState
  | success _ s => s
  | revert _ s => s

-- Reduction rules for projections applied to constructors.
-- These ensure that when simp produces `ContractResult.success ...`, further
-- `.fst`/`.snd` applications are automatically reduced.
@[simp] theorem fst_success [Inhabited α] (a : α) (s : ContractState) :
  (ContractResult.success a s).fst = a := rfl

@[simp] theorem snd_success (a : α) (s : ContractState) :
  (ContractResult.success a s).snd = s := rfl

@[simp] theorem snd_revert (msg : String) (s : ContractState) :
  (ContractResult.revert (α := α) msg s).snd = s := rfl

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

-- Convenience: run a Contract with EVM-like revert semantics.
-- Any revert is normalized to the pre-call snapshot `s`.
def Contract.run {α : Type} (c : Contract α) (s : ContractState) : ContractResult α :=
  match c s with
  | ContractResult.success a s' => ContractResult.success a s'
  | ContractResult.revert msg _ => ContractResult.revert msg s

/-- Execute `attempt` with per-call rollback semantics and, on revert, run
`handler` from the original pre-call snapshot. Successful attempts keep their
post-state and do not invoke the handler. -/
def Contract.tryCatch {α : Type} (attempt : Contract α) (handler : String → Contract Unit) :
    Contract Unit :=
  fun s =>
    match Contract.run attempt s with
    | ContractResult.success _ s' => ContractResult.success () s'
    | ContractResult.revert msg rollback => handler msg rollback

@[simp] theorem Contract.eq_of_run_success {α : Type} {c : Contract α} {s : ContractState}
    {a : α} {s' : ContractState} (h : c.run s = ContractResult.success a s') :
    c s = ContractResult.success a s' := by
  unfold Contract.run at h
  cases hcs : c s with
  | success a0 s0 =>
    simp [hcs] at h
    rcases h with ⟨ha, hs⟩
    subst ha
    subst hs
    rfl
  | revert msg s0 =>
    simp [hcs] at h

@[simp] theorem pure_run (a : α) (state : ContractState) :
  (pure a : Contract α).run state = ContractResult.success a state := rfl

@[simp] theorem tryCatch_success_run
    (attempt : Contract α) (handler : String → Contract Unit) (state state' : ContractState)
    (value : α)
    (h : attempt.run state = ContractResult.success value state') :
    (Contract.tryCatch attempt handler).run state = ContractResult.success () state' := by
  unfold Contract.tryCatch Contract.run at *
  simp [h]

@[simp] theorem tryCatch_revert_run
    (attempt : Contract α) (handler : String → Contract Unit) (state : ContractState)
    (msg : String)
    (h : attempt.run state = ContractResult.revert msg state) :
    (Contract.tryCatch attempt handler).run state = (handler msg).run state := by
  unfold Contract.tryCatch Contract.run at *
  simp [h]

-- Helper: check if result is success
def ContractResult.isSuccess {α : Type} : ContractResult α → Bool
  | success _ _ => true
  | revert _ _ => false

-- Helper: extract value from success (unsafe, for testing)
def ContractResult.getValue? {α : Type} : ContractResult α → Option α
  | success a _ => some a
  | revert _ _ => none

-- Helper: extract state from result.
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
  | ContractResult.revert _ _ => s

@[simp] theorem runState_eq_snd_run {α : Type} (c : Contract α) (s : ContractState) :
    c.runState s = (c.run s).snd := by
  unfold Contract.runState Contract.run ContractResult.snd
  cases h : c s <;> simp

end Contract

-- Storage operations for Uint256
def getStorage (s : StorageSlot Uint256) : Contract Uint256 :=
  fun state => ContractResult.success (state.storage s.slot) state

def setStorage (s : StorageSlot Uint256) (value : Uint256) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  }

@[simp] theorem getStorage_run (s : StorageSlot Uint256) (state : ContractState) :
  (getStorage s).run state = ContractResult.success (state.storage s.slot) state := rfl

@[simp] theorem setStorage_run (s : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
  (setStorage s value).run state = ContractResult.success () { state with
    storage := fun slot => if slot == s.slot then value else state.storage slot
  } := rfl

-- Storage operations for Address
def getStorageAddr (s : StorageSlot Address) : Contract Address :=
  fun state => ContractResult.success (state.storageAddr s.slot) state

def setStorageAddr (s : StorageSlot Address) (value : Address) : Contract Unit :=
  fun state => ContractResult.success () { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  }

@[simp] theorem getStorageAddr_run (s : StorageSlot Address) (state : ContractState) :
  (getStorageAddr s).run state = ContractResult.success (state.storageAddr s.slot) state := rfl

@[simp] theorem setStorageAddr_run (s : StorageSlot Address) (value : Address) (state : ContractState) :
  (setStorageAddr s value).run state = ContractResult.success () { state with
    storageAddr := fun slot => if slot == s.slot then value else state.storageAddr slot
  } := rfl

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

@[simp] theorem getMapping_run (s : StorageSlot (Address → Uint256)) (key : Address) (state : ContractState) :
  (getMapping s key).run state = ContractResult.success (state.storageMap s.slot key) state := rfl

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
  } := rfl

-- Typed address-valued mapping helpers on top of the word-backed storage model.
def getMappingAddr (s : StorageSlot (Address → Uint256)) (key : Address) : Contract Address :=
  fun state => ContractResult.success (wordToAddress (state.storageMap s.slot key)) state

def setMappingAddr (s : StorageSlot (Address → Uint256)) (key value : Address) : Contract Unit :=
  setMapping s key (addressToWord value)

@[simp] theorem getMappingAddr_run (s : StorageSlot (Address → Uint256)) (key : Address)
    (state : ContractState) :
  (getMappingAddr s key).run state =
    ContractResult.success (wordToAddress (state.storageMap s.slot key)) state := rfl

@[simp] theorem setMappingAddr_run (s : StorageSlot (Address → Uint256)) (key value : Address)
    (state : ContractState) :
  (setMappingAddr s key value).run state =
    (setMapping s key (addressToWord value)).run state := rfl

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
  (getMapping2 s key1 key2).run state = ContractResult.success (state.storageMap2 s.slot key1 key2) state := rfl

@[simp] theorem setMapping2_run (s : StorageSlot (Address → Address → Uint256)) (key1 key2 : Address) (value : Uint256) (state : ContractState) :
  (setMapping2 s key1 key2 value).run state = ContractResult.success () { state with
    storageMap2 := fun slot addr1 addr2 =>
      if slot == s.slot && addr1 == key1 && addr2 == key2 then value
      else state.storageMap2 slot addr1 addr2
  } := rfl

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
  (getMappingUint s key).run state = ContractResult.success (state.storageMapUint s.slot key) state := rfl

@[simp] theorem setMappingUint_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Uint256) (state : ContractState) :
  (setMappingUint s key value).run state = ContractResult.success () { state with
    storageMapUint := fun slot k =>
      if slot == s.slot && k == key then value
      else state.storageMapUint slot k
  } := rfl

def getMappingUintAddr (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) : Contract Address :=
  fun state => ContractResult.success (wordToAddress (state.storageMapUint s.slot key)) state

def setMappingUintAddr (s : StorageSlot (Uint256 → Uint256)) (key : Uint256) (value : Address) :
    Contract Unit :=
  setMappingUint s key (addressToWord value)

@[simp] theorem getMappingUintAddr_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (state : ContractState) :
  (getMappingUintAddr s key).run state =
    ContractResult.success (wordToAddress (state.storageMapUint s.slot key)) state := rfl

@[simp] theorem setMappingUintAddr_run (s : StorageSlot (Uint256 → Uint256)) (key : Uint256)
    (value : Address) (state : ContractState) :
  (setMappingUintAddr s key value).run state =
    (setMappingUint s key (addressToWord value)).run state := rfl

private def storageArraySetAt : List Uint256 → Nat → Uint256 → Option (List Uint256)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, idx + 1, value => do
      let updatedRest ← storageArraySetAt rest idx value
      some (head :: updatedRest)

private def storageArrayDropLast? : List Uint256 → Option (List Uint256)
  | [] => none
  | [_] => some []
  | head :: rest => do
      let updatedRest ← storageArrayDropLast? rest
      some (head :: updatedRest)

-- Storage dynamic-array operations (#1571)
def getStorageArrayLength (s : StorageSlot (List Uint256)) : Contract Uint256 :=
  fun state => ContractResult.success (((state.storageArray s.slot).length : Nat) : Uint256) state

def getStorageArrayElement (s : StorageSlot (List Uint256)) (index : Uint256) : Contract Uint256 :=
  fun state =>
    match (state.storageArray s.slot)[index.val]? with
    | some value => ContractResult.success value state
    | none => ContractResult.revert "Storage array index out of bounds" state

def pushStorageArray (s : StorageSlot (List Uint256)) (value : Uint256) : Contract Unit :=
  fun state =>
    let current := state.storageArray s.slot
    ContractResult.success () { state with
      storageArray := fun slot => if slot == s.slot then current ++ [value] else state.storageArray slot
    }

def popStorageArray (s : StorageSlot (List Uint256)) : Contract Unit :=
  fun state =>
    match storageArrayDropLast? (state.storageArray s.slot) with
    | some updated =>
        ContractResult.success () { state with
          storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
        }
    | none => ContractResult.revert "Storage array pop on empty array" state

def setStorageArrayElement (s : StorageSlot (List Uint256)) (index value : Uint256) : Contract Unit :=
  fun state =>
    match storageArraySetAt (state.storageArray s.slot) index.val value with
    | some updated =>
        ContractResult.success () { state with
          storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
        }
    | none => ContractResult.revert "Storage array index out of bounds" state

@[simp] theorem getStorageArrayLength_run (s : StorageSlot (List Uint256)) (state : ContractState) :
  (getStorageArrayLength s).run state =
    ContractResult.success (((state.storageArray s.slot).length : Nat) : Uint256) state := rfl

@[simp] theorem getStorageArrayElement_run_some (s : StorageSlot (List Uint256)) (index : Uint256)
    (state : ContractState) (value : Uint256)
    (h : (state.storageArray s.slot)[index.val]? = some value) :
    (getStorageArrayElement s index).run state = ContractResult.success value state := by
  simp [Contract.run, getStorageArrayElement, h]

@[simp] theorem getStorageArrayElement_run_none (s : StorageSlot (List Uint256)) (index : Uint256)
    (state : ContractState)
    (h : (state.storageArray s.slot)[index.val]? = none) :
    (getStorageArrayElement s index).run state =
      ContractResult.revert "Storage array index out of bounds" state := by
  simp [Contract.run, getStorageArrayElement, h]

@[simp] theorem pushStorageArray_run (s : StorageSlot (List Uint256)) (value : Uint256)
    (state : ContractState) :
  (pushStorageArray s value).run state = ContractResult.success () { state with
    storageArray := fun slot => if slot == s.slot then state.storageArray s.slot ++ [value] else state.storageArray slot
  } := rfl

@[simp] theorem popStorageArray_run_some (s : StorageSlot (List Uint256)) (state : ContractState)
    (updated : List Uint256)
    (h : storageArrayDropLast? (state.storageArray s.slot) = some updated) :
    (popStorageArray s).run state = ContractResult.success () { state with
      storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
    } := by
  simp [Contract.run, popStorageArray, h]

@[simp] theorem popStorageArray_run_none (s : StorageSlot (List Uint256)) (state : ContractState)
    (h : storageArrayDropLast? (state.storageArray s.slot) = none) :
    (popStorageArray s).run state =
      ContractResult.revert "Storage array pop on empty array" state := by
  simp [Contract.run, popStorageArray, h]

@[simp] theorem setStorageArrayElement_run_some (s : StorageSlot (List Uint256))
    (index value : Uint256) (state : ContractState) (updated : List Uint256)
    (h : storageArraySetAt (state.storageArray s.slot) index.val value = some updated) :
    (setStorageArrayElement s index value).run state = ContractResult.success () { state with
      storageArray := fun slot => if slot == s.slot then updated else state.storageArray slot
    } := by
  simp [Contract.run, setStorageArrayElement, h]

@[simp] theorem setStorageArrayElement_run_none (s : StorageSlot (List Uint256))
    (index value : Uint256) (state : ContractState)
    (h : storageArraySetAt (state.storageArray s.slot) index.val value = none) :
    (setStorageArrayElement s index value).run state =
      ContractResult.revert "Storage array index out of bounds" state := by
  simp [Contract.run, setStorageArrayElement, h]

-- Event emission (#153)
def emitEvent (name : String) (args : List Uint256) (indexedArgs : List Uint256 := []) : Contract Unit :=
  fun state => ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
  }

@[simp] theorem emitEvent_run (name : String) (args : List Uint256) (indexedArgs : List Uint256) (state : ContractState) :
  (emitEvent name args indexedArgs).run state = ContractResult.success () { state with
    events := state.events ++ [{ name := name, args := args, indexedArgs := indexedArgs }]
  } := rfl

-- Read-only context accessors
def msgSender : Contract Address :=
  fun state => ContractResult.success state.sender state

def contractAddress : Contract Address :=
  fun state => ContractResult.success state.thisAddress state

def msgValue : Contract Uint256 :=
  fun state => ContractResult.success state.msgValue state

def blockTimestamp : Contract Uint256 :=
  fun state => ContractResult.success state.blockTimestamp state

def blockNumber : Contract Uint256 :=
  fun state => ContractResult.success state.blockNumber state

def chainid : Contract Uint256 :=
  fun state => ContractResult.success state.chainId state

@[simp] theorem msgSender_run (state : ContractState) :
  msgSender.run state = ContractResult.success state.sender state := rfl

@[simp] theorem contractAddress_run (state : ContractState) :
  contractAddress.run state = ContractResult.success state.thisAddress state := rfl

@[simp] theorem msgValue_run (state : ContractState) :
  msgValue.run state = ContractResult.success state.msgValue state := rfl

@[simp] theorem blockTimestamp_run (state : ContractState) :
  blockTimestamp.run state = ContractResult.success state.blockTimestamp state := rfl

@[simp] theorem blockNumber_run (state : ContractState) :
  blockNumber.run state = ContractResult.success state.blockNumber state := rfl

@[simp] theorem chainid_run (state : ContractState) :
  chainid.run state = ContractResult.success state.chainId state := rfl

-- Require guard (explicit failure on condition = false)
def require (condition : Bool) (message : String) : Contract Unit :=
  fun s => if condition
           then ContractResult.success () s
           else ContractResult.revert message s

/-- Reentrancy guard primitive.
Uses `lockSlot` as a mutex (`0` = unlocked, nonzero = locked), sets it before
running `body`, and clears it on both success and revert paths. -/
def nonReentrant (lockSlot : StorageSlot Uint256) (body : Contract α) : Contract α :=
  fun s =>
    if s.storage lockSlot.slot == 0 then
      let sLocked := (setStorage lockSlot 1).runState s
      match body sLocked with
      | ContractResult.success a s' =>
          ContractResult.success a ((setStorage lockSlot 0).runState s')
      | ContractResult.revert msg s' =>
          ContractResult.revert msg ((setStorage lockSlot 0).runState s')
    else
      ContractResult.revert "ReentrancyGuard: reentrant call" s

-- Simp lemmas for require
@[simp] theorem require_true (msg : String) (s : ContractState) :
  (require true msg).run s = ContractResult.success () s := rfl

@[simp] theorem require_false (msg : String) (s : ContractState) :
  (require false msg).run s = ContractResult.revert msg s := rfl

theorem require_succeeds (cond : Bool) (msg : String) (s : ContractState) :
  cond = true → (require cond msg).run s = ContractResult.success () s := by
  intro h; subst h; rfl

@[simp] theorem nonReentrant_locked_reverts
    (lockSlot : StorageSlot Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.storage lockSlot.slot ≠ 0) :
    (nonReentrant lockSlot body).run s =
      ContractResult.revert "ReentrancyGuard: reentrant call" s := by
  have hNe : (s.storage lockSlot.slot == 0) = false := by
    simp [hLocked]
  simp [Contract.run, nonReentrant, hNe]

-- Regression for #254: mutations before a revert do not leak through `run`.
theorem run_revert_rolls_back_storage (value : Uint256) (s : ContractState) :
  ((bind (setStorage ⟨0⟩ value) (fun _ => require false "revert")).run s) =
    ContractResult.revert "revert" s := by
  rfl

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
    bind (pure a) f = f a := rfl

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
