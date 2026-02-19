/-
  SimpleStorage: Basic Correctness Proofs

  This file contains proofs of basic correctness properties for SimpleStorage.

  Status: Complete — all 13 proofs proven with zero axioms and zero sorry.
-/

import Verity.Examples.SimpleStorage
import Verity.Specs.SimpleStorage.Spec
import Verity.Specs.SimpleStorage.Invariants

namespace Verity.Proofs.SimpleStorage

open Verity
open Verity.Examples
open Verity.Specs.SimpleStorage

-- Lemma: setStorage updates the correct slot
theorem setStorage_updates_slot (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.storage 0 = value := by
  -- Unfold definitions
  simp [setStorage]

-- Lemma: getStorage reads from the correct slot
theorem getStorage_reads_slot (s : ContractState) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let result := ((getStorage slot).run s).fst
  result = s.storage 0 := by
  simp [getStorage]

-- Lemma: setStorage preserves other slots
theorem setStorage_preserves_other_slots (s : ContractState) (value : Uint256) (n : Nat)
  (h : n ≠ 0) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.storage n = s.storage n := by
  simp [setStorage, h]

-- Lemma: setStorage preserves context (sender, thisAddress)
theorem setStorage_preserves_sender (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.sender = s.sender := by
  simp [setStorage]

theorem setStorage_preserves_address (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.thisAddress = s.thisAddress := by
  simp [setStorage]

-- Lemma: setStorage preserves address storage
theorem setStorage_preserves_addr_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.storageAddr = s.storageAddr := by
  simp [setStorage]

-- Lemma: setStorage preserves mapping storage
theorem setStorage_preserves_map_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := ⟨0⟩
  let s' := ((setStorage slot value).run s).snd
  s'.storageMap = s.storageMap := by
  simp [setStorage]

-- Main theorem: store meets its specification
theorem store_meets_spec (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  store_spec value s s' := by
  simp [store, storedData, store_spec, Specs.sameAddrMapContext,
    Specs.sameContext, Specs.sameStorageAddr, Specs.sameStorageMap]
  intro slot h_neq
  simp [setStorage, storedData, h_neq]

-- Main theorem: retrieve meets its specification
theorem retrieve_meets_spec (s : ContractState) :
  let result := ((retrieve).run s).fst
  retrieve_spec result s := by
  simp [retrieve, storedData, retrieve_spec]

-- Main theorem: store then retrieve returns the stored value
-- This is the key correctness property!
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  let result := ((retrieve).run s').fst
  result = value := by
  -- Strategy: use store_meets_spec to show s'.storage 0 = value
  -- then use retrieve_meets_spec to show result = s'.storage 0
  have h_store : store_spec value s ((store value).run s).snd :=
    store_meets_spec s value
  have h_retrieve : retrieve_spec ((retrieve).run ((store value).run s).snd).fst ((store value).run s).snd :=
    retrieve_meets_spec ((store value).run s).snd
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]

-- Theorem: store preserves well-formedness
theorem store_preserves_wellformedness (s : ContractState) (value : Uint256)
  (h : WellFormedState s) :
  let s' := ((store value).run s).snd
  WellFormedState s' := by
  simp only [store, storedData, setStorage, Contract.run, ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero⟩

-- Theorem: retrieve preserves state (read-only operation)
theorem retrieve_preserves_state (s : ContractState) :
  let s' := ((retrieve).run s).snd
  s' = s := by
  simp [retrieve, storedData, getStorage]

-- Theorem: retrieve is idempotent (running twice is the same as once)
theorem retrieve_twice_idempotent (s : ContractState) :
  let s' := ((retrieve).run s).snd
  ((retrieve).run s').snd = s' := by
  intro s'
  have h := retrieve_preserves_state s'
  simpa using h

end Verity.Proofs.SimpleStorage
