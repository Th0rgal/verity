/-
  Basic correctness proofs for Counter contract.

  Proves that Counter operations satisfy their specifications.
-/

import Verity.Specs.Counter.Spec
import Verity.Specs.Counter.Invariants

namespace Verity.Proofs.Counter

open Verity
open Verity.Examples.Counter
open Verity.Specs.Counter

/-! ## Basic Lemmas about setStorage and getStorage

These reuse patterns from SimpleStorage proofs.
-/

theorem setStorage_updates_count (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := ((setStorage slot value).run s).snd
  s'.storage 0 = value := by
  simp [setStorage, count]

theorem getStorage_reads_count (s : ContractState) :
  let slot : StorageSlot Uint256 := count
  let result := ((getStorage slot).run s).fst
  result = s.storage 0 := by
  simp [getStorage, count]

theorem setStorage_preserves_other_slots (s : ContractState) (value : Uint256) (slot_num : Nat)
  (h : slot_num ≠ 0) :
  let slot : StorageSlot Uint256 := count
  let s' := ((setStorage slot value).run s).snd
  s'.storage slot_num = s.storage slot_num := by
  simp [setStorage, count, h]

theorem setStorage_preserves_context (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := ((setStorage slot value).run s).snd
  s'.sender = s.sender ∧ s'.thisAddress = s.thisAddress := by
  simp [setStorage, count]

theorem setStorage_preserves_addr_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := ((setStorage slot value).run s).snd
  s'.storageAddr = s.storageAddr := by
  simp [setStorage, count]

theorem setStorage_preserves_map_storage (s : ContractState) (value : Uint256) :
  let slot : StorageSlot Uint256 := count
  let s' := ((setStorage slot value).run s).snd
  s'.storageMap = s.storageMap := by
  simp [setStorage, count]

/-! ## increment Correctness -/

theorem increment_meets_spec (s : ContractState) :
  let s' := ((increment).run s).snd
  increment_spec s s' := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro slot h_neq
    simp only [increment, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]
    split
    · next h =>
      have : slot = 0 := beq_iff_eq.mp h
      exact absurd this h_neq
    · rfl
  · simp [Specs.sameAddrMapContext, Specs.sameContext, Specs.sameStorageAddr, Specs.sameStorageMap,
      increment, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]

theorem increment_adds_one (s : ContractState) :
  let s' := ((increment).run s).snd
  s'.storage 0 = EVM.Uint256.add (s.storage 0) 1 := by
  have h := increment_meets_spec s; simp [increment_spec] at h; exact h.1

/-! ## decrement Correctness -/

theorem decrement_meets_spec (s : ContractState) :
  let s' := ((decrement).run s).snd
  decrement_spec s s' := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro slot h_neq
    simp only [decrement, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]
    split
    · next h =>
      have : slot = 0 := beq_iff_eq.mp h
      exact absurd this h_neq
    · rfl
  · simp [Specs.sameAddrMapContext, Specs.sameContext, Specs.sameStorageAddr, Specs.sameStorageMap,
      decrement, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]

theorem decrement_subtracts_one (s : ContractState) :
  let s' := ((decrement).run s).snd
  s'.storage 0 = EVM.Uint256.sub (s.storage 0) 1 := by
  have h := decrement_meets_spec s; simp [decrement_spec] at h; exact h.1

/-! ## getCount Correctness -/

theorem getCount_meets_spec (s : ContractState) :
  let result := ((getCount).run s).fst
  getCount_spec result s := by
  simp [getCount, getCount_spec, count]

theorem getCount_reads_count_value (s : ContractState) :
  let result := ((getCount).run s).fst
  result = s.storage 0 := by
  simpa [getCount_spec] using getCount_meets_spec s

/-! ## Composition Properties -/

theorem increment_getCount_correct (s : ContractState) :
  let s' := ((increment).run s).snd
  let result := ((getCount).run s').fst
  result = EVM.Uint256.add (s.storage 0) 1 := by
  have h_inc := increment_adds_one s
  simpa only [h_inc] using getCount_reads_count_value (((increment).run s).snd)

theorem decrement_getCount_correct (s : ContractState) :
  let s' := ((decrement).run s).snd
  let result := ((getCount).run s').fst
  result = EVM.Uint256.sub (s.storage 0) 1 := by
  have h_dec := decrement_subtracts_one s
  simpa only [h_dec] using getCount_reads_count_value (((decrement).run s).snd)

theorem increment_twice_adds_two (s : ContractState) :
  let s' := ((increment).run s).snd
  let s'' := ((increment).run s').snd
  s''.storage 0 = EVM.Uint256.add (EVM.Uint256.add (s.storage 0) 1) 1 := by
  have h1 : (((increment).run s).snd).storage 0 = EVM.Uint256.add (s.storage 0) 1 := increment_adds_one s
  have h2 : (((increment).run (((increment).run s).snd)).snd).storage 0 =
      EVM.Uint256.add (((increment).run s).snd.storage 0) 1 :=
    increment_adds_one (((increment).run s).snd)
  calc (((increment).run (((increment).run s).snd)).snd).storage 0
      = EVM.Uint256.add (((increment).run s).snd.storage 0) 1 := h2
    _ = EVM.Uint256.add (EVM.Uint256.add (s.storage 0) 1) 1 := by rw [h1]

theorem increment_decrement_cancel (s : ContractState) :
  let s' := ((increment).run s).snd
  let s'' := ((decrement).run s').snd
  s''.storage 0 = s.storage 0 := by
  have h1 : (((increment).run s).snd).storage 0 = EVM.Uint256.add (s.storage 0) 1 := increment_adds_one s
  have h2 : (((decrement).run (((increment).run s).snd)).snd).storage 0 =
      EVM.Uint256.sub (((increment).run s).snd.storage 0) 1 :=
    decrement_subtracts_one (((increment).run s).snd)
  calc (((decrement).run (((increment).run s).snd)).snd).storage 0
      = EVM.Uint256.sub (((increment).run s).snd.storage 0) 1 := h2
    _ = EVM.Uint256.sub (EVM.Uint256.add (s.storage 0) 1) 1 := by rw [h1]
    _ = s.storage 0 := by
      exact (EVM.Uint256.sub_add_cancel (s.storage 0) 1)

/-! ## State Preservation -/

theorem increment_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((increment).run s).snd
  WellFormedState s' := by
  simp only [increment, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero⟩

theorem decrement_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((decrement).run s).snd
  WellFormedState s' := by
  simp only [decrement, count, getStorage, setStorage, bind, Contract.run, Bind.bind, ContractResult.snd]
  exact ⟨h.sender_nonzero, h.contract_nonzero⟩

theorem getCount_preserves_state (s : ContractState) :
  let s' := ((getCount).run s).snd
  s' = s := by
  simp [getCount, getStorage]

end Verity.Proofs.Counter
