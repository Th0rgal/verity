/-
  Advanced correctness proofs for Counter contract.

  Proves deeper properties beyond Basic.lean:
  - Standalone invariant proofs matching Invariants.lean definitions
  - Combined spec forms matching Spec.lean definitions
  - State preservation composition
-/

import Verity.Core
import Verity.Examples.Counter
import Verity.EVM.Uint256
import Verity.Specs.Counter.Spec
import Verity.Specs.Counter.Invariants
import Verity.Proofs.Counter.Basic

namespace Verity.Proofs.Counter.Correctness

open Verity
open Verity.Examples.Counter
open Verity.Specs.Counter
open Verity.Proofs.Counter

/-! ## Standalone Invariant Proofs

Prove that each operation satisfies the invariant definitions from Invariants.lean.
These establish that increment/decrement only modify slot 0.
-/

/-- increment preserves all state except count (matches state_preserved_except_count def). -/
theorem increment_state_preserved_except_count (s : ContractState) :
  let s' := ((increment).run s).snd
  state_preserved_except_count s s' := by
  have h := increment_meets_spec s
  rcases h with ⟨_, h_slots, h_same⟩
  rcases h_same with ⟨h_addr, h_map, h_ctx⟩
  refine ⟨fun h_ne => h_slots 0 h_ne, h_addr, h_map, ?_⟩
  simpa [context_preserved, Specs.sameContext] using h_ctx

/-- decrement preserves all state except count. -/
theorem decrement_state_preserved_except_count (s : ContractState) :
  let s' := ((decrement).run s).snd
  state_preserved_except_count s s' := by
  have h := decrement_meets_spec s
  rcases h with ⟨_, h_slots, h_same⟩
  rcases h_same with ⟨h_addr, h_map, h_ctx⟩
  refine ⟨fun h_ne => h_slots 0 h_ne, h_addr, h_map, ?_⟩
  simpa [context_preserved, Specs.sameContext] using h_ctx

/-- getCount preserves all state (trivially, since it's read-only). -/
theorem getCount_state_preserved (s : ContractState) :
  let s' := ((getCount).run s).snd
  state_preserved_except_count s s' := by
  have h := getCount_preserves_state s
  simp [h, state_preserved_except_count, storage_isolated, addr_storage_unchanged,
    map_storage_unchanged, Specs.sameContext]

/-! ## Combined Spec Proofs

Prove the combined operation specs defined in Spec.lean.
-/

/-- increment followed by getCount satisfies increment_getCount_spec. -/
theorem increment_getCount_meets_spec (s : ContractState) :
  let s' := ((increment).run s).snd
  let result := ((getCount).run s').fst
  increment_getCount_spec s result := by
  simp [increment_getCount_spec]
  exact increment_getCount_correct s

/-- decrement followed by getCount satisfies decrement_getCount_spec. -/
theorem decrement_getCount_meets_spec (s : ContractState) :
  let s' := ((decrement).run s).snd
  let result := ((getCount).run s').fst
  decrement_getCount_spec s result := by
  simp [decrement_getCount_spec]
  exact decrement_getCount_correct s

/-- Two increments satisfy two_increments_spec. -/
theorem two_increments_meets_spec (s : ContractState) :
  let s' := ((increment).run s).snd
  let s'' := ((increment).run s').snd
  two_increments_spec s s'' := by
  simp [two_increments_spec]
  exact increment_twice_adds_two s

/-- Increment then decrement satisfies increment_decrement_cancel spec. -/
theorem increment_decrement_meets_cancel (s : ContractState) :
  let s' := ((increment).run s).snd
  let s'' := ((decrement).run s').snd
  Specs.Counter.increment_decrement_cancel s s'' := by
  simp [Specs.Counter.increment_decrement_cancel]
  exact Proofs.Counter.increment_decrement_cancel s

/-! ## Read-Only Well-Formedness -/

/-- getCount preserves well-formedness (trivially, since read-only). -/
theorem getCount_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((getCount).run s).snd
  WellFormedState s' := by
  have h_pres := getCount_preserves_state s
  rw [h_pres]
  exact h

/-! ## Decrement → getCount Composition -/

/-- decrement followed by getCount returns count - 1. -/
theorem decrement_getCount_correct (s : ContractState) :
  let s' := ((decrement).run s).snd
  ((getCount).run s').fst = EVM.Uint256.sub (s.storage 0) 1 := by
  have h_dec := decrement_subtracts_one s
  have h_get := getCount_reads_count_value (((decrement).run s).snd)
  simp only [h_dec] at h_get
  exact h_get

/-! ## Edge Cases -/

/-- Decrementing at zero wraps to max (EVM modular subtraction). -/
theorem decrement_at_zero_wraps_max (s : ContractState) (h : s.storage 0 = 0) :
  let s' := ((decrement).run s).snd
  s'.storage 0 = EVM.MAX_UINT256 := by
  show ((decrement).run s).snd.storage 0 = EVM.MAX_UINT256
  rw [decrement_subtracts_one s, h]
  simp [EVM.MAX_UINT256, EVM.Uint256.sub, Verity.Core.MAX_UINT256,
    Verity.Core.Uint256.sub, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS]

/-! ## Summary

All 10 theorems fully proven with zero sorry:

Standalone invariant proofs:
1. increment_state_preserved_except_count
2. decrement_state_preserved_except_count
3. getCount_state_preserved

Combined spec proofs:
4. increment_getCount_meets_spec
5. decrement_getCount_meets_spec
6. two_increments_meets_spec
7. increment_decrement_meets_cancel

Read-only preservation:
8. getCount_preserves_wellformedness

Composition:
9. decrement_getCount_correct

EVM edge cases:
10. decrement_at_zero_wraps_max
-/

end Verity.Proofs.Counter.Correctness
