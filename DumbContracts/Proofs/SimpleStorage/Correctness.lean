/-
  Advanced correctness proofs for SimpleStorage contract.

  Proves deeper properties beyond Basic.lean:
  - store_retrieve_roundtrip (matching exact spec form)
  - Standalone invariant proofs matching Invariants.lean definitions
  - Retrieve preserves well-formedness
-/

import DumbContracts.Core
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Specs.SimpleStorage.Spec
import DumbContracts.Specs.SimpleStorage.Invariants
import DumbContracts.Proofs.SimpleStorage.Basic

namespace DumbContracts.Proofs.SimpleStorage.Correctness

open DumbContracts
open DumbContracts.Examples
open DumbContracts.Specs.SimpleStorage
open DumbContracts.Proofs.SimpleStorage

/-! ## Roundtrip Specification

Prove store_retrieve_roundtrip in its exact spec form from Spec.lean:
for any s_after_store satisfying store_spec, retrieve returns the stored value.
-/

/-- The foundational roundtrip property: any state satisfying store_spec
    will yield the stored value on retrieve. -/
theorem store_retrieve_roundtrip_holds (value : Uint256) (s : ContractState) :
  store_retrieve_roundtrip value s := by
  intro s_after h_spec
  simp [retrieve_spec]
  simp [store_spec] at h_spec
  exact h_spec.1.symm

/-! ## Standalone Invariant Proofs

Prove that store satisfies each invariant from Invariants.lean individually.
-/

/-- store preserves storage isolation: slot 0 update doesn't affect other slots. -/
theorem store_preserves_storage_isolated (s : ContractState) (value : Uint256) (slot : Nat) :
  let s' := ((store value).run s).snd
  storage_isolated s s' slot := by
  simp [storage_isolated]
  intro h_ne
  have h := store_meets_spec s value
  simp [store_spec] at h
  exact h.2.1 slot h_ne

/-- store preserves address storage. -/
theorem store_preserves_addr_storage (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  addr_storage_unchanged s s' := by
  simp [addr_storage_unchanged]
  have h := store_meets_spec s value
  simp [store_spec] at h
  exact h.2.2.1

/-- store preserves mapping storage. -/
theorem store_preserves_map_storage (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  map_storage_unchanged s s' := by
  simp [map_storage_unchanged]
  have h := store_meets_spec s value
  simp [store_spec] at h
  exact h.2.2.2.1

/-- store preserves context (sender, thisAddress). -/
theorem store_preserves_context (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  context_preserved s s' := by
  have h := store_meets_spec s value
  simp [store_spec] at h
  simpa [Specs.sameContext, context_preserved] using h.2.2.2.2

/-- retrieve preserves all state (read-only, trivially preserves everything). -/
theorem retrieve_preserves_context (s : ContractState) :
  let s' := ((retrieve).run s).snd
  context_preserved s s' := by
  have h := retrieve_preserves_state s
  simp [h, Specs.sameContext]

/-- retrieve preserves well-formedness. -/
theorem retrieve_preserves_wellformedness (s : ContractState) (h : WellFormedState s) :
  let s' := ((retrieve).run s).snd
  WellFormedState s' := by
  have h_pres := retrieve_preserves_state s
  rw [h_pres]
  exact h

/-! ## Summary

All 7 theorems fully proven with zero sorry:

Roundtrip:
1. store_retrieve_roundtrip_holds

Standalone invariants:
2. store_preserves_storage_isolated
3. store_preserves_addr_storage
4. store_preserves_map_storage
5. store_preserves_context
6. retrieve_preserves_context

Well-formedness:
7. retrieve_preserves_wellformedness
-/

end DumbContracts.Proofs.SimpleStorage.Correctness
