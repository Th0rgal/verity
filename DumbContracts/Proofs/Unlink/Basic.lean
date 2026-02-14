/-
  Unlink Privacy Protocol: Implementation-to-Spec Correctness Proofs

  This file proves that the Unlink EDSL implementation (UnlinkPool.lean)
  satisfies the formal specification (Spec.lean).

  Key result: insertLeaves correctly updates merkle root, marks root as
  seen, increments leaf index, and preserves nullifier state + context.
  This is the core building block for deposit_meets_spec and transact_meets_spec.
-/

import DumbContracts.Core
import DumbContracts.Examples.Unlink.UnlinkPool
import DumbContracts.Specs.Unlink.Spec

namespace DumbContracts.Proofs.Unlink

open DumbContracts
open DumbContracts.Specs.Unlink

/-! ## Slot separation lemmas

The storage layout uses distinct Nat slots:
  - nextLeafIndex: slot 0
  - merkleRoot: slot 1
  - nullifierHashes(h): slot 2 + h.val (≥ 2)
  - rootSeen(r): slot 3 + r.val (≥ 3)

Slots 0 and 1 never collide with nullifier or root-seen slots.
-/

theorem rootSeen_slot_ne_zero (r : Uint256) : 3 + r.val ≠ 0 := by omega
theorem rootSeen_slot_ne_one (r : Uint256) : 3 + r.val ≠ 1 := by omega
theorem nullifier_slot_ne_zero (h : Uint256) : 2 + h.val ≠ 0 := by omega
theorem nullifier_slot_ne_one (h : Uint256) : 2 + h.val ≠ 1 := by omega

/-! ## insertLeaves: Individual Property Proofs

insertLeaves is the core state-changing function used by both deposit and
transact. We prove each storage effect individually.

Note: We qualify implementation names explicitly to avoid ambiguity with
spec predicates (e.g., Specs.Unlink.rootSeen vs Examples.Unlink.rootSeen).

After monadic unfolding, Lean normalizes `a + b` as `b + a` for Uint256.
We use `Core.Uint256.add_comm` to handle this systematically.
-/

-- Tactic macro for unfolding insertLeaves monadic code
macro "unfold_insertLeaves" : tactic =>
  `(tactic|
    (unfold Examples.Unlink.insertLeaves Examples.Unlink.markRootSeen
     simp only [getStorage, setStorage, DumbContracts.bind, DumbContracts.pure,
       Contract.run, ContractResult.snd, Bind.bind, Pure.pure,
       Examples.Unlink.merkleRoot, Examples.Unlink.nextLeafIndex,
       Examples.Unlink.rootSeen, instMonadContract]))

-- Property 1: Merkle root is updated (slot 1)
set_option maxRecDepth 1024 in
theorem insertLeaves_updates_root (commitments : List Uint256) (s : ContractState) :
    ((Examples.Unlink.insertLeaves commitments).run s).snd.storage 1 =
    s.storage 1 + commitments.length := by
  unfold_insertLeaves
  split
  · next h => exact absurd h (by simp [beq_iff_eq])
  · split
    · next h => exfalso; simp [beq_iff_eq] at h; omega
    · simp [Core.Uint256.add_comm]

-- Property 2: New root is marked as seen
set_option maxRecDepth 1024 in
theorem insertLeaves_marks_root_seen (commitments : List Uint256) (s : ContractState) :
    let newRoot := s.storage 1 + (commitments.length : Uint256)
    ((Examples.Unlink.insertLeaves commitments).run s).snd.storage (3 + newRoot.val) = 1 := by
  unfold_insertLeaves
  simp [Core.Uint256.add_comm]

-- Property 3: Leaf index is updated (slot 0)
set_option maxRecDepth 1024 in
theorem insertLeaves_updates_leaf_index (commitments : List Uint256) (s : ContractState) :
    ((Examples.Unlink.insertLeaves commitments).run s).snd.storage 0 =
    s.storage 0 + commitments.length := by
  unfold_insertLeaves
  simp only [beq_self_eq_true, ↓reduceIte]
  have h : ¬(0 = 3 + (Core.Uint256.ofNat commitments.length + s.storage 1).val) := by omega
  simp [h, Core.Uint256.add_comm]

-- Property 4: Arbitrary slot preservation
set_option maxRecDepth 1024 in
theorem insertLeaves_preserves_slot (commitments : List Uint256) (s : ContractState)
    (slot : Nat) (h0 : slot ≠ 0) (h1 : slot ≠ 1)
    (h3 : slot ≠ 3 + (s.storage 1 + (commitments.length : Uint256)).val) :
    ((Examples.Unlink.insertLeaves commitments).run s).snd.storage slot =
    s.storage slot := by
  unfold_insertLeaves
  have h3' : slot ≠ 3 + (Core.Uint256.ofNat commitments.length + s.storage 1).val := by
    rw [show Core.Uint256.ofNat commitments.length + s.storage 1 =
         s.storage 1 + Core.Uint256.ofNat commitments.length
       from Core.Uint256.add_comm _ _]
    exact h3
  simp [beq_iff_eq, h0, h1, h3']

-- Property 5: Context is preserved
set_option maxRecDepth 1024 in
theorem insertLeaves_preserves_context (commitments : List Uint256) (s : ContractState) :
    Specs.sameContext s
    ((Examples.Unlink.insertLeaves commitments).run s).snd := by
  unfold_insertLeaves
  unfold Specs.sameContext
  exact ⟨rfl, rfl, rfl, rfl⟩

-- Property 6: insertLeaves always succeeds (no require guards)
set_option maxRecDepth 1024 in
theorem insertLeaves_succeeds (commitments : List Uint256) (s : ContractState) :
    ∃ s', (Examples.Unlink.insertLeaves commitments).run s =
    ContractResult.success () s' := by
  unfold_insertLeaves
  exact ⟨_, rfl⟩

/-! ## Spec-Level Properties

These connect insertLeaves to the formal spec predicates from Spec.lean.
-/

-- The new merkle root differs from the old one (when commitments non-empty)
theorem insertLeaves_root_changes (commitments : List Uint256) (s : ContractState)
    (h_nonempty : commitments.length > 0)
    (h_no_overflow : (s.storage 1).val + commitments.length < Core.Uint256.modulus) :
    currentMerkleRoot ((Examples.Unlink.insertLeaves commitments).run s).snd ≠
    currentMerkleRoot s := by
  simp only [currentMerkleRoot]
  rw [insertLeaves_updates_root]
  exact gt_implies_ne (add_length_gt commitments h_nonempty h_no_overflow)

-- The new root is marked as seen (spec predicate)
theorem insertLeaves_new_root_seen (commitments : List Uint256) (s : ContractState) :
    Specs.Unlink.rootSeen
      ((Examples.Unlink.insertLeaves commitments).run s).snd
      (currentMerkleRoot ((Examples.Unlink.insertLeaves commitments).run s).snd) := by
  simp only [Specs.Unlink.rootSeen, currentMerkleRoot]
  rw [insertLeaves_updates_root]
  exact insertLeaves_marks_root_seen commitments s

-- The leaf index is correctly updated (spec predicate)
set_option maxRecDepth 1024 in
theorem insertLeaves_leaf_index_updated (commitments : List Uint256) (s : ContractState) :
    Specs.Unlink.nextLeafIndex
      ((Examples.Unlink.insertLeaves commitments).run s).snd =
    Specs.Unlink.nextLeafIndex s + commitments.length := by
  simp only [Specs.Unlink.nextLeafIndex]
  exact insertLeaves_updates_leaf_index commitments s

-- Nullifier spent status is preserved
theorem insertLeaves_preserves_nullifiers (commitments : List Uint256) (s : ContractState)
    (nullifier : Uint256)
    (h_no_col : 2 + nullifier.val ≠ 3 + (s.storage 1 + (commitments.length : Uint256)).val) :
    nullifierSpent s nullifier →
    nullifierSpent ((Examples.Unlink.insertLeaves commitments).run s).snd nullifier := by
  simp only [Specs.Unlink.nullifierSpent]
  intro h
  rw [insertLeaves_preserves_slot commitments s _ (by omega) (by omega) h_no_col]
  exact h

-- Root seen status is preserved for previously-seen roots
theorem insertLeaves_preserves_roots (commitments : List Uint256) (s : ContractState)
    (root : Uint256) :
    Specs.Unlink.rootSeen s root →
    Specs.Unlink.rootSeen
      ((Examples.Unlink.insertLeaves commitments).run s).snd root := by
  simp only [Specs.Unlink.rootSeen]
  intro h
  by_cases h_eq : root.val = (s.storage 1 + (commitments.length : Uint256)).val
  · rw [show 3 + root.val = 3 + (s.storage 1 + (commitments.length : Uint256)).val from by omega]
    exact insertLeaves_marks_root_seen commitments s
  · rw [insertLeaves_preserves_slot commitments s (3 + root.val) (by omega) (by omega)
      (by omega)]
    exact h

end DumbContracts.Proofs.Unlink
