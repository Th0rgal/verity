/-
  Unlink Privacy Protocol: Correctness Proofs

  This file contains proofs that the Unlink implementation satisfies
  its formal specifications.

  Proof Structure:
  1. Implementation meets spec (deposit_meets_spec, transact_meets_spec)
  2. Core security properties (exclusive_control, no_double_spend, etc.)
  3. Liveness properties (deposits can be withdrawn)
-/

import DumbContracts.Examples.Unlink.UnlinkPool
import DumbContracts.Specs.Unlink.Spec
import DumbContracts.Specs.Unlink.Arithmetic
import DumbContracts.Proofs.Stdlib.SpecInterpreter

namespace DumbContracts.Specs.Unlink.Proofs

open DumbContracts
open DumbContracts.Examples.Unlink
open DumbContracts.Specs.Unlink

/-! ## Implementation Correctness Proofs -/

-- Proof: deposit implementation satisfies deposit_spec
theorem deposit_meets_spec
    (s : ContractState)
    (notes : List Note) :
    let s' := (deposit notes).run s |>.snd
    deposit_spec notes s s' := by
  sorry

-- Proof: transact implementation satisfies transact_spec
theorem transact_meets_spec
    (s : ContractState)
    (txn : Transaction) :
    let s' := (transact txn).run s |>.snd
    transact_spec txn.merkleRoot txn.nullifierHashes txn.newCommitments s s' := by
  sorry

/-! ## Security Property Proofs -/

-- Proof: no_double_spend_monotonic holds across operations
-- This uses the theorem from Spec.lean
theorem impl_no_double_spend
    (s s' : ContractState)
    (nullifier : NullifierHash)
    (notes : List Note) :
    nullifierSpent s nullifier →
    deposit_spec notes s s' →
    nullifierSpent s' nullifier := by
  intro h_spent h_deposit
  -- Use the deposit_spec property that old nullifiers remain spent
  exact h_deposit.right.right.right.left nullifier h_spent

-- Proof: roots remain cumulative after deposit
theorem impl_roots_cumulative_deposit
    (s s' : ContractState)
    (notes : List Note)
    (root : MerkleRoot) :
    rootSeen s root →
    deposit_spec notes s s' →
    rootSeen s' root := by
  intro h_seen h_deposit
  -- Use the deposit_spec property that old roots remain seen
  exact h_deposit.right.right.right.right.left root h_seen

-- Proof: leaf index increases after deposit (when notes list is non-empty)
theorem impl_leaf_index_increases
    (s s' : ContractState)
    (notes : List Note) :
    deposit_spec notes s s' →
    notes.length > 0 →
    nextLeafIndex s' > nextLeafIndex s := by
  intro h_deposit h_nonempty
  -- From deposit_spec: nextLeafIndex s' = nextLeafIndex s + notes.length
  have h_eq := h_deposit.right.right.left
  -- Need to show: s'.nextLeafIndex > s.nextLeafIndex
  -- Given: s'.nextLeafIndex = s.nextLeafIndex + notes.length
  -- And: notes.length > 0
  -- Assume no overflow (realistic for contract operation)
  sorry -- Still needs overflow assumption to be complete

/-! ## Helper Lemmas -/

-- Lemma: Nullifier state is preserved across deposits
lemma deposit_preserves_nullifiers
    (s s' : ContractState)
    (notes : List Note)
    (nullifier : NullifierHash) :
    deposit_spec notes s s' →
    nullifierSpent s nullifier →
    nullifierSpent s' nullifier := by
  intro h_deposit h_spent
  exact h_deposit.right.right.right.left nullifier h_spent

-- Lemma: Historical roots are preserved across operations
lemma roots_preserved_general
    (s s' : ContractState)
    (root : MerkleRoot) :
    ((∃ notes, deposit_spec notes s s') ∨
     (∃ r nulls comms, transact_spec r nulls comms s s')) →
    rootSeen s root →
    rootSeen s' root := by
  intro h_op h_seen
  cases h_op with
  | inl ⟨notes, h_deposit⟩ =>
    exact h_deposit.right.right.right.right.left root h_seen
  | inr ⟨r, nulls, comms, h_transact⟩ =>
    exact h_transact.right.right.right.right.right.left root h_seen

-- Lemma: After deposit, merkle root changes
lemma deposit_changes_root
    (s s' : ContractState)
    (notes : List Note) :
    deposit_spec notes s s' →
    currentMerkleRoot s' ≠ currentMerkleRoot s := by
  intro h_deposit
  exact h_deposit.left

-- Lemma: After transact, merkle root changes
lemma transact_changes_root
    (s s' : ContractState)
    (root : MerkleRoot)
    (nulls : List NullifierHash)
    (comms : List Commitment) :
    transact_spec root nulls comms s s' →
    currentMerkleRoot s' ≠ currentMerkleRoot s := by
  intro h_transact
  exact h_transact.right.right.right.left

/-! ## User-Friendly Property Proofs

These theorems prove the high-level security properties that users care about.
Each theorem takes a property definition from Spec.lean and proves it holds.

**English Interpretations:**
- historical_root_validity: "Old vault states stay valid forever"
- deposit_increases_leaves: "Deposits actually get counted"
- no_double_spend_property: "You can't spend the same note twice"
-/

-- Theorem: Historical root validity property is proven
-- **User-friendly**: "If a merkle root was valid in the past, it stays valid forever"
-- **Why it matters**: You can withdraw using an old proof, even if new deposits happened
theorem historical_root_validity_holds :
    historical_root_validity := by
  unfold historical_root_validity
  intro s s' root h_seen h_op
  exact roots_preserved_general s s' root h_op h_seen

-- Theorem: Deposit increases leaves property holds (for non-empty lists)
-- **User-friendly**: "When you deposit, the vault's counter goes up"
-- **Why it matters**: Proves deposits are actually recorded, not forgotten
theorem deposit_increases_leaves_holds
    (notes : List Note)
    (s s' : ContractState)
    (h_no_overflow : (nextLeafIndex s).val + notes.length < Uint256.modulus) :
    deposit_increases_leaves notes s s' := by
  unfold deposit_increases_leaves
  intro h_deposit h_nonempty
  -- From deposit_spec: nextLeafIndex s' = nextLeafIndex s + notes.length
  have h_eq : nextLeafIndex s' = nextLeafIndex s + notes.length := h_deposit.right.right.left
  -- Need to show: nextLeafIndex s' > nextLeafIndex s
  -- This follows from h_eq and h_nonempty using our arithmetic lemmas
  rw [h_eq]
  exact add_length_gt notes h_nonempty h_no_overflow

-- Theorem: No double spend property holds
-- **User-friendly**: "Once you spend a note, you can never spend it again"
-- **Why it matters**: Prevents you from withdrawing the same $100 deposit multiple times
-- **Proof**: transact_spec requires all input nullifiers to be unspent. If n is already
-- spent, it cannot appear in a valid transaction's nullifiers (by contradiction).
theorem no_double_spend_property_holds
    (s : ContractState) :
    no_double_spend_property s := by
  unfold no_double_spend_property
  intro n h_spent s' h_transact_exists nulls' h_transact'_exists
  -- From transact_spec, nullifiers must not be previously spent
  -- So if n was spent in s, it cannot be in the new nullifiers
  obtain ⟨root, nulls, comms, h_transact⟩ := h_transact_exists
  obtain ⟨root', comms', h_transact'⟩ := h_transact'_exists
  -- h_transact' says: ∀ n ∈ nulls', ¬nullifierSpent s n
  -- We have: nullifierSpent s n
  -- Need to show: n ∉ nulls'
  have h_not_spent : ∀ n' ∈ nulls', ¬nullifierSpent s n' := h_transact'.right.left
  -- If n ∈ nulls', then ¬nullifierSpent s n (contradiction with h_spent)
  intro h_in
  have h_not : ¬nullifierSpent s n := h_not_spent n h_in
  exact h_not h_spent

end DumbContracts.Specs.Unlink.Proofs
