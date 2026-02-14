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

/-! ## Input Validation Properties -/

-- Theorem: Valid deposits have positive amounts
-- **User-friendly**: "You can't deposit zero or negative amounts"
-- **Why it matters**: Prevents dust/spam deposits and undefined behavior
theorem valid_deposit_implies_positive_amounts
    (notes : List Note) :
    valid_deposit_input notes →
    ∀ note ∈ notes, note.amount > 0 := by
  intro h_valid
  exact h_valid.right

-- Theorem: Valid transacts have non-zero nullifiers
-- **User-friendly**: "Every transaction must spend at least one note"
-- **Why it matters**: No-op transactions are rejected
theorem valid_transact_implies_has_inputs
    (nulls : List NullifierHash)
    (comms : List Commitment)
    (withdrawalAmount withdrawalRecipient : Uint256) :
    valid_transact_input nulls comms withdrawalAmount withdrawalRecipient →
    nulls.length > 0 := by
  intro h_valid
  exact h_valid.left

-- Theorem: Valid transacts with withdrawals have valid recipients
-- **User-friendly**: "If you're withdrawing, you must specify where to send the money"
-- **Why it matters**: Prevents accidental burns/lost funds
theorem valid_transact_withdrawal_implies_valid_recipient
    (nulls : List NullifierHash)
    (comms : List Commitment)
    (withdrawalAmount withdrawalRecipient : Uint256) :
    valid_transact_input nulls comms withdrawalAmount withdrawalRecipient →
    withdrawalAmount > 0 →
    withdrawalRecipient ≠ 0 := by
  intro h_valid h_amount
  exact h_valid.right.right.right h_amount

/-! ## Implementation Correctness Proofs -/

-- These theorems connect the EDSL implementation to the declarative spec.
-- They require reasoning about the Contract monad (bind chains, for-loops,
-- require guards) which needs proof infrastructure not yet available.
--
-- Current blockers:
-- 1. deposit uses `for` loops and `mut` which don't unfold cleanly
-- 2. Both functions use `require` guards that cause reverts on invalid input,
--    so the theorems need preconditions (valid input + root seen, etc.)
-- 3. Storage slot distinctness reasoning is needed for insertLeaves
--
-- These are deferred until the monad proof infrastructure supports
-- loop reasoning and conditional branching.

theorem deposit_meets_spec
    (s : ContractState)
    (notes : List Note) :
    let s' := (deposit notes).run s |>.snd
    deposit_spec notes s s' := by
  sorry

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
    (notes : List Note)
    (h_no_overflow : (nextLeafIndex s).val + notes.length < Uint256.modulus) :
    deposit_spec notes s s' →
    notes.length > 0 →
    nextLeafIndex s' > nextLeafIndex s := by
  intro h_deposit h_nonempty
  -- From deposit_spec: nextLeafIndex s' = nextLeafIndex s + notes.length
  have h_eq := h_deposit.right.right.left
  -- Use arithmetic lemma: a + n > a when n > 0
  rw [h_eq]
  exact add_length_gt notes h_nonempty h_no_overflow

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

-- Theorem: Commitments are cumulative (leaf count is monotonic)
-- **User-friendly**: "The vault keeps growing - deposits are never lost"
-- **Why it matters**: Proves that commitments persist forever, the system doesn't delete deposits
theorem commitments_cumulative_holds
    (h_no_overflow_deposit : ∀ s s' notes, deposit_spec notes s s' → (nextLeafIndex s).val + notes.length < Uint256.modulus)
    (h_no_overflow_transact : ∀ s s' root nulls comms, transact_spec root nulls comms s s' → (nextLeafIndex s).val + comms.length < Uint256.modulus) :
    commitments_cumulative := by
  unfold commitments_cumulative
  intro s s' h_op
  exact leaf_index_monotonic s s' (h_no_overflow_deposit s s') (h_no_overflow_transact s s') h_op

-- Theorem: Transact requires valid root
-- **User-friendly**: "You can only withdraw using proofs from actual vault states"
-- **Why it matters**: Can't forge transactions with fake merkle roots
theorem transact_requires_valid_root_holds :
    transact_requires_valid_root := by
  unfold transact_requires_valid_root
  intro s s' root nulls comms h_transact
  -- From transact_spec, the first condition is: rootSeen s root
  exact h_transact.left

-- Theorem: Transact requires fresh nullifiers
-- **User-friendly**: "Transactions can only spend unspent notes"
-- **Why it matters**: Enforces the "once spent, always spent" rule at transaction time
theorem transact_requires_fresh_nullifiers_holds :
    transact_requires_fresh_nullifiers := by
  unfold transact_requires_fresh_nullifiers
  intro s s' root nulls comms h_transact
  -- From transact_spec, the second condition is: ∀ n ∈ nulls, ¬nullifierSpent s n
  exact h_transact.right.left

-- Theorem: Exclusive withdrawal (contract-level) holds
-- **User-friendly**: "To withdraw, the nullifier must be fresh (unspent)"
-- **Why it matters**: Combined with ZK soundness, this guarantees only the
-- note secret holder can withdraw
theorem exclusive_withdrawal_holds :
    exclusive_withdrawal := by
  unfold exclusive_withdrawal
  intro s nullifier h_can_spend
  obtain ⟨s', root, comms, h_transact⟩ := h_can_spend
  have h_fresh : ∀ n ∈ [nullifier], ¬nullifierSpent s n := h_transact.right.left
  simp at h_fresh
  exact h_fresh

-- Theorem: Full exclusive withdrawal (contract + crypto) holds
-- Uses zk_soundness axiom to combine both halves of the security guarantee
theorem exclusive_withdrawal_full_holds (txn : Transaction) (s s' : ContractState) :
    exclusive_withdrawal_full txn s s' := by
  unfold exclusive_withdrawal_full
  intro h_transact nullifier h_mem
  constructor
  · -- Contract enforcement: nullifier was fresh
    exact h_transact.right.left nullifier h_mem
  · -- Cryptographic enforcement: spender knows the secret
    exact zk_soundness txn s s' h_transact nullifier h_mem

end DumbContracts.Specs.Unlink.Proofs
