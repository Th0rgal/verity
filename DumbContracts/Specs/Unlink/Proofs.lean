/-
  Unlink Privacy Protocol: Correctness Proofs

  This file contains proofs that the Unlink implementation satisfies
  its formal specifications.

  Proof Structure:
  1. Input validation properties
  2. Auxiliary lemmas (root preservation, nullifier monotonicity)
  3. User-friendly security property proofs
-/

import DumbContracts.Specs.Unlink.Spec
import DumbContracts.Specs.Unlink.Arithmetic

namespace DumbContracts.Specs.Unlink.Proofs

open DumbContracts
open DumbContracts.Specs.Unlink
open DumbContracts.Core.Uint256

/-! ## Input Validation Properties -/

theorem valid_deposit_implies_positive_amounts
    (notes : List Note) :
    valid_deposit_input notes →
    ∀ note ∈ notes, note.amount > 0 := by
  intro h; exact h.2

theorem valid_transact_implies_has_inputs
    (nulls : List NullifierHash) (comms : List Commitment)
    (withdrawalAmount withdrawalRecipient : Uint256) :
    valid_transact_input nulls comms withdrawalAmount withdrawalRecipient →
    nulls.length > 0 := by
  intro h; exact h.1

theorem valid_transact_withdrawal_implies_valid_recipient
    (nulls : List NullifierHash) (comms : List Commitment)
    (withdrawalAmount withdrawalRecipient : Uint256) :
    valid_transact_input nulls comms withdrawalAmount withdrawalRecipient →
    withdrawalAmount > 0 → withdrawalRecipient ≠ 0 := by
  intro h ha; exact h.2.2.2 ha

/-! ## Auxiliary Theorems -/

theorem deposit_preserves_nullifiers
    (s s' : ContractState) (notes : List Note) (nullifier : NullifierHash) :
    deposit_spec notes s s' → nullifierSpent s nullifier →
    nullifierSpent s' nullifier := by
  intro hd hn; exact hd.2.2.2.1 nullifier hn

theorem roots_preserved_general
    (s s' : ContractState) (root : MerkleRoot) :
    ((∃ notes, deposit_spec notes s s') ∨
     (∃ r nulls comms, transact_spec r nulls comms s s')) →
    rootSeen s root → rootSeen s' root := by
  intro h_op h_seen
  rcases h_op with ⟨notes, hd⟩ | ⟨r, nulls, comms, ht⟩
  · exact hd.2.2.2.2.1 root h_seen
  · exact ht.2.2.2.2.2.2.1 root h_seen

theorem deposit_changes_root (s s' : ContractState) (notes : List Note) :
    deposit_spec notes s s' → currentMerkleRoot s' ≠ currentMerkleRoot s := by
  intro hd; exact hd.1

theorem transact_changes_root
    (s s' : ContractState) (root : MerkleRoot)
    (nulls : List NullifierHash) (comms : List Commitment) :
    transact_spec root nulls comms s s' →
    currentMerkleRoot s' ≠ currentMerkleRoot s := by
  intro ht; exact ht.2.2.2.1

/-! ## User-Friendly Security Property Proofs -/

theorem historical_root_validity_holds : historical_root_validity := by
  unfold historical_root_validity
  intro s s' root h_seen h_op
  exact roots_preserved_general s s' root h_op h_seen

theorem deposit_increases_leaves_holds
    (notes : List Note) (s s' : ContractState)
    (h_no_overflow : (nextLeafIndex s).val + notes.length < modulus) :
    deposit_increases_leaves notes s s' := by
  unfold deposit_increases_leaves
  intro hd hn; rw [hd.2.2.1]; exact add_length_gt notes hn h_no_overflow

theorem no_double_spend_property_holds (s : ContractState) :
    no_double_spend_property s := by
  unfold no_double_spend_property
  intro n hs s' _ nulls' ⟨root', comms', ht'⟩
  intro h_in; exact (ht'.2.1 n h_in) hs

theorem commitments_cumulative_holds
    (h_no_overflow_deposit : ∀ s s' notes,
      deposit_spec notes s s' → (nextLeafIndex s).val + notes.length < modulus)
    (h_no_overflow_transact : ∀ s s' root nulls comms,
      transact_spec root nulls comms s s' → (nextLeafIndex s).val + comms.length < modulus) :
    commitments_cumulative := by
  unfold commitments_cumulative
  intro s s' h_op
  exact leaf_index_monotonic s s' (h_no_overflow_deposit s s') (h_no_overflow_transact s s') h_op

theorem transact_requires_valid_root_holds : transact_requires_valid_root := by
  unfold transact_requires_valid_root
  intro s s' root nulls comms ht; exact ht.1

theorem transact_requires_fresh_nullifiers_holds : transact_requires_fresh_nullifiers := by
  unfold transact_requires_fresh_nullifiers
  intro s s' root nulls comms ht; exact ht.2.1

theorem exclusive_withdrawal_holds : exclusive_withdrawal := by
  unfold exclusive_withdrawal
  intro s nullifier ⟨s', root, comms, ht⟩
  have := ht.2.1 nullifier (List.Mem.head _)
  exact this

theorem exclusive_withdrawal_full_holds (txn : Transaction) (s s' : ContractState) :
    exclusive_withdrawal_full txn s s' := by
  unfold exclusive_withdrawal_full
  intro ht nullifier h_mem
  exact ⟨ht.2.1 nullifier h_mem, zk_soundness txn s s' ht nullifier h_mem⟩

end DumbContracts.Specs.Unlink.Proofs
