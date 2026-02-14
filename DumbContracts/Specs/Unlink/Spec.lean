/-
  Unlink Privacy Protocol: Formal Specification

  This file defines the formal specification for the Unlink privacy protocol,
  a ZK-SNARK based mixer using commitment-nullifier schemes.

  Core Security Properties:
  1. Exclusive control: Only note holders can withdraw their funds
  2. No double spending: Nullifiers prevent reuse
  3. Deposit-withdrawal liveness: Valid deposits are withdrawable
  4. Privacy: Cryptographic assumption about unlinkability
-/

import DumbContracts.Core
import DumbContracts.Specs.Common
import DumbContracts.Specs.Unlink.Arithmetic

namespace DumbContracts.Specs.Unlink

open DumbContracts
open DumbContracts.Specs
open DumbContracts.Core.Uint256

/-! ## Type Definitions -/

abbrev Commitment := Uint256
abbrev NullifierHash := Uint256
abbrev MerkleRoot := Uint256

structure Note where
  npk : Uint256
  token : Uint256
  amount : Uint256
  deriving Repr

-- Spec-level transaction (core fields only; the implementation adds proof/withdrawal fields)
structure Transaction where
  merkleRoot : Uint256
  nullifierHashes : List Uint256
  newCommitments : List Uint256

/-! ## Storage Layout -/

-- Storage slot indices (matching UnlinkPool.lean)
-- Slot 0: next leaf index
-- Slot 1: merkle root
-- Slot 2 + hash: nullifier spent mapping
-- Slot 3 + root: root seen mapping

/-! ## State Predicates -/

def nullifierSpent (s : ContractState) (nullifier : NullifierHash) : Prop :=
  s.storage (2 + nullifier) = 1

def rootSeen (s : ContractState) (root : MerkleRoot) : Prop :=
  s.storage (3 + root) = 1

def currentMerkleRoot (s : ContractState) : MerkleRoot :=
  s.storage 1

def nextLeafIndex (s : ContractState) : Uint256 :=
  s.storage 0

/-! ## Validation Predicates -/

def valid_deposit_input (notes : List Note) : Prop :=
  notes.length > 0 ∧
  ∀ note ∈ notes, note.amount > 0

-- Matches Solidity: both nullifiers and commitments must be non-empty
def valid_transact_input (nulls : List NullifierHash) (comms : List Commitment)
    (withdrawalAmount : Uint256) (withdrawalRecipient : Uint256) : Prop :=
  nulls.length > 0 ∧
  comms.length > 0 ∧
  nulls.length ≤ 16 ∧
  comms.length ≤ 16 ∧
  (withdrawalAmount > 0 → withdrawalRecipient ≠ 0)

/-! ## Deposit Specification -/

-- deposit_spec: observable storage effects of a deposit
-- Conjuncts (6): root change, new root seen, leaf index, nullifier preservation,
--                root preservation, context preservation
def deposit_spec
    (notes : List Note)
    (s s' : ContractState) : Prop :=
  currentMerkleRoot s' ≠ currentMerkleRoot s ∧
  rootSeen s' (currentMerkleRoot s') ∧
  nextLeafIndex s' = nextLeafIndex s + notes.length ∧
  (∀ n : Uint256, nullifierSpent s n → nullifierSpent s' n) ∧
  (∀ r : Uint256, rootSeen s r → rootSeen s' r) ∧
  sameContext s s'

/-! ## Transact (Private Transfer) Specification -/

-- transact_spec: observable storage effects of a private transaction
-- Conjuncts (9): root valid, nullifiers fresh, nullifiers spent, root change,
--                new root seen, leaf index, root preservation, nullifier preservation,
--                context preservation
def transact_spec
    (merkleRoot : MerkleRoot)
    (nullifiers : List NullifierHash)
    (newCommitments : List Commitment)
    (s s' : ContractState) : Prop :=
  rootSeen s merkleRoot ∧
  (∀ n ∈ nullifiers, ¬nullifierSpent s n) ∧
  (∀ n ∈ nullifiers, nullifierSpent s' n) ∧
  currentMerkleRoot s' ≠ currentMerkleRoot s ∧
  rootSeen s' (currentMerkleRoot s') ∧
  nextLeafIndex s' = nextLeafIndex s + newCommitments.length ∧
  (∀ r : Uint256, rootSeen s r → rootSeen s' r) ∧
  (∀ n : Uint256, nullifierSpent s n → nullifierSpent s' n) ∧
  sameContext s s'

/-! ## Core Security Theorems -/

-- Once spent, always spent (across any operation)
theorem no_double_spend_monotonic
    (s s' : ContractState) (nullifier : NullifierHash) :
    nullifierSpent s nullifier →
    (∃ notes, deposit_spec notes s s') ∨
    (∃ root nulls comms, transact_spec root nulls comms s s') →
    nullifierSpent s' nullifier := by
  intro h_spent h_op
  rcases h_op with ⟨notes, hd⟩ | ⟨root, nulls, comms, ht⟩
  · exact hd.2.2.2.1 nullifier h_spent
  · exact ht.2.2.2.2.2.2.2.1 nullifier h_spent

-- Historical roots remain valid across operations
theorem roots_cumulative
    (s s' : ContractState) (root : MerkleRoot) :
    rootSeen s root →
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    rootSeen s' root := by
  intro h_seen h_op
  rcases h_op with ⟨notes, hd⟩ | ⟨r, nulls, comms, ht⟩
  · exact hd.2.2.2.2.1 root h_seen
  · exact ht.2.2.2.2.2.2.1 root h_seen

-- Leaf index is monotonically increasing
theorem leaf_index_monotonic
    (s s' : ContractState)
    (h_no_overflow_deposit : ∀ notes, deposit_spec notes s s' → (nextLeafIndex s).val + notes.length < modulus)
    (h_no_overflow_transact : ∀ root nulls comms, transact_spec root nulls comms s s' → (nextLeafIndex s).val + comms.length < modulus) :
    (∃ notes, deposit_spec notes s s') ∨
    (∃ root nulls comms, transact_spec root nulls comms s s') →
    nextLeafIndex s' ≥ nextLeafIndex s := by
  intro h_op
  rcases h_op with ⟨notes, hd⟩ | ⟨root, nulls, comms, ht⟩
  · exact eq_add_implies_ge hd.2.2.1 (h_no_overflow_deposit notes hd)
  · exact eq_add_implies_ge ht.2.2.2.2.2.1 (h_no_overflow_transact root nulls comms ht)

/-! ## High-Level Security Properties -/

-- Once a nullifier is spent, it cannot appear in any future transaction's inputs
def no_double_spend_property (s : ContractState) : Prop :=
  ∀ (n : NullifierHash) (s' : ContractState)
    (root : MerkleRoot) (nulls : List NullifierHash) (comms : List Commitment),
    nullifierSpent s n →
    transact_spec root nulls comms s s' →
    n ∉ nulls

-- Deposits increase the leaf count (when non-empty)
def deposit_increases_leaves (notes : List Note) (s s' : ContractState) : Prop :=
  deposit_spec notes s s' →
  notes.length > 0 →
  nextLeafIndex s' > nextLeafIndex s

-- Valid historical roots remain valid after any operation
def historical_root_validity : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot),
    rootSeen s root →
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    rootSeen s' root

-- The merkle tree only grows — commitments persist forever
def commitments_cumulative : Prop :=
  ∀ (s s' : ContractState),
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    nextLeafIndex s' ≥ nextLeafIndex s

-- Transactions require a previously-seen merkle root
def transact_requires_valid_root : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot) (nulls : List NullifierHash) (comms : List Commitment),
    transact_spec root nulls comms s s' →
    rootSeen s root

-- Transactions can only spend unspent nullifiers
def transact_requires_fresh_nullifiers : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot) (nulls : List NullifierHash) (comms : List Commitment),
    transact_spec root nulls comms s s' →
    ∀ n ∈ nulls, ¬nullifierSpent s n

/-! ## Cryptographic Assumptions

These are trust assumptions about the ZK proof system and hash function.
They cannot be proven from contract logic — we state them as axioms.
-/

-- Abstract type for note secrets (the preimage known only to the note owner)
axiom NoteSecret : Type

-- Abstract relation: "this secret corresponds to this nullifier"
axiom secretDerivesNullifier : NoteSecret → NullifierHash → Prop

-- Abstract relation: "this secret corresponds to this commitment"
axiom secretDerivesCommitment : NoteSecret → Commitment → Prop

-- ZK proof soundness: if a transaction is accepted, the prover knows
-- secrets for each nullifier that correspond to commitments in the tree.
axiom zk_soundness :
  ∀ (txn : Transaction) (s s' : ContractState),
    transact_spec txn.merkleRoot txn.nullifierHashes txn.newCommitments s s' →
    ∀ nullifier ∈ txn.nullifierHashes,
      ∃ (secret : NoteSecret) (commitment : Commitment),
        secretDerivesNullifier secret nullifier ∧
        secretDerivesCommitment secret commitment

-- Nullifier binding: different secrets produce different nullifiers.
axiom nullifier_binding :
  ∀ (s1 s2 : NoteSecret) (n : NullifierHash),
    secretDerivesNullifier s1 n →
    secretDerivesNullifier s2 n →
    s1 = s2

/-! ## Derived Security Properties -/

-- Exclusive withdrawal (contract-level): to spend a nullifier, it must be fresh.
def exclusive_withdrawal : Prop :=
  ∀ (s : ContractState) (nullifier : NullifierHash),
    (∃ s' root comms, transact_spec root [nullifier] comms s s') →
    ¬nullifierSpent s nullifier

-- Exclusive withdrawal (full): combines contract enforcement with ZK soundness.
-- "To spend a nullifier, you must know the note secret AND it must be fresh."
def exclusive_withdrawal_full (txn : Transaction) (s s' : ContractState) : Prop :=
  transact_spec txn.merkleRoot txn.nullifierHashes txn.newCommitments s s' →
  ∀ nullifier ∈ txn.nullifierHashes,
    ¬nullifierSpent s nullifier ∧
    ∃ (secret : NoteSecret) (commitment : Commitment),
      secretDerivesNullifier secret nullifier ∧
      secretDerivesCommitment secret commitment

end DumbContracts.Specs.Unlink
