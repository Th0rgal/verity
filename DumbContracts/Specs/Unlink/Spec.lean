/-
  Unlink Privacy Protocol: Formal Specification

  This file defines the formal specification for the Unlink privacy protocol,
  a ZK-SNARK based mixer using commitment-nullifier schemes.

  Simplified to focus on core storage-based properties that can be verified.

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

/-! ## Type Definitions -/

-- A commitment to a note (hash of npk, token, amount)
abbrev Commitment := Uint256

-- A nullifier hash (prevents double spending)
abbrev NullifierHash := Uint256

-- A merkle root representing the state of all commitments
abbrev MerkleRoot := Uint256

-- A note contains: nullifier public key, token address, amount
structure Note where
  npk : Uint256        -- nullifier public key
  token : Uint256      -- token address (as uint256)
  amount : Uint256     -- amount of tokens
  deriving Repr

/-! ## Storage Layout Constants -/

-- Storage slot indices (matching UnlinkPool.lean)
def NEXT_LEAF_INDEX_SLOT : Nat := 0
def MERKLE_ROOT_SLOT : Nat := 1
-- Nullifier mapping starts at slot 2 + nullifierHash
-- Root seen mapping starts at slot 3 + root (simplified for spec)
def VERIFIER_ROUTER_SLOT : Nat := 4

/-! ## State Predicates (Storage-Based) -/

-- Check if a nullifier has been spent (value = 1 in storage)
def nullifierSpent (s : ContractState) (nullifier : NullifierHash) : Prop :=
  s.storage (2 + nullifier) = 1

-- Check if a root has been seen (value = 1 in storage)
def rootSeen (s : ContractState) (root : MerkleRoot) : Prop :=
  s.storage (3 + root) = 1

-- Get the current merkle root from storage
def currentMerkleRoot (s : ContractState) : MerkleRoot :=
  s.storage MERKLE_ROOT_SLOT

-- Get the next leaf index from storage
def nextLeafIndex (s : ContractState) : Uint256 :=
  s.storage NEXT_LEAF_INDEX_SLOT

/-! ## Validation Predicates -/

-- Valid deposit input: non-empty notes list with positive amounts
def valid_deposit_input (notes : List Note) : Prop :=
  notes.length > 0 ∧
  ∀ note ∈ notes, note.amount > 0

-- Valid transact input: bounded nullifier/commitment lists, valid withdrawal params
def valid_transact_input (nulls : List NullifierHash) (comms : List Commitment)
    (withdrawalAmount : Uint256) (withdrawalRecipient : Uint256) : Prop :=
  nulls.length > 0 ∧
  nulls.length ≤ 16 ∧
  comms.length ≤ 16 ∧
  (withdrawalAmount > 0 → withdrawalRecipient ≠ 0)

/-! ## Deposit Specification -/

-- Simplified deposit_spec focusing on observable storage changes
-- In reality, tokens are transferred via external calls (modeled later)
-- Precondition: valid_deposit_input notes
def deposit_spec
    (notes : List Note)
    (s s' : ContractState) : Prop :=
  -- Merkle root changes (new commitments added)
  currentMerkleRoot s' ≠ currentMerkleRoot s ∧
  -- New root is marked as seen
  rootSeen s' (currentMerkleRoot s') ∧
  -- Leaf index increases by number of notes
  nextLeafIndex s' = nextLeafIndex s + notes.length ∧
  -- Old nullifiers remain spent
  (∀ n : Uint256, nullifierSpent s n → nullifierSpent s' n) ∧
  -- Old roots remain seen
  (∀ r : Uint256, rootSeen s r → rootSeen s' r) ∧
  -- Context unchanged (sender, address, value, timestamp)
  sameContext s s'

/-! ## Transact (Private Transfer) Specification -/

-- Simplified transact_spec focusing on nullifier and merkle tree updates
-- Precondition: valid_transact_input nullifiers newCommitments withdrawalAmount withdrawalRecipient
-- (withdrawal params not included in this simplified spec)
def transact_spec
    (merkleRoot : MerkleRoot)
    (nullifiers : List NullifierHash)
    (newCommitments : List Commitment)
    (s s' : ContractState) : Prop :=
  -- Provided merkle root was previously seen
  rootSeen s merkleRoot ∧
  -- All nullifiers were NOT previously spent
  (∀ n ∈ nullifiers, ¬nullifierSpent s n) ∧
  -- All nullifiers are NOW marked as spent
  (∀ n ∈ nullifiers, nullifierSpent s' n) ∧
  -- Merkle root changes (new commitments added)
  currentMerkleRoot s' ≠ currentMerkleRoot s ∧
  -- New root is marked as seen
  rootSeen s' (currentMerkleRoot s') ∧
  -- Leaf index increases by number of new commitments
  nextLeafIndex s' = nextLeafIndex s + newCommitments.length ∧
  -- Old roots remain seen
  (∀ r : Uint256, rootSeen s r → rootSeen s' r) ∧
  -- Old nullifiers remain spent (monotonicity)
  (∀ n : Uint256, nullifierSpent s n → nullifierSpent s' n) ∧
  -- Context unchanged
  sameContext s s'

/-! ## Core Security Theorems -/

-- Theorem: No double spending - once spent, always spent
theorem no_double_spend_monotonic
    (s s' : ContractState)
    (nullifier : NullifierHash) :
    nullifierSpent s nullifier →
    -- After any valid operation
    (∃ notes, deposit_spec notes s s') ∨
    (∃ root nulls comms, transact_spec root nulls comms s s') →
    -- Nullifier remains spent
    nullifierSpent s' nullifier := by
  intro h_spent h_op
  cases h_op with
  | inl ⟨notes, h_deposit⟩ =>
    -- From deposit_spec, old nullifiers remain spent
    exact h_deposit.right.right.right.left nullifier h_spent
  | inr ⟨root, nulls, comms, h_transact⟩ =>
    -- From transact_spec, old nullifiers remain spent
    exact h_transact.right.right.right.right.right.right.left nullifier h_spent

-- Theorem: Roots are cumulative (historical tracking)
theorem roots_cumulative
    (s s' : ContractState)
    (root : MerkleRoot) :
    rootSeen s root →
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    rootSeen s' root := by
  intro h_seen h_op
  cases h_op with
  | inl ⟨notes, h_deposit⟩ =>
    exact h_deposit.right.right.right.right.left root h_seen
  | inr ⟨r, nulls, comms, h_transact⟩ =>
    exact h_transact.right.right.right.right.right.left root h_seen

-- Theorem: Leaf index is monotonically increasing
theorem leaf_index_monotonic
    (s s' : ContractState)
    (h_no_overflow_deposit : ∀ notes, deposit_spec notes s s' → (nextLeafIndex s).val + notes.length < Uint256.modulus)
    (h_no_overflow_transact : ∀ root nulls comms, transact_spec root nulls comms s s' → (nextLeafIndex s).val + comms.length < Uint256.modulus) :
    (∃ notes, deposit_spec notes s s') ∨
    (∃ root nulls comms, transact_spec root nulls comms s s') →
    nextLeafIndex s' ≥ nextLeafIndex s := by
  intro h_op
  cases h_op with
  | inl ⟨notes, h_deposit⟩ =>
    -- From deposit_spec: s'.nextLeafIndex = s.nextLeafIndex + notes.length
    have h_eq := h_deposit.right.right.left
    have h_overflow := h_no_overflow_deposit notes h_deposit
    exact eq_add_implies_ge h_eq h_overflow
  | inr ⟨root, nulls, comms, h_transact⟩ =>
    have h_eq := h_transact.right.right.right.right.left
    have h_overflow := h_no_overflow_transact root nulls comms h_transact
    exact eq_add_implies_ge h_eq h_overflow

/-! ## High-Level Security Properties (User-Friendly Statements) -/

-- Property: Once a nullifier is spent, it cannot be spent again
def no_double_spend_property (s : ContractState) : Prop :=
  ∀ (n : NullifierHash),
    nullifierSpent s n →
    ∀ s' : ContractState,
      (∃ root nulls comms, transact_spec root nulls comms s s') →
      -- The spent nullifier cannot be in the new transaction's nullifiers
      ∀ nulls : List NullifierHash,
        (∃ root comms, transact_spec root nulls comms s s') →
        n ∉ nulls

-- Property: Deposits increase the leaf count
def deposit_increases_leaves (notes : List Note) (s s' : ContractState) : Prop :=
  deposit_spec notes s s' →
  notes.length > 0 →
  nextLeafIndex s' > nextLeafIndex s

-- Property: Valid historical roots remain valid
def historical_root_validity : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot),
    rootSeen s root →
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    rootSeen s' root

-- Property: Commitments are cumulative (never removed)
-- The merkle tree only grows - commitments persist forever
def commitments_cumulative : Prop :=
  ∀ (s s' : ContractState),
    (∃ notes, deposit_spec notes s s') ∨
    (∃ r nulls comms, transact_spec r nulls comms s s') →
    -- Leaf count never decreases
    nextLeafIndex s' ≥ nextLeafIndex s

-- Property: Transact respects merkle root validity
-- You can only transact using roots that were actually seen
def transact_requires_valid_root : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot) (nulls : List NullifierHash) (comms : List Commitment),
    transact_spec root nulls comms s s' →
    rootSeen s root

-- Property: Fresh nullifiers only
-- Transactions can only spend unspent nullifiers
def transact_requires_fresh_nullifiers : Prop :=
  ∀ (s s' : ContractState) (root : MerkleRoot) (nulls : List NullifierHash) (comms : List Commitment),
    transact_spec root nulls comms s s' →
    ∀ n ∈ nulls, ¬nullifierSpent s n

/-! ## Cryptographic Assumptions

The following are properties that depend on the ZK proof system's soundness
and the hash function's security. They cannot be proven from the contract
logic alone — they are trust assumptions about the cryptographic primitives.

We state them as `axiom` to be explicit: the security model relies on these.
-/

-- Abstract type for note secrets (the preimage known only to the note owner)
axiom NoteSecret : Type

-- Abstract relation: "this secret corresponds to this nullifier"
-- In practice: nullifier = PoseidonHash(secret, leafIndex, ...)
axiom secretDerivesNullifier : NoteSecret → NullifierHash → Prop

-- Abstract relation: "this secret corresponds to this commitment"
-- In practice: commitment = PoseidonHash(npk, token, amount) where npk = derive(secret)
axiom secretDerivesCommitment : NoteSecret → Commitment → Prop

-- Cryptographic assumption 1: ZK proof soundness
-- If verifyProof accepts a transaction, then the prover knows secrets
-- for each nullifier that correspond to commitments in the merkle tree.
-- This is what the Groth16/PLONK verification guarantees.
axiom zk_soundness :
  ∀ (txn : Transaction) (s s' : ContractState),
    transact_spec txn.merkleRoot txn.nullifierHashes txn.newCommitments s s' →
    ∀ nullifier ∈ txn.nullifierHashes,
      ∃ (secret : NoteSecret) (commitment : Commitment),
        secretDerivesNullifier secret nullifier ∧
        secretDerivesCommitment secret commitment
        -- (In full model: ∧ commitment is in the merkle tree at txn.merkleRoot)

-- Cryptographic assumption 2: Nullifier binding
-- Different secrets produce different nullifiers.
-- This prevents two people from accidentally (or maliciously) generating
-- the same nullifier from different notes.
axiom nullifier_binding :
  ∀ (s1 s2 : NoteSecret) (n : NullifierHash),
    secretDerivesNullifier s1 n →
    secretDerivesNullifier s2 n →
    s1 = s2

-- Note: Commitment hiding (privacy/unlinkability) is a computational assumption
-- about Poseidon hash that cannot be meaningfully stated in constructive logic.
-- It's assumed implicitly: the hash function is a secure commitment scheme.

/-! ## Derived Security Property

Exclusive withdrawal: combining the contract-level properties we proved
with the cryptographic assumptions above.
-/

-- Property: Exclusive withdrawal (contract-level part)
-- "To spend a nullifier, it must not have been spent before"
-- This is the contract enforcement half of "only I can withdraw my money."
-- The other half (only the secret holder can produce a valid ZK proof) comes
-- from zk_soundness above.
def exclusive_withdrawal : Prop :=
  ∀ (s : ContractState) (nullifier : NullifierHash),
    (∃ s' root comms, transact_spec root [nullifier] comms s s') →
    ¬nullifierSpent s nullifier

-- Combined property: exclusive withdrawal + ZK soundness
-- "To spend a nullifier, you must know the note secret AND it must be fresh"
-- This is the full user-facing guarantee but relies on the zk_soundness axiom.
def exclusive_withdrawal_full (txn : Transaction) (s s' : ContractState) : Prop :=
  transact_spec txn.merkleRoot txn.nullifierHashes txn.newCommitments s s' →
  ∀ nullifier ∈ txn.nullifierHashes,
    ¬nullifierSpent s nullifier ∧
    ∃ (secret : NoteSecret) (commitment : Commitment),
      secretDerivesNullifier secret nullifier ∧
      secretDerivesCommitment secret commitment

end DumbContracts.Specs.Unlink
