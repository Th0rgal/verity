# Dumb Contracts

DumbContracts is a Lean 4 project for writing smart contracts in a tiny EDSL, proving their behavior in Lean, and compiling verified specs to Yul/EVM bytecode. It contains executable semantics, a compiler pipeline, and machine-checked proofs across the EDSL and IR generation, with Yul preservation proofs in progress.

## Example

```lean
-- Implementation
def storedData : StorageSlot Uint256 := ⟨0⟩

def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

def retrieve : Contract Uint256 := do
  getStorage storedData

-- Proof: retrieve returns what store stored
theorem store_retrieve_correct (s : ContractState) (value : Uint256) :
  let s' := ((store value).run s).snd
  let result := ((retrieve).run s').fst
  result = value := by
  have h_store := store_meets_spec s value
  have h_retrieve := retrieve_meets_spec ((store value).run s |>.2)
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]
```

## Spec Example (Human-Friendly Rules)

Specs are small, readable rules about what a function must do.
Here is the SimpleStorage spec from `DumbContracts/Specs/SimpleStorage/Spec.lean`:

```lean
-- store updates slot 0, keeps everything else unchanged
def store_spec (value : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 0 = value ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

-- retrieve returns slot 0
def retrieve_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0
```

## What’s Verified

- **EDSL correctness**: Each example contract satisfies its specification in Lean.
- **Spec semantics**: ContractSpec execution matches the intended DSL behavior.
- **Compiler correctness**: IR generation is proven; Yul codegen proofs are in progress (semantics + scaffolding in place).
- **Automation**: Common proof patterns are captured in reusable lemmas.

See `Compiler/Proofs/README.md` for the proof inventory and layout across layers.

## Assumptions and Trust Model

These are the remaining trusted components outside Lean:

- **`solc` Yul compiler**: The Solidity compiler is trusted to compile Yul to EVM bytecode (CI now compiles generated Yul as a sanity check).
- **EVM semantics**: The EVM execution model is assumed to match the specification used in proofs.
- **Function selectors**: Precomputed `keccak256` hashes in `Compiler/Selector.lean` are assumed correct (CI checks fixtures against `solc --hashes`).

Semantics are defined in Lean here:

- EDSL semantics: `DumbContracts/Core.lean`
- Spec semantics: `DumbContracts/Proofs/Stdlib/SpecInterpreter.lean`
- IR semantics: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- Yul semantics: `Compiler/Proofs/YulGeneration/Semantics.lean`

## Repository Structure

```
DumbContracts/                       # EDSL core + stdlib + examples/specs/proofs
Compiler/                            # Compiler (spec DSL, IR, codegen, selector, Yul AST)
Compiler/Proofs/                     # Compiler correctness proofs (3 layers)
compiler/                            # Generated Yul output + fixtures (used in tests/docs)
docs/                                # Design notes and verification summaries
docs-site/                           # Documentation site (MDX)
examples/solidity/                   # Solidity/Yul fixtures and test outputs
scripts/                             # build/test scripts
test/                                # Foundry tests (unit, property, differential)
```

## Where Things Live (Spec → Impl → Proof)

- **User-facing specs**: `DumbContracts/Specs/<Name>/Spec.lean` (+ `Invariants.lean`)
- **Implementations (EDSL)**: `DumbContracts/Examples/<Name>.lean`
- **User-facing proofs**: `DumbContracts/Specs/<Name>/Proofs.lean`
- **Reusable proof infrastructure**: `DumbContracts/Proofs/Stdlib/` (spec interpreter + automation)
- **Compiler specs (for codegen)**: `Compiler/Specs.lean` (separate from user specs)
- **Compiler proofs**: `Compiler/Proofs/` (IR generation + Yul preservation)

## Adding a Contract (Checklist)

1. Write a small, human-readable spec in `DumbContracts/Specs/<Name>/Spec.lean`.
2. Add invariants in `DumbContracts/Specs/<Name>/Invariants.lean` (optional but encouraged).
3. Implement the contract in `DumbContracts/Examples/<Name>.lean` using the EDSL.
4. Prove the implementation meets the spec in `DumbContracts/Specs/<Name>/Proofs.lean`.
5. Add compiler-level spec glue in `Compiler/Specs.lean` and IR/Yul proofs in `Compiler/Proofs/` if new patterns are introduced.
6. Add tests in `test/` (unit + property + differential if applicable).
7. Use `SimpleStorage` as the minimal end-to-end reference for file layout and proof style.

## Adding a Contract (Common Pitfalls)

- Storage slot mismatches between the spec, EDSL implementation, and compiler spec.
- Mapping conversions that assume simple storage slots instead of typed storage.
- Missing proofs when a spec is changed but the EDSL implementation or invariants are not updated.

## Examples and Proofs

- **Lean examples (EDSL implementations)**: `DumbContracts/Examples/`
- **Specifications + invariants + Layer 1 proofs**: `DumbContracts/Specs/`
- **Contract-level proofs (EDSL properties)**: `DumbContracts/Proofs/`
- **Compiler proofs**: `Compiler/Proofs/` (Layer 1 infra, Layer 2: IR, Layer 3: Yul)

## Unlink Privacy Protocol (Formal Verification)

The [Unlink privacy protocol](https://github.com/Th0rgal/unlink-contracts) is a ZK-SNARK based mixer (deposit, private transfer, anonymous withdrawal) implemented in Solidity. This project contains a complete Lean rewrite using the EDSL, formal specifications of its security properties, and machine-checked proofs that the implementation satisfies the specs. All theorems are proven with zero `sorry`.

### Solidity vs Lean — File Mapping

| Solidity (unlink-contracts) | Lean (this repo) | What it does |
|---|---|---|
| `src/lib/Models.sol` | `DumbContracts/Specs/Unlink/Types.lean` | `Note`, `Commitment`, `NullifierHash`, `MerkleRoot` |
| `src/lib/State.sol` | `DumbContracts/Examples/Unlink/UnlinkPool.lean` (storage slots) | Storage layout: slots 0-4, nullifier/root mappings |
| `src/lib/Logic.sol` | `DumbContracts/Examples/Unlink/UnlinkPool.lean` (functions) | `deposit`, `transact`, `insertLeaves`, `hashNote`, etc. |
| `src/UnlinkPool.sol` | `DumbContracts/Examples/Unlink/UnlinkPool.lean` | Entry points: `deposit`, `transact`, view functions |
| _(no equivalent)_ | `DumbContracts/Specs/Unlink/Spec.lean` | Formal specification: what each function must do |
| _(no equivalent)_ | `DumbContracts/Specs/Unlink/Proofs.lean` | Security property proofs |
| _(no equivalent)_ | `DumbContracts/Proofs/Unlink/Basic.lean` | `insertLeaves` correctness proofs |
| _(no equivalent)_ | `DumbContracts/Proofs/Unlink/Correctness.lean` | `deposit_meets_spec` proof |
| _(no equivalent)_ | `DumbContracts/Proofs/Unlink/TransactCorrectness.lean` | `transact_meets_spec` proof |
| _(no equivalent)_ | `DumbContracts/Specs/Unlink/Arithmetic.lean` | Uint256 arithmetic lemmas |

### Specifications (What Each Function Must Do)

Defined in `Specs/Unlink/Spec.lean`. These are the rules the implementation is proven to satisfy.

**`deposit_spec`** — 6 conjuncts:
1. Merkle root changes
2. New root is marked as seen
3. Leaf index increases by the number of notes
4. Previously-spent nullifiers remain spent
5. Previously-seen roots remain seen
6. Context (sender, address, value, timestamp) is preserved

**`transact_spec`** — 10 conjuncts:
1. Merkle root was previously seen
2. All input nullifiers were fresh (unspent)
3. All input nullifiers are now spent
4. Merkle root changes
5. New root is marked as seen
6. Leaf index increases by the number of new commitments
7. Previously-seen roots remain seen
8. Previously-spent nullifiers remain spent
9. Context is preserved
10. If withdrawal amount > 0, the withdrawal commitment equals the last output commitment

### Cryptographic Assumptions

These are stated as axioms (they model the ZK proof system, not the contract logic):

| Axiom | What it says |
|---|---|
| `zk_soundness` | If a transaction is accepted, the prover knows a secret and commitment for each nullifier |
| `nullifier_binding` | Different secrets produce different nullifiers (collision resistance) |

### Proven Theorems

All proofs are machine-checked (zero `sorry`). Grouped by file:

**Spec-level security (`Specs/Unlink/Spec.lean`)** — 3 theorems:
- `no_double_spend_monotonic` — once spent, a nullifier stays spent across any operation
- `roots_cumulative` — historical roots remain valid across any operation
- `leaf_index_monotonic` — leaf index never decreases

**Security properties (`Specs/Unlink/Proofs.lean`)** — 14 theorems:
- `valid_deposit_implies_positive_amounts` — deposit validation implies positive note amounts
- `valid_transact_implies_has_inputs` — transact validation implies non-empty nullifiers
- `valid_transact_implies_has_commitments` — transact validation implies non-empty commitments
- `valid_transact_withdrawal_implies_valid_recipient` — non-zero withdrawal requires non-zero recipient
- `deposit_preserves_nullifiers` — deposits don't clear nullifiers
- `roots_preserved_general` — any operation preserves historical roots
- `deposit_changes_root` — deposits change the merkle root
- `transact_changes_root` — transactions change the merkle root
- `historical_root_validity_holds` — valid roots remain valid forever
- `deposit_increases_leaves_holds` — deposits grow the merkle tree
- `no_double_spend_property_holds` — spent nullifier can't appear in future transaction inputs
- `commitments_cumulative_holds` — the merkle tree only grows
- `transact_requires_valid_root_holds` — transactions require a previously-seen root
- `transact_requires_fresh_nullifiers_holds` — transactions can only spend unspent nullifiers
- `exclusive_withdrawal_holds` — to spend a nullifier, it must be unspent
- `exclusive_withdrawal_full_holds` — combines contract enforcement with ZK soundness: to spend a nullifier, it must be fresh AND the prover must know the secret
- `withdrawal_commitment_coherence_holds` — withdrawal commitment matches last output commitment

**`insertLeaves` building blocks (`Proofs/Unlink/Basic.lean`)** — 15 theorems:
- `insertLeaves_updates_root` — slot 1 gets `oldRoot + commitments.length`
- `insertLeaves_marks_root_seen` — new root's seen-slot is set to 1
- `insertLeaves_updates_leaf_index` — slot 0 gets `oldIndex + commitments.length`
- `insertLeaves_preserves_slot` — all other slots unchanged
- `insertLeaves_preserves_context` — context preserved
- `insertLeaves_succeeds` — always returns `success`
- `insertLeaves_root_changes` — new root differs from old (non-empty list)
- `insertLeaves_new_root_seen` — new root satisfies `rootSeen` predicate
- `insertLeaves_leaf_index_updated` — leaf index incremented correctly
- `insertLeaves_preserves_nullifiers` — nullifier spent status unchanged
- `insertLeaves_preserves_roots` — previously-seen roots remain seen

**Deposit correctness (`Proofs/Unlink/Correctness.lean`)** — 7 theorems:
- `hashNote_eq` — `hashNote` computes `npk + token + amount` without modifying state
- `computeCommitments_spec` — preserves state, output list has same length as input
- `validateNotes_spec` — preserves state when all note amounts are positive
- `deposit_reduces` — deposit is equivalent to `insertLeaves` on commitments
- `deposit_succeeds` — deposit doesn't revert when preconditions hold
- **`deposit_meets_spec`** — the deposit implementation satisfies all 6 conjuncts of `deposit_spec`

**Transact correctness (`Proofs/Unlink/TransactCorrectness.lean`)** — 15 theorems:
- `isRootSeen_spec`, `isRootSeen_true` — root-seen check characterization
- `verifyProof_spec` — proof verification characterization
- `isNullifierSpent_spec` — nullifier-spent check characterization
- `checkNullifiersUnspent_spec` — recursive nullifier check
- `markNullifierSpent_spec` — single nullifier state effect
- `markNullifiersSpent_succeeds` — recursive marking always succeeds
- `markNullifiersSpent_preserves_one` — slots with value 1 stay at 1
- `markNullifiersSpent_sets_slots` — each nullifier slot is set to 1
- `markNullifiersSpent_preserves_other_slots` — unrelated slots unchanged
- `markNullifiersSpent_preserves_context` — context preserved
- `markNullifiersSpent_preserves_spent` — already-spent nullifiers remain spent
- `markNullifiersSpent_preserves_rootSeen` — root-seen slots preserved
- **`transact_meets_spec`** — the transact implementation satisfies all 10 conjuncts of `transact_spec`

**Arithmetic (`Specs/Unlink/Arithmetic.lean`)** — 7 theorems:
- `add_pos_gt`, `add_length_gt`, `eq_add_pos_implies_gt`, `gt_irrefl`, `gt_implies_ne`, `add_nat_ge`, `eq_add_implies_ge`

### Scaffolded Components

These parts are placeholders — the proofs are valid for the scaffolded behavior, but the scaffolds don't model full cryptographic operations:

- **`hashNote`**: returns `npk + token + amount` (real: Poseidon hash)
- **`verifyProof`**: returns `true` (real: ZK-SNARK verification via verifier router)
- **`insertLeaves`**: updates root as `oldRoot + commitments.length` (real: incremental Merkle tree)
- **Token transfers**: not modeled (real: ERC20 `transferFrom` / ETH handling)

### Reading the Proofs

Start with `Spec.lean` to understand what's being claimed, then check the corresponding proof file:

```
Spec.lean          →  "deposit must change the root, mark it seen, ..."
Correctness.lean   →  "running deposit on this state produces a state satisfying deposit_spec"
```

The main theorems to look at are `deposit_meets_spec` and `transact_meets_spec` — everything else is a building block for these two.

## Build and Test

```bash
# Type-check DumbContracts (EDSL + proofs)
lake build

# Build compiler executable
lake build dumbcontracts-compiler

# Run Foundry tests (unit + property + differential + selector sanity)
forge test

# Optional: scale differential random test counts
# DIFFTEST_RANDOM_SMALL defaults to 100, DIFFTEST_RANDOM_LARGE defaults to 10000
# DIFFTEST_RANDOM_COUNT overrides both small/large when set
# Large counts can be expensive; tune these for local runs vs CI.
# CI runs with DIFFTEST_RANDOM_LARGE=10000 across all differential harnesses.
# CI builds the compiler + difftest interpreter once and shares generated Yul across test shards.
# CI shards download a prebuilt difftest interpreter artifact and run it directly (must be executable).
# DIFFTEST_RANDOM_SEED is mixed with shard index + contract label to avoid identical sequences across shards.
DIFFTEST_RANDOM_SMALL=200 DIFFTEST_RANDOM_LARGE=20000 DIFFTEST_RANDOM_SEED=42 forge test

# Optional: extract proof theorem names into a test manifest
python3 scripts/extract_property_manifest.py

# Optional: check that property tests reference real theorems
python3 scripts/check_property_manifest.py

# Optional: check that property_manifest.json matches current proofs
python3 scripts/check_property_manifest_sync.py

# Optional: check that all theorems have property coverage (with exclusions)
python3 scripts/check_property_coverage.py

# Optional: check selector hashing against specs and generated Yul (including yul-new if present)
python3 scripts/check_selectors.py
```

## Documentation

- `Compiler/Proofs/README.md` — Proof structure and navigation
- `docs-site/` — Documentation website (MDX)
- Roadmap, milestones, and progress updates: `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`

## License

MIT
