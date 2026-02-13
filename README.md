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
