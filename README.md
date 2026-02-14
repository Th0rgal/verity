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

## What's Verified

- **EDSL correctness**: Each example contract satisfies its specification in Lean.
- **Spec semantics**: ContractSpec execution matches the intended DSL behavior.
- **Compiler correctness**: IR generation and Yul codegen fully proven (Layers 1-3 complete).
- **Automation**: Common proof patterns are captured in reusable lemmas.

See [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for detailed verification status and [`Compiler/Proofs/README.md`](Compiler/Proofs/README.md) for proof inventory.

## Trust Model

See [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for detailed trust assumptions and semantics definitions.

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

## Adding a Contract

**File Layout (Spec → Impl → Proof):**
1. **Spec**: `DumbContracts/Specs/<Name>/Spec.lean` — Human-readable function specifications
2. **Invariants**: `DumbContracts/Specs/<Name>/Invariants.lean` — State properties (optional but encouraged)
3. **Implementation**: `DumbContracts/Examples/<Name>.lean` — EDSL contract code
4. **EDSL Proofs**: `DumbContracts/Specs/<Name>/Proofs.lean` — Layer 1 correctness proofs
5. **Compiler Spec**: `Compiler/Specs.lean` — ContractSpec for code generation
6. **Tests**: `test/Property<Name>.t.sol` + differential tests

**Common Pitfalls:**
- Storage slot mismatches between spec, EDSL, and compiler
- Mapping conversions assuming simple slots instead of typed storage
- Stale proofs when specs change

**Reference**: Use `SimpleStorage` as the minimal end-to-end example.

**Infrastructure:**
- **Proof automation**: `DumbContracts/Proofs/Stdlib/` (SpecInterpreter + automation lemmas)
- **Compiler proofs**: `Compiler/Proofs/` (Layer 2: IR generation, Layer 3: Yul preservation)

## Build and Test

**Basic Commands:**
```bash
lake build                          # Type-check Lean code (EDSL + proofs)
lake build dumbcontracts-compiler   # Build compiler executable
forge test                          # Run all Foundry tests
```

**Differential Testing (optional scaling):**
```bash
# Defaults: DIFFTEST_RANDOM_SMALL=100, DIFFTEST_RANDOM_LARGE=10000
# Override with DIFFTEST_RANDOM_COUNT or scale individually:
DIFFTEST_RANDOM_SMALL=200 DIFFTEST_RANDOM_LARGE=20000 DIFFTEST_RANDOM_SEED=42 forge test
```

**Property Coverage Checks:**
```bash
python3 scripts/check_property_manifest.py       # Verify test tags reference real theorems
python3 scripts/check_property_coverage.py       # Ensure all theorems have tests
python3 scripts/check_property_manifest_sync.py  # Verify manifest matches proofs
python3 scripts/check_selectors.py               # Verify keccak256 selector hashing
```

## Documentation

- `Compiler/Proofs/README.md` — Proof structure and navigation
- `docs-site/` — Documentation website (MDX)
- Roadmap, milestones, and progress updates: `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`

## License

MIT
