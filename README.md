# Dumb Contracts

DumbContracts is a Lean 4 project for writing smart contracts in a tiny EDSL, proving their behavior in Lean, and compiling verified specs to Yul/EVM bytecode. It contains executable semantics, a compiler pipeline, and machine-checked proofs across the EDSL and IR generation, with Yul preservation proofs across all three verification layers.

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

## Contracts

| Contract | Theorems | Description |
|----------|----------|-------------|
| SimpleStorage | 20 | Store/retrieve with roundtrip proof |
| Counter | 28 | Increment/decrement with wrapping, composition proofs |
| SafeCounter | 25 | Overflow/underflow revert proofs |
| Owned | 22 | Access control and ownership transfer |
| OwnedCounter | 45 | Cross-pattern composition, lockout proofs |
| Ledger | 32 | Deposit/withdraw/transfer with balance conservation |
| SimpleToken | 56 | Mint/transfer, supply conservation, storage isolation |
| ReentrancyExample | 4 | Reentrancy vulnerability vs safe withdrawal (inline proofs) |
| CryptoHash | — | External cryptographic library linking (no specs, no tests) |

**Verification snapshot**: 296 theorems across 9 categories, 207 covered by property tests (70% coverage), 89 proof-only exclusions. 5 documented axioms, 12 `sorry` in Ledger sum proofs ([#65](https://github.com/Th0rgal/dumbcontracts/issues/65)). 290 Foundry tests across 23 test suites.

## What's Verified

- **EDSL correctness**: Each contract satisfies its specification in Lean (Layer 1).
- **Compiler correctness**: IR generation preserves ContractSpec semantics (Layer 2). Yul codegen preserves IR semantics (Layer 3).
- **End-to-end pipeline**: EDSL → ContractSpec → IR → Yul fully verified with 5 axioms.
- **Trust boundary**: Yul → EVM bytecode via solc (validated by 70k+ differential tests).

See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for detailed trust boundaries, [`AXIOMS.md`](AXIOMS.md) for axiom documentation, and [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for full status.

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

Use the scaffold generator to create all boilerplate files:
```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

**File Layout (Spec → Impl → Proof):**
1. **Spec**: `DumbContracts/Specs/<Name>/Spec.lean` — Human-readable function specifications
2. **Invariants**: `DumbContracts/Specs/<Name>/Invariants.lean` — State properties (optional but encouraged)
3. **Implementation**: `DumbContracts/Examples/<Name>.lean` — EDSL contract code
4. **EDSL Proofs**: `DumbContracts/Specs/<Name>/Proofs.lean` — Layer 1 correctness proofs
5. **Compiler Spec**: `Compiler/Specs.lean` — ContractSpec for code generation
6. **Tests**: `test/Property<Name>.t.sol` + differential tests

**Documentation Checklist:**
After adding a contract, update these files to keep counts in sync:
- `test/property_manifest.json` — Run `python3 scripts/extract_property_manifest.py`
- Contracts table in this README
- `docs/VERIFICATION_STATUS.md` — Contract table and coverage stats
- `docs-site/public/llms.txt` — Quick Facts and theorem breakdown

**Common Pitfalls:**
- Storage slot mismatches between spec, EDSL, and compiler
- Mapping conversions assuming simple slots instead of typed storage
- Stale proofs when specs change

**Reference**: Use `SimpleStorage` as the minimal end-to-end example (full spec pipeline). Use `ReentrancyExample` as a reference for proof-only contracts (inline theorems, no compiler spec).

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
# Defaults: DIFFTEST_RANDOM_SMALL=100, DIFFTEST_RANDOM_LARGE=10000, DIFFTEST_RANDOM_SEED=42
# Override with DIFFTEST_RANDOM_COUNT or scale individually:
DIFFTEST_RANDOM_SMALL=200 DIFFTEST_RANDOM_LARGE=20000 DIFFTEST_RANDOM_SEED=42 forge test

# Test with multiple seeds to detect flakiness:
./scripts/test_multiple_seeds.sh              # Test with 7 default seeds
./scripts/test_multiple_seeds.sh 1 2 3 4 5    # Test with custom seeds
```

**Validation Checks:**
```bash
python3 scripts/check_property_manifest.py       # Verify test tags reference real theorems
python3 scripts/check_property_coverage.py       # Ensure all theorems have tests
python3 scripts/check_property_manifest_sync.py  # Verify manifest matches proofs
python3 scripts/check_selectors.py               # Verify keccak256 selector hashing
python3 scripts/check_storage_layout.py          # Verify storage slot consistency across layers
python3 scripts/check_contract_structure.py      # Verify contract file structure is complete
python3 scripts/check_doc_counts.py              # Verify documentation counts match codebase
```

## Documentation

- `Compiler/Proofs/README.md` — Proof structure and navigation
- `docs-site/` — Documentation website (MDX)
- Roadmap, milestones, and progress updates: `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`

## License

MIT
