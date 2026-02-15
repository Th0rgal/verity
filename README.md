# Verity

**Verity** is a Lean 4 framework enabling developers to write smart contracts in a domain-specific language, formally verify their correctness, and compile them to EVM bytecode.

The philosophy: focus on simple rules, easy to understand and trust for humans, while leaving implementation up to agentic developers. Thanks to formal verification, the code is mathematically guaranteed to match the specs, which don't require any understanding of algorithmics.

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
Here is the SimpleStorage spec from `Verity/Specs/SimpleStorage/Spec.lean`:

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

## Vision: Built for the Agentic Era

Verity enables **separation of concerns** for trustless agentic development:

- **Humans write specs**, simple, auditable rules (10 lines)
- **Agents write implementations**, complex, optimized code (1000 lines)
- **Math proves correctness**, no trust required

### One Spec, Many Implementations

```lean
-- Human audits once:
def transfer_spec : Spec Bool := ...

-- Agents compete on implementations:
def transfer_v1 : Contract Bool := ... // naive
def transfer_v2 : Contract Bool := ... // gas-optimized
def transfer_v3 : Contract Bool := ... // packed storage

// All proven correct:
theorem v1_correct : semantics transfer_v1 = transfer_spec
theorem v2_correct : semantics transfer_v2 = transfer_spec
theorem v3_correct : semantics transfer_v3 = transfer_spec
```

### Verified Intent Over Trusted Code

- **Traditional**: "Can we trust this code?" (audit 1000 lines)
- **Verity**: "Can we trust this spec?" (audit 10 lines, math proves the rest)

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

**Verification snapshot**: 296 theorems across 9 categories, 216 covered by property tests (73% coverage), 80 proof-only exclusions. 5 documented axioms, 12 `sorry` in Ledger sum proofs ([#65](https://github.com/Th0rgal/verity/issues/65)). 299 Foundry tests across 23 test suites.

## What's Verified

- **EDSL correctness**: Each contract satisfies its specification in Lean (Layer 1).
- **Compiler correctness**: IR generation preserves ContractSpec semantics (Layer 2). Yul codegen preserves IR semantics (Layer 3).
- **End-to-end pipeline**: EDSL → ContractSpec → IR → Yul fully verified with 5 axioms.
- **Trust boundary**: Yul → EVM bytecode via solc (validated by 70k+ differential tests).

See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for detailed trust boundaries, [`AXIOMS.md`](AXIOMS.md) for axiom documentation, and [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for full status.

## Repository Structure

```
Verity/                              # EDSL core + stdlib + examples/specs/proofs
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

**File Layout (Spec, Impl, Proof):**
1. **Spec**: `Verity/Specs/<Name>/Spec.lean`, human-readable function specifications
2. **Invariants**: `Verity/Specs/<Name>/Invariants.lean`, state properties (optional but encouraged)
3. **Implementation**: `Verity/Examples/<Name>.lean`, EDSL contract code
4. **EDSL Proofs**: `Verity/Specs/<Name>/Proofs.lean`, Layer 1 correctness proofs
5. **Compiler Spec**: `Compiler/Specs.lean`, ContractSpec for code generation
6. **Tests**: `test/Property<Name>.t.sol` + differential tests

**Post-generation**: Fill in spec bodies, implement contract, write proofs, add properties. See [`CONTRIBUTING.md`](CONTRIBUTING.md).

## Building

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# Build the project
lake build

# Build the compiler binary
lake build verity-compiler

# Generate Yul from Lean contracts
lake exe verity-compiler

# Run Foundry tests (requires foundry)
forge test
```

## Testing

**Property Testing**: 290 tests across 23 test suites validate EDSL ≡ Yul ≡ EVM execution.

```bash
# Run property tests
forge test

# Run with verbosity
forge test -vvv

# Run specific test file
forge test --match-path test/PropertyCounter.t.sol
```

**Differential Testing**: Tests compare EDSL interpreter output against Solidity-compiled EVM execution to catch compiler bugs.

See [`test/README.md`](test/README.md) for details.

## Documentation

- [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md), what's verified, what's trusted, trust reduction roadmap
- [`AXIOMS.md`](AXIOMS.md), all 5 axioms with soundness justifications
- [`CONTRIBUTING.md`](CONTRIBUTING.md), coding conventions, workflow, PR guidelines
- [`docs/ROADMAP.md`](docs/ROADMAP.md), verification progress, planned features
- [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md), per-theorem status
- [`docs-site/`](docs-site/), full documentation site

## Philosophy: "Dumb Contracts"

The name **"dumb contracts"** captures our approach: write contracts so simple they can't be wrong.

- **Simple specs**, no algorithmic knowledge required
- **Human auditable**, trust the rules, not the implementation
- **Mathematically proven**, correctness guaranteed by Lean

In the agentic era, agents will write most code. Verity ensures their implementations are trustworthy by default.

## License

MIT License - See [LICENSE](LICENSE) file for details.
