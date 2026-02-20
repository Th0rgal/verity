<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>Formally verified smart contracts. From spec to bytecode.</strong><br>
  <em>Write simple rules. Let agents implement. Math proves the rest.</em>
</p>

<p align="center">
  <a href="https://github.com/Th0rgal/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/theorems-401-brightgreen.svg" alt="401 Theorems"></a>
  <a href="https://github.com/Th0rgal/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/Th0rgal/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

## 5-Minute Quick Start

```bash
# 1. Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env

# 2. Clone and build
git clone https://github.com/Th0rgal/verity.git
cd verity
lake build                                    # Verifies all 431 theorems

# 3. Generate a new contract
python3 scripts/generate_contract.py MyContract

# 4. Compile to Yul/EVM
lake build verity-compiler
lake exe verity-compiler                      # Output in compiler/yul/
```

**With external libraries (e.g., Poseidon hash):**
```bash
# Link your Yul library at compile time
lake exe verity-compiler --link examples/external-libs/MyLib.yul -o compiler/yul
```

**With deterministic Yul patch pass + coverage report:**
```bash
lake exe verity-compiler \
  --enable-patches \
  --patch-max-iterations 2 \
  --patch-report compiler/patch-report.tsv \
  -o compiler/yul-patched
```

**Run tests:**
```bash
FOUNDRY_PROFILE=difftest forge test           # 375 tests across 32 suites
```

---

Verity is a Lean 4 framework that lets you write smart contracts in a domain-specific language, formally verify their correctness, and compile them to EVM bytecode.

**The idea is simple:** humans review 10-line specs that are easy to audit. Agents write 1000-line implementations. Lean proves the implementation matches the spec - no trust required.

## How It Works

```lean
-- 1. Write a spec (human-readable, ~10 lines)
def store_spec (value : Uint256) (s s' : ContractState) : Prop :=
  s'.storage 0 = value ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'

-- 2. Write an implementation
def store (value : Uint256) : Contract Unit := do
  setStorage storedData value

-- 3. Prove correctness - math guarantees the match
theorem store_meets_spec (s : ContractState) (value : Uint256) :
  store_spec value s (((store value).run s).snd) := by
  simp [store, store_spec, storedData, setStorage, storageUnchangedExcept, sameAddrMapContext]
```

One spec can have many competing implementations - naive, gas-optimized, packed storage - all proven correct against the same rules.

## Verified Contracts

| Contract | Theorems | Description |
|----------|----------|-------------|
| SimpleStorage | 20 | Store/retrieve with roundtrip proof |
| Counter | 28 | Increment/decrement with wrapping, composition proofs |
| SafeCounter | 25 | Overflow/underflow revert proofs |
| Owned | 23 | Access control and ownership transfer |
| OwnedCounter | 48 | Cross-pattern composition, lockout proofs |
| Ledger | 33 | Deposit/withdraw/transfer with balance conservation |
| SimpleToken | 61 | Mint/transfer, supply conservation, storage isolation |
| ERC20 | 19 | Foundation scaffold with initial spec/read-state proofs |
| ERC721 | 11 | Foundation scaffold with token ownership/approval proof baseline |
| ReentrancyExample | 4 | Reentrancy vulnerability vs safe withdrawal |

**Unverified examples**:
- [CryptoHash](Verity/Examples/CryptoHash.lean) demonstrates external library linking via the [Linker](Compiler/Linker.lean) but has no specs or proofs.
- [ERC20](Verity/Examples/ERC20.lean) is a new foundation scaffold with executable logic plus formal spec/invariant modules in `Verity/Specs/ERC20/`, with proof development tracked in [#69](https://github.com/Th0rgal/verity/issues/69).
- [ERC721](Verity/Examples/ERC721.lean) is a new foundation scaffold with executable logic plus formal spec/invariant modules in `Verity/Specs/ERC721/`, with proof development tracked in [#73](https://github.com/Th0rgal/verity/issues/73).

### Using External Libraries (Linker)

Verity supports linking external Yul libraries (e.g., cryptographic libraries) to your verified contracts. Prove your contract logic with simple placeholders, then swap in production implementations at compile time.

**The pattern:**
1. Write a simple Lean placeholder (e.g., `add a b` for a hash function)
2. Add an `externalCall` in your ContractSpec 
3. Link your production Yul library at compile time

```bash
# Compile with external libraries
lake exe verity-compiler \
    --link examples/external-libs/PoseidonT3.yul \
    --link examples/external-libs/PoseidonT4.yul \
    -o compiler/yul
```

**Minimal example:**

```lean
-- 1. Lean placeholder (for proofs)
def myHash (a b : Uint256) : Contract Uint256 := do
  return (a + b)  -- simple placeholder

-- 2. ContractSpec calls the real library
Stmt.letVar "h" (Expr.externalCall "myHash" [Expr.param "a", Expr.param "b"])

-- 3. Compile with: lake exe verity-compiler --link examples/external-libs/MyHash.yul
```

See [`examples/external-libs/README.md`](examples/external-libs/README.md) for a step-by-step guide and [`docs-site/content/guides/linking-libraries.mdx`](docs-site/content/guides/linking-libraries.mdx) for the full documentation.

431 theorems across 11 categories, all fully proven. 381 Foundry tests across 35 test suites. 250 covered by property tests (58% coverage, 181 proof-only exclusions). 1 documented axioms. 0 `sorry` — Ledger sum proofs completed in Conservation.lean ([#65](https://github.com/Th0rgal/verity/issues/65)).

## What's Verified

- **EDSL correctness** - each contract satisfies its spec in Lean (Layer 1)
- **Compiler correctness** - IR generation preserves semantics (Layer 2), Yul codegen preserves IR (Layer 3)
- **End-to-end pipeline** - EDSL -> ContractSpec -> IR -> Yul, fully verified with 1 axioms
- **Trust boundary** - Yul -> EVM bytecode via solc (validated by 70k+ differential tests)

See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for trust boundaries, [`AXIOMS.md`](AXIOMS.md) for axiom documentation, and [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for full status.

## Getting Started

<details>
<summary><strong>Building</strong></summary>

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env

# Build the project
lake build

# Build and run the compiler
lake build verity-compiler
lake exe verity-compiler

# Run Foundry tests (requires difftest profile for FFI access)
FOUNDRY_PROFILE=difftest forge test
```

</details>

<details>
<summary><strong>Testing</strong></summary>

**Foundry tests** (381 tests) validate EDSL = Yul = EVM execution:

```bash
FOUNDRY_PROFILE=difftest forge test                                          # run all
FOUNDRY_PROFILE=difftest forge test -vvv                                     # verbose
FOUNDRY_PROFILE=difftest forge test --match-path test/PropertyCounter.t.sol  # specific file
```

> **Note**: Tests require `FOUNDRY_PROFILE=difftest` because they compile Yul via `solc` using `vm.ffi()`. The default profile has FFI disabled for security. See [foundry.toml](foundry.toml).

**Differential tests** compare EDSL interpreter output against Solidity-compiled EVM to catch compiler bugs. See [`test/README.md`](test/README.md).

</details>

<details>
<summary><strong>Adding a contract</strong></summary>

```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

This scaffolds the full file layout:

1. **Implementation** - `Verity/Examples/<Name>.lean`
2. **Spec** - `Verity/Specs/<Name>/Spec.lean`
3. **Invariants** - `Verity/Specs/<Name>/Invariants.lean`
4. **Layer 2 Proof Re-export** - `Verity/Specs/<Name>/Proofs.lean`
5. **Basic Proofs** - `Verity/Proofs/<Name>/Basic.lean`
6. **Correctness Proofs** - `Verity/Proofs/<Name>/Correctness.lean`
7. **Tests** - `test/Property<Name>.t.sol`

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for conventions and workflow.

</details>

<details>
<summary><strong>Linking external libraries</strong></summary>

Use the Linker to integrate production cryptographic libraries (Poseidon, Groth16, etc.) with formally verified contract logic:

1. **Write a placeholder** in your Lean contract:
```lean
-- Placeholder: simple addition for proofs
def hash (a b : Uint256) : Contract Uint256 := do
  return add a b
```

2. **Add external call** in `Compiler/Specs.lean`:
```lean
Stmt.letVar "h" (Expr.externalCall "poseidonHash" [Expr.param "a", Expr.param "b"])
```

3. **Compile with linking**:
```bash
lake exe verity-compiler --link examples/external-libs/MyHash.yul -o compiler/yul
```

The compiler validates function names, arities, and prevents name collisions. See [`examples/external-libs/README.md`](examples/external-libs/README.md) for detailed guidance.

</details>

## Documentation

**Full documentation**: [verity.thomasm.ar](https://verity.thomasm.ar/) — guides, DSL reference, examples, and verification details.

| | |
|---|---|
| [Docs Site](https://verity.thomasm.ar/) | Full documentation site with guides and DSL reference |
| [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) | What's verified, what's trusted, trust reduction roadmap |
| [`AXIOMS.md`](AXIOMS.md) | All axioms with soundness justifications (1 remaining) |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Coding conventions, workflow, PR guidelines |
| [`docs/ROADMAP.md`](docs/ROADMAP.md) | Verification progress, planned features |
| [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) | Per-theorem status |

## License

MIT - See [LICENSE.md](LICENSE.md) for details.
