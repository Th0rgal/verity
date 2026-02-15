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
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/theorems-296-brightgreen.svg" alt="296 Theorems"></a>
  <a href="https://github.com/Th0rgal/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/Th0rgal/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

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
| Owned | 22 | Access control and ownership transfer |
| OwnedCounter | 45 | Cross-pattern composition, lockout proofs |
| Ledger | 32 | Deposit/withdraw/transfer with balance conservation |
| SimpleToken | 56 | Mint/transfer, supply conservation, storage isolation |
| ReentrancyExample | 4 | Reentrancy vulnerability vs safe withdrawal |
| CryptoHash | - | External cryptographic library linking |

296 theorems across 9 categories. 299 Foundry tests across 23 test suites. 216 covered by property tests (73% coverage, 80 proof-only exclusions). 5 documented axioms, 12 `sorry` in Ledger sum proofs ([#65](https://github.com/Th0rgal/verity/issues/65)).

## What's Verified

- **EDSL correctness** - each contract satisfies its spec in Lean (Layer 1)
- **Compiler correctness** - IR generation preserves semantics (Layer 2), Yul codegen preserves IR (Layer 3)
- **End-to-end pipeline** - EDSL -> ContractSpec -> IR -> Yul, fully verified with 5 axioms
- **Trust boundary** - Yul -> EVM bytecode via solc (validated by 70k+ differential tests)

See [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) for trust boundaries, [`AXIOMS.md`](AXIOMS.md) for axiom documentation, and [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) for full status.

## Getting Started

<details>
<summary><strong>Building</strong></summary>

```bash
# Install Lean 4 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile

# Build the project
lake build

# Build and run the compiler
lake build verity-compiler
lake exe verity-compiler

# Run Foundry tests
forge test
```

</details>

<details>
<summary><strong>Testing</strong></summary>

**Property tests** (299 tests) validate EDSL = Yul = EVM execution:

```bash
forge test                                          # run all
forge test -vvv                                     # verbose
forge test --match-path test/PropertyCounter.t.sol  # specific file
```

**Differential tests** compare EDSL interpreter output against Solidity-compiled EVM to catch compiler bugs. See [`test/README.md`](test/README.md).

</details>

<details>
<summary><strong>Adding a contract</strong></summary>

```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

This scaffolds the full file layout:

1. **Spec** - `Verity/Specs/<Name>/Spec.lean`
2. **Invariants** - `Verity/Specs/<Name>/Invariants.lean`
3. **Implementation** - `Verity/Examples/<Name>.lean`
4. **Proofs** - `Verity/Specs/<Name>/Proofs.lean`
5. **Compiler Spec** - `Compiler/Specs.lean`
6. **Tests** - `test/Property<Name>.t.sol`

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for conventions and workflow.

</details>

## Documentation

| | |
|---|---|
| [`TRUST_ASSUMPTIONS.md`](TRUST_ASSUMPTIONS.md) | What's verified, what's trusted, trust reduction roadmap |
| [`AXIOMS.md`](AXIOMS.md) | All 5 axioms with soundness justifications |
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | Coding conventions, workflow, PR guidelines |
| [`docs/ROADMAP.md`](docs/ROADMAP.md) | Verification progress, planned features |
| [`docs/VERIFICATION_STATUS.md`](docs/VERIFICATION_STATUS.md) | Per-theorem status |
| [`docs-site/`](docs-site/) | Full documentation site |

## License

MIT - See [LICENSE.md](LICENSE.md) for details.
