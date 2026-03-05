<p align="center">
  <img src="verity.svg" alt="Verity" width="200" />
</p>

<h1 align="center">Verity</h1>

<p align="center">
  <strong>Formally verified smart contracts. From spec to bytecode.</strong>
</p>

<p align="center">
  <a href="https://github.com/Th0rgal/verity/blob/main/LICENSE.md"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT License"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/Th0rgal/verity"><img src="https://img.shields.io/badge/theorems-272-brightgreen.svg" alt="272 Theorems"></a>
  <a href="https://github.com/Th0rgal/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/Th0rgal/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

## What is Verity?

Verity is a **formally verified smart contract compiler** written in [Lean 4](https://lean-lang.org/). You write contracts in an embedded DSL (domain-specific language), write specs describing what the contract should do, prove the specs hold, and compile to Yul/EVM bytecode — with machine-checked proofs that compilation preserves semantics.

**In short**: write a contract, state what it should do, prove it, compile it, and the compiler is proven to not break anything along the way.

---

## How it works

### 1. Write a contract in the EDSL

Contracts look like Lean `do`-notation with storage declarations:

```lean
-- Contracts/Counter/Contract.lean
def count : StorageSlot Uint256 := ⟨0⟩

def increment : Contract Unit := do
  let current ← getStorage count
  setStorage count (add current 1)

def getCount : Contract Uint256 := do
  getStorage count
```

`Contract α` is a state monad: `ContractState → ContractResult α`. Operations like `getStorage`, `setStorage`, `require` manipulate blockchain state (storage slots, sender address, etc).

The `verity_contract` [macro](Verity/Macro/Elaborate.lean) can also generate these definitions from a more concise syntax:

```lean
-- Contracts/MacroContracts/Counter.lean
verity_contract Counter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)
```

### 2. Write a spec

Specs are plain Lean predicates describing what the contract should do:

```lean
-- Contracts/Counter/Spec.lean
def increment_spec (s s' : ContractState) : Prop :=
  s'.storage 0 = add (s.storage 0) 1 ∧
  storageUnchangedExcept 0 s s' ∧
  sameAddrMapContext s s'
```

This says: after `increment`, slot 0 increased by 1, no other slot changed, and context (sender, address maps) is preserved.

### 3. Prove the spec

Proofs show the contract satisfies its spec. Lean's type checker verifies them:

```lean
-- Contracts/Counter/Proofs/Basic.lean
theorem increment_meets_spec (s : ContractState) :
    let s' := ((increment).run s).snd
    increment_spec s s' := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · intro slot h_neq; simp [increment, count, ...]; split <;> simp_all
  · simp [sameAddrMapContext, ...]
```

### 4. Compile — with proven correctness

The compiler turns contracts into Yul (Solidity's low-level IR) through three layers, each proven to preserve semantics:

```
EDSL contract (Lean)
  ↓  Layer 1: EDSL ≡ CompilationModel     [PROVEN]
CompilationModel (declarative IR spec)
  ↓  Layer 2: CompilationModel → IR        [PROVEN]
Intermediate Representation
  ↓  Layer 3: IR → Yul                     [PROVEN, 3 axioms]
Yul
  ↓  solc (trusted external compiler)
EVM Bytecode
```

| Layer | What it proves | Key file |
|-------|---------------|----------|
| 1 | EDSL execution = CompilationModel interpretation | [TypedIRCompilerCorrectness.lean](Verity/Core/Free/TypedIRCompilerCorrectness.lean) |
| 2 | CompilationModel → IR preserves behavior | [IRInterpreter.lean](Compiler/Proofs/IRGeneration/IRInterpreter.lean) |
| 3 | IR → Yul codegen preserves behavior | [Preservation.lean](Compiler/Proofs/YulGeneration/Preservation.lean) |

Layers 2 and 3 (`CompilationModel → IR → Yul`) are verified with 3 axioms (one selector axiom plus two private preservation bridge axioms). See [AXIOMS.md](AXIOMS.md).

### 5. Test the compiled output (belt and suspenders)

**Foundry tests** (475 tests) validate EDSL = Yul = EVM execution. 475 Foundry tests across 38 test suites run the compiled Yul on a real EVM. The proofs already guarantee correctness, but the tests confirm it works end-to-end:

```bash
FOUNDRY_PROFILE=difftest forge test    # 475 tests across 38 suites
```

---

## Verified contracts

| Contract | Theorems | What it demonstrates |
|----------|----------|---------------------|
| SimpleStorage | 20 | Store/retrieve with roundtrip proof |
| Counter | 28 | Increment/decrement, composition proofs |
| SafeCounter | 25 | Overflow/underflow revert proofs |
| Owned | 23 | Access control, ownership transfer |
| OwnedCounter | 48 | Cross-pattern composition, lockout proofs |
| Ledger | 33 | Deposit/withdraw/transfer, balance conservation |
| SimpleToken | 61 | Mint/transfer, supply conservation |
| ERC20 | 19 | ERC-20 baseline with approve/transfer |
| ERC721 | 11 | NFT ownership/approval baseline |
| ReentrancyExample | 4 | Reentrancy vulnerability vs safe pattern |
| CryptoHash | — | External library linking demo (no proofs) |

272 theorems across 10 categories. 475 Foundry tests across 38 test suites. 250 covered by property tests (92% coverage, 22 proof-only exclusions). 3 documented axioms. 0 `sorry` placeholders.

---

## External calls

Verity's DSL prevents raw external calls for safety. Instead, you can:

1. **Link external Yul libraries** (e.g., Poseidon hash) at compile time:
   ```bash
   lake exe verity-compiler --link examples/external-libs/PoseidonT3.yul -o artifacts/yul
   ```
   The linked library's correctness is a trust assumption. See [examples/external-libs/](examples/external-libs/).

2. **Use External Call Modules (ECMs)** for typed, auditable call patterns (ERC-20 transfers, precompiles, callbacks). See [Compiler/Modules/](Compiler/Modules/) and [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md).

---

## Quick start

```bash
# Install Lean 4
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env

# Clone and build — Verifies all 272 theorems
git clone https://github.com/Th0rgal/verity.git && cd verity
lake build

# Compile contracts to Yul
lake exe verity-compiler                              # all contracts
lake exe verity-compiler --edsl-contract counter      # specific contract

# Run Foundry tests
FOUNDRY_PROFILE=difftest forge test    # 475 tests across 38 suites
```

**Scaffold a new contract**:
```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

This creates: implementation, spec, invariants, proofs, and Foundry test files.

---

## Verification guarantees

Every claim is enforced by CI on every commit:

| Claim | Value | Verify locally |
|-------|-------|----------------|
| Tracked theorems | 425 across 11 categories | `make verify` |
| Incomplete proofs (`sorry`) | 0 | `python3 scripts/check_lean_hygiene.py` |
| Project-specific axioms | 3 ([documented](AXIOMS.md)) | `make axiom-report` |
| Foundry runtime tests | 475 across 38 suites | `make test-foundry` |
| Property test coverage | 250/425 (59%) | `python3 scripts/check_property_coverage.py` |

---

## How Verity compares

| | Certora | Halmos | Verity |
|---|---|---|---|
| **Approach** | Bounded model checking | Symbolic execution (Z3) | Interactive theorem proving (Lean 4) |
| **Strengths** | Great automation, battle-tested | Free, integrates with Foundry | Unbounded proofs, verified compiler |
| **Trade-offs** | Bounded (may miss edge cases) | Bounded (path explosion) | Higher per-property effort |
| **Compiler trust** | Trusts solc entirely | Trusts solc entirely | Verifies 3 compilation layers |
| **Best for** | Production audits at scale | Bug-finding in Foundry | High-assurance contracts |

Verity is not a replacement for these tools. It's for cases where you need mathematical certainty across all inputs and execution paths. The effort gap is narrowing as AI improves at interactive theorem proving.

---

## Documentation

| Document | What it covers |
|----------|---------------|
| **[TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md)** | What's verified vs trusted, trust reduction roadmap |
| **[AXIOMS.md](AXIOMS.md)** | All axioms with soundness justifications |
| **[docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)** | Per-contract theorem status, coverage tables |
| **[docs/ROADMAP.md](docs/ROADMAP.md)** | Verification progress, planned features |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Coding conventions, PR guidelines |
| [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md) | ECM framework guide |
| [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md) | Wrapping arithmetic specification |
| [Docs site](https://verity.thomas.md/) | Full documentation with guides |

---

## Project structure

```
verity/
├── Verity/              # EDSL framework
│   ├── Core/            #   Core types: Contract monad, ContractState, Uint256
│   ├── Macro/           #   verity_contract macro elaborator
│   └── Stdlib/          #   Proven helper lemmas (arithmetic, automation)
├── Contracts/           # Verified contract implementations
│   ├── <Name>/Contract.lean   #   Contract implementation
│   ├── <Name>/Spec.lean       #   Formal specification
│   ├── <Name>/Proofs/*.lean   #   Correctness proofs
│   └── MacroContracts/  #   Macro-generated contract examples
├── Compiler/            # Compilation pipeline
│   ├── CompilationModel.lean  # Declarative compiler-facing contract model
│   ├── Proofs/          #   Compilation correctness proofs (Layers 1-3)
│   │   ├── SemanticBridge.lean      # EDSL ≡ IR bridge theorems
│   │   ├── EndToEnd.lean            # Layers 2+3 composition
│   │   └── YulGeneration/           # IR → Yul preservation
│   ├── Yul/             #   Yul code generation
│   └── Modules/         #   External Call Modules (ECMs)
├── test/                # Foundry tests (475 tests)
├── artifacts/yul/       # Compiled Yul output
└── scripts/             # CI validation scripts
```

## License

MIT - See [LICENSE.md](LICENSE.md).
