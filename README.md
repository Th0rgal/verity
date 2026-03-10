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
  <a href="https://github.com/Th0rgal/verity/blob/main/docs/VERIFICATION_STATUS.md"><img src="https://img.shields.io/badge/verification-status-live-brightgreen.svg" alt="Verification status"></a>
  <a href="https://github.com/Th0rgal/verity/actions"><img src="https://img.shields.io/github/actions/workflow/status/Th0rgal/verity/verify.yml?label=verify" alt="Verify"></a>
</p>

---

## What is Verity?

Verity is a **formally verified smart contract compiler** written in [Lean 4](https://lean-lang.org/). You write contracts in an embedded DSL (domain-specific language), write specs describing what the contract should do, prove the specs hold, and compile to Yul/EVM bytecode — with machine-checked proofs that compilation preserves semantics.

**In short**: write a contract, state what it should do, prove it, compile it, and the compiler is proven to not break anything along the way.

---

## How it works

### 1. Write a contract

Contracts are written using the `verity_contract` [macro](Verity/Macro/Elaborate.lean). It is the canonical contract authoring path, and it generates both an executable Lean specification (`Contract` monad) and a declarative compilation model (`CompilationModel`) from one definition, with a machine-checked proof that they agree:

```lean
-- Contracts/Counter/Counter.lean
verity_contract Counter where
  storage
    count : Uint256 := slot 0

  function increment () : Unit := do
    let current ← getStorage count
    setStorage count (add current 1)
```

Under the hood, the macro generates a `Contract α` state monad (`ContractState → ContractResult α`) with operations like `getStorage`, `setStorage`, and `require` that manipulate blockchain state. You generally should not hand-write a separate `CompilationModel`; the macro-generated one is the compiler input.

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
  ↓  Layer 1: EDSL ≡ CompilationModel     [PROVEN FOR CURRENT CONTRACTS; GENERIC CORE, CONTRACT BRIDGES]
CompilationModel (declarative IR spec)
  ↓  Layer 2: CompilationModel → IR        [PARTIAL GENERIC, CONTRACT BRIDGES ACTIVE]
Intermediate Representation
  ↓  Layer 3: IR → Yul                     [GENERIC SURFACE, 1 AXIOM]
Yul
  ↓  solc (trusted external compiler)
EVM Bytecode
```

| Layer | What it proves | Key file |
|-------|---------------|----------|
| 1 | A generic typed-IR core plus contract-level bridge theorems establish EDSL execution = CompilationModel interpretation for the current supported contracts | [TypedIRCompilerCorrectness.lean](Compiler/TypedIRCompilerCorrectness.lean) |
| 2 | A generic whole-contract theorem shape exists, but its non-core function-level closure still depends on 2 documented axioms; the proved core fragment already runs on structural fuel, and the theorem surface now explicitly assumes normalized transaction-context fields | [Contract.lean](Compiler/Proofs/IRGeneration/Contract.lean) |
| 3 | IR → Yul codegen is proved generically at the statement/function level, but the current full dispatch-preservation path still uses 1 documented bridge axiom; the checked contract-level theorem surface now makes dispatch-guard safety explicit for each selected function case | [Preservation.lean](Compiler/Proofs/YulGeneration/Preservation.lean) |

There are currently 4 documented Lean axioms in total: 1 selector axiom, 2 generic non-core Layer 2 axioms, and 1 Layer 3 dispatch bridge axiom. See [AXIOMS.md](AXIOMS.md).

Layer 1 is the frontend EDSL-to-`CompilationModel` bridge. The per-contract files in `Contracts/<Name>/Proofs/` prove human-readable contract specifications; they are not what “Layer 1” means in the compiler stack. Layer 2 currently combines a generic supported-statement theorem with contract-specific full-contract bridges. Layers 2 and 3 (`CompilationModel → IR → Yul`) are verified with the current documented axioms and bridge boundaries; see [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) and [AXIOMS.md](AXIOMS.md).

### 5. Test the compiled output (belt and suspenders)

**Foundry tests** validate EDSL = Yul = EVM execution. See [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) for the current test count and coverage snapshot. The proofs already guarantee correctness, but the tests confirm it works end-to-end:

```bash
FOUNDRY_PROFILE=difftest forge test
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
| ReentrancyExample | 5 | Reentrancy vulnerability vs safe pattern |
| CryptoHash | — | External library linking demo (no proofs) |

Current theorem totals, test counts, coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

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

# Clone and build — verifies the current proof set
git clone https://github.com/Th0rgal/verity.git && cd verity
lake build

# Compile contracts to Yul
lake exe verity-compiler --manifest packages/verity-examples/contracts.manifest
lake exe verity-compiler --module Contracts.Counter.Counter  # specific contract

# Run Foundry tests
FOUNDRY_PROFILE=difftest forge test
```

**Scaffold a new contract**:
```bash
python3 scripts/generate_contract.py MyContract
python3 scripts/generate_contract.py MyToken --fields "balances:mapping,totalSupply:uint256,owner:address"
```

This creates: implementation, spec, invariants, proofs, and Foundry test files.

---

## Verification guarantees

Every claim is enforced by CI on every commit. See [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md) for the current counts, coverage tables, and proof-status snapshot, then use `make verify`, `make axiom-report`, `make test-foundry`, and `make check` for local confirmation.

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
│   ├── <Name>/Spec.lean       #   Formal specification
│   ├── <Name>/Proofs/*.lean   #   Correctness proofs
│   ├── <Name>/<Name>.lean      #   Canonical verity_contract definitions
│   └── Proofs/SemanticBridge.lean # Manual EDSL -> IR/Yul bridge theorems for a subset of contracts
├── Compiler/            # Compilation pipeline
│   ├── CompilationModel/      # Declarative compiler-facing model (types, validation, codegen)
│   ├── Proofs/          #   Compilation correctness proofs (Layers 1-3)
│   │   ├── EndToEnd.lean            # Layers 2+3 composition
│   │   └── YulGeneration/           # IR → Yul preservation
│   ├── Yul/             #   Yul code generation
│   └── Modules/         #   External Call Modules (ECMs)
├── packages/            # Independent sub-packages (verity-edsl, verity-compiler, verity-examples)
├── test/                # Foundry tests
├── artifacts/yul/       # Compiled Yul output
└── scripts/             # CI validation scripts
```

## License

MIT - See [LICENSE.md](LICENSE.md).
