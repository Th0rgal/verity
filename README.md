# Dumb Contracts

A minimal Lean 4 embedded DSL for writing and formally verifying smart contracts.

The core is 212 lines of Lean. It models contract state, storage operations, and `require` guards using an explicit success/revert result type. On top of this, 7 example contracts are implemented and verified with 252 machine-checked proofs (no `sorry`, no axioms).

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
  let s' := (store value).run s |>.2
  let result := retrieve.run s' |>.1
  result = value := by
  have h_store := store_meets_spec s value
  have h_retrieve := retrieve_meets_spec ((store value).run s |>.2)
  simp [store_spec] at h_store
  simp [retrieve_spec] at h_retrieve
  simp only [h_retrieve, h_store.1]
```

Build and verify:
```bash
lake build  # Type-checks all 252 proofs
```

## Contracts

| Contract | Theorems | What's verified |
|----------|----------|-----------------|
| SimpleStorage | 19 | Store/retrieve roundtrip, state isolation |
| Counter | 29 | Arithmetic, composition, decrement-at-zero |
| Owned | 22 | Access control, ownership transfer |
| SimpleToken | 64 | Mint/transfer, supply conservation, storage isolation |
| OwnedCounter | 34 | Cross-pattern composition, ownership transfer lockout |
| Ledger | 40 | Deposit/withdraw/transfer, balance conservation |
| SafeCounter | 30 | Overflow/underflow revert proofs |
| Stdlib/Math | 14 | safeMul/safeDiv correctness |

## What's proven

- **Safety**: Access control (mint reverts for non-owner), no overdrafts (transfer reverts on insufficient balance), overflow protection
- **Correctness**: Each state-modifying operation matches its specification
- **Invariants**: WellFormedState preservation, owner stability, storage isolation between slot types
- **Composition**: Operation sequences produce expected results (mint then balanceOf, deposit then withdraw cancellation, ownership transfer locks out old owner)
- **Conservation**: Exact sum equations for token mint/transfer and ledger deposit/withdraw/transfer

## Project structure

```
edsl/
└── DumbContracts/
    ├── Core.lean           # 212 lines: ContractResult, storage ops, require, simp lemmas
    └── Stdlib/Math.lean    # Safe arithmetic (safeAdd, safeSub, safeMul, safeDiv)

examples/lean/
└── DumbContracts/
    ├── Examples/           # 7 contract implementations
    ├── Specs/              # Formal specifications per contract (Spec.lean, Invariants.lean)
    └── Proofs/             # Machine-checked proofs per contract (Basic.lean, Correctness.lean, ...)

examples/solidity/          # Solidity reference contracts
compiler/                   # Lean-to-Yul compiler work area
```

## Core API

```lean
-- Contract monad with explicit success/failure
inductive ContractResult (α : Type) where
  | success : α → ContractState → ContractResult α
  | revert : String → ContractState → ContractResult α

abbrev Contract (α : Type) := ContractState → ContractResult α

-- Storage operations
def getStorage : StorageSlot Uint256 → Contract Uint256
def setStorage : StorageSlot Uint256 → Uint256 → Contract Unit
def getMapping : StorageSlot (Address → Uint256) → Address → Contract Uint256
def setMapping : StorageSlot (Address → Uint256) → Address → Uint256 → Contract Unit

-- Guards
def require : Bool → String → Contract Unit
```

The `ContractResult` type makes `require` failures explicit. The custom `bind` short-circuits on `revert`, so do-notation works like Solidity: a failed `require` stops execution and reverts.

## Getting started

Requires [Lean 4](https://leanprover.github.io/) (4.15.0+).

```bash
git clone https://github.com/Th0rgal/dumbcontracts.git
cd dumbcontracts
lake build
```

To write a verified contract, add files in three places:
1. `examples/lean/DumbContracts/Examples/` for the implementation
2. `examples/lean/DumbContracts/Specs/` for the specification
3. `examples/lean/DumbContracts/Proofs/` for the proofs

## Known limitations

- Transfer proofs require `sender != to` (self-transfer overwrites the sender deduction)
- Uint256 is modeled as `Nat` (no overflow for basic arithmetic)
- No multi-contract interaction
- No reentrancy modeling
- No Mathlib dependency, so `ring`, `linarith`, etc. are unavailable

## Documentation

- [STATUS.md](STATUS.md) - Current verification status
- [RESEARCH.md](RESEARCH.md) - Design history
- [docs-site/](docs-site/) - Documentation website

## License

MIT
