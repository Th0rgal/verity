# Verification Status

## Architecture

Verity implements a **three-layer verification stack** proving smart contracts correct from specification to Yul bytecode:

```
EDSL contracts (Lean)
    ↓ Layer 1: EDSL ≡ CompilationModel [PROVEN]
CompilationModel (declarative compiler-facing model)
    ↓ Layer 2: CompilationModel → IR [PROVEN]
Intermediate Representation (IR)
    ↓ Layer 3: IR → Yul [PROVEN, 1 axiom]
Yul (EVM Assembly)
    ↓ (Trusted: solc compiler)
EVM Bytecode
```

## Layer 1: EDSL ≡ CompilationModel — COMPLETE

**What it proves**: The EDSL `Contract` monad execution is equivalent to `CompilationModel` interpretation for all supported contracts. Per-contract proofs under `Verity/Proofs/` then show these contracts satisfy their human-readable specifications.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | Complete | `Verity/Proofs/SimpleStorage/` |
| Counter | 28 | Complete | `Verity/Proofs/Counter/` |
| SafeCounter | 25 | Complete | `Verity/Proofs/SafeCounter/` |
| Owned | 23 | Complete | `Verity/Proofs/Owned/` |
| OwnedCounter | 48 | Complete | `Verity/Proofs/OwnedCounter/` |
| Ledger | 33 | Complete | `Verity/Proofs/Ledger/` |
| SimpleToken | 61 | Complete | `Verity/Proofs/SimpleToken/` |
| ERC20 | 19 | Baseline | `Verity/Proofs/ERC20/` |
| ERC721 | 11 | Baseline | `Verity/Proofs/ERC721/` |
| ReentrancyExample | 4 | Complete | `Verity/Examples/ReentrancyExample.lean` |
| CryptoHash | 0 | No specs | `Verity/Examples/CryptoHash.lean` |
| **Total** | **272** | **✅ 100%** | — |

> **Note**: Stdlib (153 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (425 total properties).

Layer 1 uses macro-generated bridge theorems backed by a generic typed-IR compilation-correctness theorem ([`TypedIRCompilerCorrectness.lean`](../Verity/Core/Free/TypedIRCompilerCorrectness.lean)). Advanced constructs (linked libraries, ECMs, custom ABI) are expressed directly in `CompilationModel` and trusted at that boundary.

### Lowering Bridge

`Compiler/Proofs/Lowering/FromEDSL.lean` provides transition bridge theorems for all supported EDSL contracts (SimpleStorage, Counter, Owned, Ledger, OwnedCounter, SimpleToken, SafeCounter), covering:
- Write/read bridges for mutating and getter entrypoints
- Explicit revert-path bridges (owner-gated, insufficient-balance, overflow/underflow)
- Parser determinism for `--edsl-contract` selection IDs

## Layer 2: CompilationModel → IR — COMPLETE

**What it proves**: IR generation preserves CompilationModel semantics.

| Contract | IR Functions | Status |
|----------|-------------|--------|
| SimpleStorage | 2 | Proven |
| Counter | 3 | Proven |
| SafeCounter | 3 | Proven |
| Owned | 3 | Proven |
| OwnedCounter | 5 | Proven |
| Ledger | 4 | Proven |
| SimpleToken | 6 | Proven |

Key files: [`IRInterpreter.lean`](../Compiler/Proofs/IRGeneration/IRInterpreter.lean), [`EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)

## Layer 3: IR → Yul — COMPLETE

**What it proves**: Yul code generation preserves IR semantics.

All 8 Yul statement types proven equivalent to IR counterparts. Universal dispatcher theorem:

```lean
theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    statesAligned selector irState yulState →
    execResultsAligned selector
      (execIRStmt irState stmt)
      (execYulStmtFuel fuel yulState stmt)
```

Key files: [`StatementEquivalence.lean`](../Compiler/Proofs/YulGeneration/StatementEquivalence.lean), [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean)

## Property Test Coverage

| Contract | Coverage | Exclusions |
|----------|----------|------------|
| ERC20 | 100% (19/19) | 0 |
| ERC721 | 100% (11/11) | 0 |
| SafeCounter | 100% (25/25) | 0 |
| ReentrancyExample | 100% (4/4) | 0 |
| Ledger | 100% (33/33) | 0 |
| SimpleStorage | 95% (19/20) | 1 proof-only |
| OwnedCounter | 92% (44/48) | 4 proof-only |
| Owned | 87% (20/23) | 3 proof-only |
| SimpleToken | 85% (52/61) | 9 proof-only |
| Counter | 82% (23/28) | 5 proof-only |
| Stdlib | 0% (0/153) | 153 proof-only |

**Status**: 59% coverage (250/425), 175 remaining exclusions all proof-only

- **Total Properties**: 425
- **Covered**: 250
- **Excluded**: 175 (all proof-only)

**Proof-Only Properties (175 exclusions)**: Internal proof machinery that cannot be tested in Foundry.

12 `sorry` remaining: 12 in `Compiler/Proofs/SemanticBridge.lean` (EDSL ≡ IR bridge theorem proofs, blocked by `evalBuiltinCall` heartbeat limit after callvalue/calldatasize refactor) and 0 in `Compiler/Proofs/YulGeneration/Preservation.lean`. The theorem *statements* are preserved; only the proof terms use placeholders.

## Differential Testing

**Status**: Scaled to 100,000+ tests (10,000 per contract x 9 contracts) with 8-shard CI parallelization. Randomized inputs covering edge cases, comparing EDSL interpreter output against Solidity-compiled EVM execution.

## Solidity Interop Support Matrix (Issue #586)

This matrix tracks migration-critical Solidity interoperability features and current implementation status.

Status legend:
- `supported`: usable end-to-end
- `partial`: implemented with functional limits or incomplete proof/test coverage
- `unsupported`: not implemented as a first-class feature

| Feature | Spec support | Codegen support | Proof status | Test status | Current status |
|---|---|---|---|---|---|
| Custom errors + typed revert payloads | partial | partial | n/a | partial | partial |
| Low-level calls (`call` / `staticcall` / `delegatecall`) with returndata | partial | partial | n/a | partial | partial |
| `fallback` / `receive` / payable entrypoint modeling | partial | partial | n/a | partial | partial |
| Event ABI parity for indexed dynamic/tuple payloads | supported | supported | supported | supported | supported |
| Storage layout controls (packing + explicit slots) | partial | partial | partial | partial | partial |
| ABI JSON artifact generation | partial | partial | n/a | partial | partial |

Diagnostics policy for unsupported constructs:
1. Report the exact unsupported construct at compile time.
2. Suggest the nearest supported migration pattern.
3. Link to the owning tracking issue.

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-03-03
