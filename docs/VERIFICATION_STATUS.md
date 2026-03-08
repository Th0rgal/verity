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

**What it proves**: The EDSL `Contract` monad execution is equivalent to `CompilationModel` interpretation for all supported contracts. Per-contract proofs under `Contracts/<Name>/Proofs/` then show these contracts satisfy their human-readable specifications.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | Complete | `Contracts/SimpleStorage/Proofs/` |
| Counter | 28 | Complete | `Contracts/Counter/Proofs/` |
| SafeCounter | 25 | Complete | `Contracts/SafeCounter/Proofs/` |
| Owned | 23 | Complete | `Contracts/Owned/Proofs/` |
| OwnedCounter | 48 | Complete | `Contracts/OwnedCounter/Proofs/` |
| Ledger | 33 | Complete | `Contracts/Ledger/Proofs/` |
| SimpleToken | 61 | Complete | `Contracts/SimpleToken/Proofs/` |
| ERC20 | 19 | Baseline | `Contracts/ERC20/Proofs/` |
| ERC721 | 11 | Baseline | `Contracts/ERC721/Proofs/` |
| ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
| CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
| **Total** | **273** | **✅ 100%** | — |

> **Note**: Stdlib (0 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (273 total properties).

Layer 1 uses macro-generated bridge theorems backed by a generic typed-IR compilation-correctness theorem ([`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)). Advanced constructs (linked libraries, ECMs, custom ABI) are expressed directly in `CompilationModel` and trusted at that boundary.

Internal helper calls are supported operationally in `CompilationModel` and the fuel-based interpreter path, but helper-level compositional proof reuse across callers is not yet a first-class verified interface. Current Layer 1 bridges remain contract-specific; the reusable internal-helper proof boundary is tracked in [#1335](https://github.com/Th0rgal/verity/issues/1335).

### Lowering Bridge

`Compiler/Proofs/SemanticBridge.lean` provides the active contract-level bridge
theorems for supported EDSL contracts, covering:
- Write/read bridges for mutating and getter entrypoints
- Explicit revert-path bridges for owner-gated and arithmetic failure paths
- Composition with the compiled IR/Yul semantics used by the proof pipeline

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
| ReentrancyExample | 100% (5/5) | 0 |
| Ledger | 100% (33/33) | 0 |
| SimpleStorage | 95% (19/20) | 1 proof-only |
| OwnedCounter | 92% (44/48) | 4 proof-only |
| Owned | 87% (20/23) | 3 proof-only |
| SimpleToken | 85% (52/61) | 9 proof-only |
| Counter | 82% (23/28) | 5 proof-only |
| Stdlib | 0% (0/0) | 0 proof-only |

**Status**: 92% coverage (251/273), 22 remaining exclusions all proof-only

- **Total Properties**: 273
- **Covered**: 251
- **Excluded**: 22 (all proof-only)

**Proof-Only Properties (22 exclusions)**: Internal proof machinery that cannot be tested in Foundry.

0 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.

## Differential Testing

**Status**: CI runs large sharded randomized differential suites against the current contract set, comparing EDSL interpreter output against Solidity-compiled EVM execution.

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
4. When low-level mechanics, axiomatized primitives (for example `keccak256`), or external assumptions are in play, emit a machine-readable trust report via `verity-compiler --trust-report <path>`. The report groups foreign trust surfaces into explicit `proofStatus.proved`, `proofStatus.assumed`, and `proofStatus.unchecked` buckets, and localizes them to constructor/function `usageSites`. In human-readable mode, `--verbose` now emits a matching `Usage-site trust report` section before the contract-level summaries. For fail-closed verification runs, add `--deny-unchecked-dependencies`, which now reports the exact usage site that introduced each unchecked dependency.

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-03-07
