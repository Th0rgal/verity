# Verification Status

## Architecture

Verity implements a **three-layer verification stack** proving smart contracts correct from specification to Yul bytecode:

```
EDSL contracts (Lean)
    ↓ Layer 1: EDSL ≡ CompilationModel [PROVEN]
CompilationModel (declarative compiler-facing model)
    ↓ Layer 2: CompilationModel → IR [PARTIAL GENERIC, CONTRACT BRIDGES ACTIVE]
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
| LocalObligationMacroSmoke | 4 | Baseline | `Contracts/LocalObligationMacroSmoke/Proofs/` |
| SimpleToken | 61 | Complete | `Contracts/SimpleToken/Proofs/` |
| ERC20 | 19 | Baseline | `Contracts/ERC20/Proofs/` |
| ERC721 | 11 | Baseline | `Contracts/ERC721/Proofs/` |
| ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
| CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
| **Total** | **277** | **✅ 100%** | — |

> **Note**: Stdlib (0 internal proof-automation properties) is excluded from the Layer 1 contracts table above but included in overall coverage statistics (277 total properties).

Layer 1 uses macro-generated bridge theorems backed by a generic typed-IR compilation-correctness theorem ([`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)). Tuple/bytes/fixed-array/dynamic-array/string parameters now stay inside that proof path when they are carried as ABI head words/offsets. Advanced constructs beyond that typed-IR head-word surface (linked libraries, ECMs, fully custom ABI behavior) are still expressed directly in `CompilationModel` and trusted at that boundary.

Internal helper calls are supported operationally in `CompilationModel` and the fuel-based interpreter path, but helper-level compositional proof reuse across callers is not yet a first-class verified interface. Current Layer 1 bridges remain contract-specific; the reusable internal-helper proof boundary is tracked in [#1335](https://github.com/Th0rgal/verity/issues/1335).

### Lowering Bridge

`Compiler/Proofs/SemanticBridge.lean` provides the active contract-level bridge
theorems for supported EDSL contracts, covering:
- Write/read bridges for mutating and getter entrypoints
- Explicit revert-path bridges for owner-gated and arithmetic failure paths
- Composition with the compiled IR/Yul semantics used by the proof pipeline

## Layer 2: CompilationModel → IR — PARTIAL GENERIC

**What is generic today**: the repository has a structural theorem for raw
statement lists inside the explicit `SupportedStmtList` fragment witness in
[`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean),
re-exported for the compiler-proof layer in
[`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean).

**What is not generic yet**: there is not yet a single compiler-level theorem
quantified over arbitrary supported `CompilationModel` programs and successful
`CompilationModel.compile` output. Full-contract Layer 2 reasoning still
depends on contract-specific bridge theorems in
[`SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean).

**Current boundary**:
- Generic: supported statement-list compilation
- Contract-specific: full entrypoint dispatch, constructor behavior, and the
  final bridge from contract execution to compiled IR for the current contract set
- Outside the current generic theorem: events/logs, external or linked
  functionality, and other full-contract features that are not captured by the
  `SupportedStmtList` witness alone

| Contract | IR Functions | Status |
|----------|-------------|--------|
| SimpleStorage | 2 | Contract bridge proven |
| Counter | 3 | Contract bridge proven |
| SafeCounter | 3 | Contract bridge proven |
| Owned | 3 | Contract bridge proven |
| OwnedCounter | 5 | Contract bridge proven |
| Ledger | 4 | Contract bridge proven |
| SimpleToken | 6 | Contract bridge proven |

Key files:
- [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)
- [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- [`SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean)
- [`EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)

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
| LocalObligationMacroSmoke | 100% (4/4) | 0 |
| SimpleStorage | 95% (19/20) | 1 proof-only |
| OwnedCounter | 92% (44/48) | 4 proof-only |
| Owned | 87% (20/23) | 3 proof-only |
| SimpleToken | 85% (52/61) | 9 proof-only |
| Counter | 82% (23/28) | 5 proof-only |
| Stdlib | 0% (0/0) | 0 proof-only |

**Status**: 92% coverage (255/277), 22 remaining exclusions all proof-only

- **Total Properties**: 277
- **Covered**: 255
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
4. When low-level mechanics, raw `rawLog` event emission, axiomatized primitives (for example `keccak256`), local unsafe/refinement obligations, or external assumptions are in play, emit a machine-readable trust report via `verity-compiler --trust-report <path>`. The report groups foreign trust surfaces into explicit `proofStatus.proved`, `proofStatus.assumed`, and `proofStatus.unchecked` buckets, localizes them to constructor/function `usageSites`, surfaces localized `localObligations`, and now separately lists `notModeledEventEmission`, `notModeledProxyUpgradeability`, `partiallyModeledLinearMemoryMechanics`, and `partiallyModeledRuntimeIntrospection` so the current event, proxy/upgradeability, memory/ABI, and runtime-context proof gaps are explicit in both contract-level and per-site audit output. In human-readable mode, `--verbose` now emits matching usage-site and contract-level summaries. For fail-closed verification runs, add `--deny-unchecked-dependencies`, which now reports the exact usage site that introduced each unchecked dependency. For proof-strict runs that reject any unproved foreign surface, use `--deny-assumed-dependencies`, which fails on both `assumed` and `unchecked` linked externals / ECM modules and reports the exact usage site. For primitive-proof-strict runs, add `--deny-axiomatized-primitives`, which fails on any remaining axiomatized primitive and reports the exact usage site. For local-obligation-proof-strict runs, add `--deny-local-obligations`, which fails on any remaining `assumed` or `unchecked` localized unsafe/refinement obligation and reports the exact usage site. For memory-proof-strict runs, add `--deny-linear-memory-mechanics`, which fails on any remaining partially modeled linear-memory mechanic and reports the exact usage site. For event-proof-strict runs, add `--deny-event-emission`, which fails on any remaining raw `rawLog` event emission and reports the exact usage site. For low-level-proof-strict runs, add `--deny-low-level-mechanics`, which fails on any remaining first-class low-level call / returndata mechanic and reports the exact usage site. For proxy-proof-strict runs, add `--deny-proxy-upgradeability`, which fails on any remaining `delegatecall`-based proxy / upgradeability mechanic and reports the exact usage site; the dedicated proxy semantics gap is tracked under issue `#1420`. For runtime-proof-strict runs, add `--deny-runtime-introspection`, which fails on any remaining partially modeled runtime-introspection primitive and reports the exact usage site.

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-03-08
