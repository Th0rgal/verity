# Verification Status

## Architecture

Verity implements a **three-layer verification stack** proving smart contracts correct from specification to Yul bytecode:

```
EDSL contracts (Lean)
    ↓ Layer 1: EDSL ≡ CompilationModel [PROVEN FOR CURRENT CONTRACTS; GENERIC CORE, CONTRACT BRIDGES]
CompilationModel (declarative compiler-facing model)
    ↓ Layer 2: CompilationModel → IR [PARTIAL GENERIC, 2 AXIOMS, CONTRACT BRIDGES ACTIVE]
Intermediate Representation (IR)
    ↓ Layer 3: IR → Yul [GENERIC SURFACE, EXPLICIT BRIDGE HYPOTHESIS]
Yul (EVM Assembly)
    ↓ (Trusted: solc compiler)
EVM Bytecode
```

## Layer 1: EDSL ≡ CompilationModel — PROVEN FOR CURRENT CONTRACTS

**What it proves today**: running a contract through the EDSL `Contract` monad produces the same result as interpreting its `CompilationModel`. This is proved for every contract in the table below.

The proof core is generic (see [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)), but the bridge theorem that connects each contract's EDSL to its `CompilationModel` is still instantiated per contract.

> **Scope note**: the per-contract proofs under `Contracts/<Name>/Proofs/` go further — they show contracts satisfy human-readable specifications (e.g. "increment adds 1"). Those are downstream contract proofs, not Layer 1 itself.

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

> **Note**: Stdlib (0 internal proof-automation properties) is excluded from the contract-spec theorem table above but included in overall coverage statistics (277 total properties).

**What the generic typed-IR core covers**:

- **Inside the proof path**: tuple, bytes, fixed-array, dynamic-array, and string parameters carried as ABI head words/offsets.
- **Outside the proof path** (trusted at the `CompilationModel` boundary): linked libraries, ECMs, and fully custom ABI behavior.

**Internal helper calls**: supported operationally in `CompilationModel` and the fuel-based interpreter, but compositional proof reuse of helpers across callers is not yet a first-class verified interface. Tracked in [#1335](https://github.com/Th0rgal/verity/issues/1335).

### Lowering Bridge

[`Contracts/Proofs/SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean) provides the active contract-level bridge
theorems for supported EDSL contracts, covering:
- Write/read bridges for mutating and getter entrypoints
- Explicit revert-path bridges for owner-gated and arithmetic failure paths
- Composition with the compiled IR/Yul semantics used by the proof pipeline

## Layer 2: CompilationModel → IR — PARTIAL GENERIC

Tracking:
- Whole-contract generic theorem gap: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- Current body-simulation blocker: [#1564](https://github.com/Th0rgal/verity/issues/1564)
- Proof decomposition plan: [GENERIC_LAYER2_PLAN.md](./GENERIC_LAYER2_PLAN.md)

**Main theorem**: [`compile_preserves_semantics`](../Compiler/Proofs/IRGeneration/Contract.lean) — quantified over arbitrary supported `CompilationModel`s, selectors, a `SupportedSpec` witness, and successful `CompilationModel.compile` output. The proof chain is complete but transitively depends on 1 documented axiom (see below).

**Current proof status**:

| Status | What |
|--------|------|
| Proved generically | Supported statement-list compilation ([`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean), re-exported from [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)) |
| Proved generically | Initial-state normalization (`withTransactionContext` ↔ `initialIRStateForTx`) |
| Proved generically | Whole-contract theorem shape, dispatch, parameter loading |
| Still axiomatized | Body simulation for non-core statement patterns — `supported_function_body_correct_from_exact_state` in [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean) ([#1564](https://github.com/Th0rgal/verity/issues/1564)) |
| Contract-specific | End-to-end examples still use manual bridge theorems in [`SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean) |

**Explicit precondition**: the theorem requires transaction-context fields (`sender`, `thisAddress`, `msgValue`, `blockTimestamp`, `blockNumber`, `chainId`) to already fit the bounded source-side `Address`/`Uint256` domains.

**Outside current scope**: events/logs, proxy/delegatecall upgradeability, linked externals, local unsafe obligations, and other trust-surfaced features not captured by the supported whole-contract fragment.

| Contract | IR Functions | Status |
|----------|-------------|--------|
| SimpleStorage | 2 | Contract bridge proven |
| Counter | 3 | Contract bridge proven |
| Owned | 2 | Contract bridge proven |
| SafeCounter | 3 | Contract bridge proven |
| OwnedCounter | 5 | Contract bridge proven |
| Ledger | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |
| SimpleToken | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |
| ERC20 | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |
| ERC721 | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |
| Vault | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |
| LocalObligationMacroSmoke | — | No contract bridge theorem in `Contracts/Proofs/SemanticBridge.lean` |

Key files:
- [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)
- [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean)
- [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean)
- [`SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean)
- [`EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)

## Layer 3: IR → Yul — GENERIC, WITH EXPLICIT AXIOM BOUNDARY

**What it proves today**: Yul code generation preserves IR semantics through a generic statement/function equivalence stack, but the current full dispatch-preservation path still depends on 1 documented bridge hypothesis in [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean). The checked contract-level theorem surface now explicitly requires dispatch-guard safety for each selected function case: word-level zero `msg.value` on non-payable paths and a non-wrapping calldata-width bound for each case guard.

All 8 Yul statement types proven equivalent to IR counterparts. Universal dispatcher theorem:

```lean
theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    statesAligned selector irState yulState →
    execResultsAligned selector
      (execIRStmt irState stmt)
      (execYulStmtFuel fuel yulState stmt)
```

Key files: [`StatementEquivalence.lean`](../Compiler/Proofs/YulGeneration/StatementEquivalence.lean), [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean), [`AXIOMS.md`](../AXIOMS.md)

## Example Contract Compilation Coverage

The repository contains several different kinds of contract examples. Their current compile-preservation status is not uniform.

### Whole-contract EDSL → compiled IR bridge theorems present

These require manual contract-specific bridge proofs today:

- `SimpleStorage` (`store`, `retrieve`)
- `Counter` (`increment`, `decrement`, `getCount`)
- `Owned` (`getOwner`, `transferOwnership`)
- `SafeCounter` (`increment`, `decrement`, `getCount`)
- `OwnedCounter` (`getCount`, `getOwner`, `increment`, `decrement`, `transferOwnership`)

### EDSL → compiled Yul theorem present in `Contracts/Proofs/SemanticBridge.lean`

- `SimpleStorage` (`store`, `retrieve`)
- `Counter` (`increment`)  

All other current examples rely on the generic Layer 3 theorem plus testing, but do not yet have a dedicated contract-level EDSL → compiled Yul theorem in the repo.

### Spec proofs exist, but no manifest contract-level compile-preservation theorem to Yul

- `Ledger`
- `SimpleToken`
- `ERC20`
- `ERC721`
- `Vault`
- `LocalObligationMacroSmoke`

For these, the repo proves contract properties/specs, and many have macro-generated body-alignment theorems, but there is no manual bridge theorem in [`Contracts/Proofs/SemanticBridge.lean`](../Contracts/Proofs/SemanticBridge.lean) showing that the compiled IR/Yul execution preserves the contract semantics.

### Semantic example, not a current `verity_contract` compilation example

- `ReentrancyExample`

`ReentrancyExample` is proved as a semantic case study in Lean, but it is not a current `verity_contract` macro contract with a contract-level compilation-preservation theorem surface in this repo.

### Intentionally outside the current proof-complete compilation subset

- `CryptoHash`: linked external Yul libraries / external call oracle surface
- `RawLogTrustSurface`: raw event emission trust surface
- `LocalObligationTrustSurface`: explicit local unsafe/refinement obligation surface
- `ProxyUpgradeabilityMacroSmoke`, `ProxyUpgradeabilityLayoutCompatibleSmoke`, `ProxyUpgradeabilityLayoutIncompatibleSmoke`: proxy / `delegatecall` / upgradeability semantics are outside the current proof model
- `StringSmoke`, `StringEventSmoke`, `StringErrorSmoke`: smoke examples for string, error, and event surfaces rather than current end-to-end proof-complete examples

Also note that the macro-generated `*_semantic_preservation` theorems are not contract-to-Yul semantic-preservation theorems. They are body-alignment equalities between generated `CompilationModel` bodies and macro-generated body fixtures, not full execution-preservation proofs for compiled IR/Yul.

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

2 documented Lean axioms remain. The Layer 3 dispatch bridge is tracked as an explicit theorem hypothesis rather than a Lean axiom.

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
4. When trust-relevant features are in play (low-level mechanics, raw event emission, axiomatized primitives, local obligations, or external assumptions), emit a machine-readable trust report via `verity-compiler --trust-report <path>`. Use `--verbose` for a human-readable summary.

The trust report groups every foreign trust surface into `proofStatus.proved`, `proofStatus.assumed`, and `proofStatus.unchecked` buckets, localized to constructor/function usage sites. It separately lists proof-gap categories: `notModeledEventEmission`, `notModeledProxyUpgradeability`, `partiallyModeledLinearMemoryMechanics`, and `partiallyModeledRuntimeIntrospection`.

**Fail-closed flags** — each flag rejects the named surface and reports the exact usage site that introduced it:

| Flag | Rejects |
|------|---------|
| `--deny-unchecked-dependencies` | Any `unchecked` linked external or ECM module |
| `--deny-assumed-dependencies` | Any `assumed` or `unchecked` linked external or ECM module |
| `--deny-axiomatized-primitives` | Any axiomatized primitive (e.g. `keccak256`) |
| `--deny-local-obligations` | Any `assumed` or `unchecked` local unsafe/refinement obligation |
| `--deny-linear-memory-mechanics` | Any partially modeled linear-memory mechanic |
| `--deny-event-emission` | Any raw `rawLog` event emission |
| `--deny-low-level-mechanics` | Any first-class low-level call / returndata mechanic |
| `--deny-proxy-upgradeability` | Any `delegatecall`-based proxy/upgradeability mechanic (issue [#1420](https://github.com/Th0rgal/verity/issues/1420)) |
| `--deny-runtime-introspection` | Any partially modeled runtime-introspection primitive |

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-03-09
