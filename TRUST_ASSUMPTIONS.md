# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Compilation Pipeline

```
EDSL (Lean)
  ↓ [Layer 1: proved per contract, generic core + per-contract bridges]
CompilationModel
  ↓ [Layer 2: proved generically, 1 axiom]
IR
  ↓ [Layer 3: proved generically, dispatch bridge is a theorem hypothesis]
Yul
  ↓ [trusted, solc]
EVM Bytecode
```

The repository has no `sorry`, but it still has 2 documented Lean axioms. See [AXIOMS.md](AXIOMS.md) for the exact list and current elimination plan.

## What's Verified

- **Layer 1** (EDSL → `CompilationModel`): **Proved per contract.** A generic typed-IR compilation-correctness core exists; contract-level bridges instantiate it for each contract. Helper-proof reuse across callers is not yet a first-class generic interface ([#1335](https://github.com/Th0rgal/verity/issues/1335)).
  *Scope*: covers the EDSL-to-`CompilationModel` bridge only. Specification theorems in `Contracts/<Name>/Proofs/` (e.g. "increment adds 1") are a separate downstream proof layer.
- **Layer 2** (`CompilationModel` → IR): **Proved generically, 1 axiom.** The theorem `compile_preserves_semantics` holds for arbitrary supported `CompilationModel`s. It depends on `supported_function_body_correct_from_exact_state` for non-core body simulation (see [AXIOMS.md](AXIOMS.md)). Precondition: transaction-context fields must be bounded to the source-side `Address`/`Uint256` domains.
- **Layer 3** (IR → Yul): **Proved generically.** The dispatch bridge is an explicit theorem hypothesis, not a Lean axiom. Dispatch-guard preconditions: non-payable functions require word-level zero `msg.value`; each function case requires a non-wrapping calldata-width guard.
- **Cross-layer**: [`Contracts/Proofs/SemanticBridge.lean`](Contracts/Proofs/SemanticBridge.lean) has zero `sorry` but covers a subset of contracts — it is a manual bridge, not a fully generic replacement for Layers 1–3.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 2 documented axioms in [AXIOMS.md](AXIOMS.md): 1 selector axiom and 1 generic non-core Layer 2 axiom. The Layer 3 dispatch bridge remains an explicit theorem hypothesis rather than a Lean axiom.
- **Mitigation**: CI axiom reporting and location checks enforce explicit tracking.

### 3. Keccak-based Selector Computation
- **Role**: Function selector derivation (`bytes4(keccak256(signature))`).
- **Status**: 1 axiom in `Compiler/Selectors.lean:41`.
- **Mitigation**: CI cross-checks against `solc --hashes` and fixtures.

### 4. Linked Yul Libraries
- **Role**: External functions injected at compile time (e.g., Poseidon hash).
- **Trust**: Semantic correctness of linked code. Compiler validates names, arities, collisions.

### 5. Mapping Slot Derivation
- **Role**: `keccak256(abi.encode(key, baseSlot))` for Solidity-compatible storage (`activeMappingSlotBackend = .keccak`).
- **Trust**: external keccak implementation (`ffi.KEC` via EVMYul FFI) + standard collision-resistance assumptions (same trust class as Solidity/EVM).
- **Mitigation**: Abstraction-boundary CI, selector/hash cross-checks.
- **Audit surface**: machine-readable trust reports emit the explicit primitive assumption `keccak256_memory_slice_matches_evm` whenever a contract uses `Expr.keccak256`.

### 6. EVM/Yul Semantics and Gas
- **Role**: Runtime execution model.
- **Status**: 15 pure builtins bridged to EVMYulLean `UInt256` operations. Gas is not modeled.
- **Implication**: Semantic correctness does not imply gas-safety.
- **Proxy note**: `delegatecall`-based proxy / upgradeability flows still sit outside the current proof-interpreter model. Archive `--trust-report` and use `--deny-proxy-upgradeability` when proxy semantics must remain outside the selected verified subset (issue `#1420`).

### 7. External Call Modules (ECMs)
- **Role**: Reusable typed external call patterns (ERC-20 writes/reads including `totalSupply`, ERC-4626 preview/conversion helpers plus `totalAssets`, `asset`, `max*` limit reads, and `deposit`, oracle reads, precompiles, callbacks).
- **Trust**: Each module's `compile` produces correct Yul. Bug in one module doesn't affect others.
- **Mitigation**: Axiom aggregation at compile time (`--verbose`), machine-readable trust-surface emission via `--trust-report <path>`, and a fail-closed verification gate via `--deny-unchecked-dependencies` when unchecked foreign surfaces must be excluded. See [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md).

### 8. Lean Kernel
- **Role**: Proof checker soundness. Foundational assumption for all Lean-based verification.

### 9. Macro Elaborator (`verity_contract`)
- **Role**: Generates both EDSL `Contract` monad value and `CompilationModel` from one syntax tree.
- **Status**: Trusted unverified metaprogram ([Verity/Macro/Translate.lean](Verity/Macro/Translate.lean)).
- **Risk**: A translation bug would silently cause EDSL and CompilationModel to diverge.
- **Mitigation**: EDSL/IR/Yul cross-checks in [`Contracts/Proofs/SemanticBridge.lean`](Contracts/Proofs/SemanticBridge.lean) and differential tests catch divergence on the current contract set.

### 10. Local Unsafe / Refinement Obligations
- **Role**: Let a function or constructor declare a localized proof obligation for an unsafe/assembly-shaped boundary without marking the whole contract as opaque.
- **Status**: Surfaced explicitly in `--trust-report`, `--verbose`, and `proofStatus.*.localObligations`.
- **Mitigation**: `verity-compiler --deny-local-obligations` fails closed on any obligation that remains `assumed` or `unchecked`.

## Semantic Caveats

### Wrapping Arithmetic
`Uint256` arithmetic is **wrapping modulo 2^256**, matching the EVM. This is proven, not assumed (see `Compiler/Proofs/ArithmeticProfile.lean`). Checked operations (`safeAdd`, `safeSub`, `safeMul`) are available for overflow protection. See [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md).

### Revert-State Modeling
High-level semantics can expose intermediate state in reverted computations. EVM reverts discard state. Contracts should use checks-before-effects. See [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md).

## Security Audit Checklist

1. Confirm deployment uses the supported EDSL CLI path.
2. Review [AXIOMS.md](AXIOMS.md), ensure the axiom list is unchanged and justified.
3. If linked libraries are used, audit each linked Yul file as trusted code.
4. Validate selector, Yul compile, and storage-layout CI checks.
5. Confirm arithmetic and revert assumptions are acceptable for the target contract.
6. Review the low-level mechanics / external assumption report (`--verbose`) and archive `--trust-report <path>` for audit evidence when external calls or linked externals are used. For verification-oriented builds, also pass `--deny-unchecked-dependencies` so any remaining unchecked foreign surface fails closed.

## Planned Hardening

- **Issue #967**: Proof-carrying Yul rewrite rules, versioned parity packs, AST identity gates.
- **Issue #998**: Per-function machine-checked `EDSL execution ≡ EVMYulLean(compile(CompilationModel))` theorems.

## Related Documents

- [AXIOMS.md](AXIOMS.md) | [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md) | [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md)
- [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md) | [docs/ROADMAP.md](docs/ROADMAP.md) | [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

---

**Last Updated**: 2026-03-09
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
