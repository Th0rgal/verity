# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Compilation Pipeline

```
EDSL (Lean)
  ↓ [Layer 1: PROVEN FOR CURRENT CONTRACTS — generic core, contract bridges]
CompilationModel
  ↓ [Layer 2: PARTIAL GENERIC — generic theorem surface, 4 axioms]
IR
  ↓ [Layer 3: GENERIC, 5 axioms — IR → Yul]
Yul
  ↓ [trusted — solc]
EVM Bytecode
```

The repository has no `sorry`, but it still has 10 documented Lean axioms. See [AXIOMS.md](AXIOMS.md) for the exact list and current elimination plan.

## What's Verified

- **Layer 1**: A generic typed-IR compilation-correctness core exists, but the active contract-level bridges are still instantiated per contract and internal-helper proof reuse is not yet a first-class generic interface.
- **Layer 2**: A generic whole-contract theorem surface exists for supported `CompilationModel`s, and `supported_function_correct` is now a real theorem, but it still depends on 4 documented sub-axioms for initial-state normalization, parameter-state exactness, body simulation, and the `execIRFunctionFuel`/`execIRFunction` bridge.
- **Layer 3**: IR → Yul preservation is generic at the proof surface, but the current full dispatch-preservation path still depends on 5 documented axioms.
- **Cross-layer**: [`Contracts/Proofs/SemanticBridge.lean`](Contracts/Proofs/SemanticBridge.lean) has zero `sorry`, but it is a manual bridge layer for a subset of contracts rather than a fully generic replacement for Layers 1-3.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 10 documented axioms in [AXIOMS.md](AXIOMS.md): 1 selector axiom, 4 generic Layer 2 axioms, and 5 Layer 3 dispatch/preservation axioms.
- **Mitigation**: CI axiom reporting and location checks enforce explicit tracking.

### 3. Keccak-based Selector Computation
- **Role**: Function selector derivation (`bytes4(keccak256(signature))`).
- **Status**: 1 axiom in `Compiler/Selectors.lean:41`.
- **Mitigation**: CI cross-checks against `solc --hashes` and fixtures.

### 3. Linked Yul Libraries
- **Role**: External functions injected at compile time (e.g., Poseidon hash).
- **Trust**: Semantic correctness of linked code. Compiler validates names, arities, collisions.

### 4. Mapping Slot Derivation
- **Role**: `keccak256(abi.encode(key, baseSlot))` for Solidity-compatible storage (`activeMappingSlotBackend = .keccak`).
- **Trust**: external keccak implementation (`ffi.KEC` via EVMYul FFI) + standard collision-resistance assumptions (same trust class as Solidity/EVM).
- **Mitigation**: Abstraction-boundary CI, selector/hash cross-checks.
- **Audit surface**: machine-readable trust reports now emit the explicit primitive assumption `keccak256_memory_slice_matches_evm` whenever a contract uses `Expr.keccak256`.

### 5. EVM/Yul Semantics and Gas
- **Role**: Runtime execution model.
- **Status**: 15 pure builtins bridged to EVMYulLean `UInt256` operations. Gas is not modeled.
- **Implication**: Semantic correctness does not imply gas-safety.
- **Proxy note**: `delegatecall`-based proxy / upgradeability flows still sit outside the current proof-interpreter model. Archive `--trust-report` and use `--deny-proxy-upgradeability` when proxy semantics must remain outside the selected verified subset (issue `#1420`).

### 6. External Call Modules (ECMs)
- **Role**: Reusable typed external call patterns (ERC-20 writes/reads including `totalSupply`, ERC-4626 preview/conversion helpers plus `totalAssets`, `asset`, `max*` limit reads, and `deposit`, oracle reads, precompiles, callbacks).
- **Trust**: Each module's `compile` produces correct Yul. Bug in one module doesn't affect others.
- **Mitigation**: Axiom aggregation at compile time (`--verbose`), machine-readable trust-surface emission via `--trust-report <path>`, and a fail-closed verification gate via `--deny-unchecked-dependencies` when unchecked foreign surfaces must be excluded. See [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md).

### 7. Lean Kernel
- **Role**: Proof checker soundness. Foundational assumption for all Lean-based verification.

### 8. Macro Elaborator (`verity_contract`)
- **Role**: Generates both EDSL `Contract` monad value and `CompilationModel` from one syntax tree.
- **Status**: Trusted unverified metaprogram ([Verity/Macro/Translate.lean](Verity/Macro/Translate.lean)).
- **Risk**: A translation bug would silently cause EDSL and CompilationModel to diverge.
- **Mitigation**: EDSL/IR/Yul cross-checks in [`Contracts/Proofs/SemanticBridge.lean`](Contracts/Proofs/SemanticBridge.lean) and differential tests catch divergence on the current contract set.

### 9. Local Unsafe / Refinement Obligations
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
2. Review [AXIOMS.md](AXIOMS.md) — ensure the axiom list is unchanged and justified.
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
