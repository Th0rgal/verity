# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Compilation Pipeline

```
EDSL (Lean)
  ↓ [Layer 1: PROVEN — EDSL ≡ CompilationModel bridge]
CompilationModel
  ↓ [Layer 2: FULLY VERIFIED — CompilationModel → IR]
IR
  ↓ [Layer 3: FULLY VERIFIED, 1 axiom — IR → Yul]
Yul
  ↓ [trusted — solc]
EVM Bytecode
```

All three layers are proven in Lean, with 1 documented axiom (the selector axiom; see [AXIOMS.md](AXIOMS.md)).

## What's Verified

- **Layer 1**: EDSL behavior matches its CompilationModel. For supported contracts, a generic typed-IR compilation-correctness theorem eliminates per-contract manual proofs.
- **Layer 2**: CompilationModel → IR preserves behavior.
- **Layer 3**: IR → Yul preserves behavior, with 1 documented axiom (keccak256 selector).
- **Cross-layer**: `Compiler/Proofs/SemanticBridge.lean` has zero `sorry`; `Compiler/Proofs/EndToEnd.lean` composes Layers 2+3.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 1 documented axiom in [AXIOMS.md](AXIOMS.md) (`keccak256_first_4_bytes`).
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

### 6. External Call Modules (ECMs)
- **Role**: Reusable typed external call patterns (ERC-20, ERC-4626 previews, oracle reads, precompiles, callbacks).
- **Trust**: Each module's `compile` produces correct Yul. Bug in one module doesn't affect others.
- **Mitigation**: Axiom aggregation at compile time (`--verbose`) and machine-readable trust-surface emission via `--trust-report <path>`. See [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md).

### 7. Lean Kernel
- **Role**: Proof checker soundness. Foundational assumption for all Lean-based verification.

### 8. Macro Elaborator (`verity_contract`)
- **Role**: Generates both EDSL `Contract` monad value and `CompilationModel` from one syntax tree.
- **Status**: Trusted unverified metaprogram ([Verity/Macro/Translate.lean](Verity/Macro/Translate.lean)).
- **Risk**: A translation bug would silently cause EDSL and CompilationModel to diverge.
- **Mitigation**: EDSL ≡ IR bridge theorems in `Compiler/Proofs/SemanticBridge.lean` cross-check independently.

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
6. Review the low-level mechanics / external assumption report (`--verbose`) and archive `--trust-report <path>` for audit evidence when external calls or linked externals are used.

## Planned Hardening

- **Issue #967**: Proof-carrying Yul rewrite rules, versioned parity packs, AST identity gates.
- **Issue #998**: Per-function machine-checked `EDSL execution ≡ EVMYulLean(compile(CompilationModel))` theorems.

## Related Documents

- [AXIOMS.md](AXIOMS.md) | [docs/ARITHMETIC_PROFILE.md](docs/ARITHMETIC_PROFILE.md) | [docs/REVERT_STATE_MODEL.md](docs/REVERT_STATE_MODEL.md)
- [docs/EXTERNAL_CALL_MODULES.md](docs/EXTERNAL_CALL_MODULES.md) | [docs/ROADMAP.md](docs/ROADMAP.md) | [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)

---

**Last Updated**: 2026-03-08
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
