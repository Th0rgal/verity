# Trust Assumptions and Verification Boundaries

This document states what Verity proves and what it still trusts.

## Compilation Pipeline

```
EDSL (Lean)
  ↓ [Layer 1: PROVEN FOR CURRENT CONTRACTS, generic core, contract bridges]
CompilationModel
  ↓ [Layer 2: SUPPORTED-FRAGMENT GENERIC THEOREM -- CompilationModel → IR]
IR
  ↓ [Layer 3: GENERIC SURFACE, explicit bridge hypothesis, IR → Yul]
Yul
  ↓ [trusted: solc]
EVM Bytecode
```

The repository currently has 0 `sorry` placeholders across the `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules that participate in the verified compiler stack. Layer 2 (Source → IR) and Layer 3 (IR → Yul) proof scripts are fully discharged, and it now has 0 documented Lean axioms. See [AXIOMS.md](AXIOMS.md) for details.

## What's Verified

- **Layer 1**: A generic typed-IR compilation-correctness core exists, but the active contract-level bridges are still instantiated per contract and internal-helper proof reuse is not yet a first-class generic interface.
  This names the frontend EDSL-to-`CompilationModel` bridge only; the
  contract-specific specification theorems in `Contracts/<Name>/Proofs/` are a
  separate proof layer about human-readable contract behavior.
- **Layer 2**: A generic whole-contract theorem is proved for the current supported `CompilationModel` fragment. `supported_function_correct` is now a real theorem, the initial-state normalization step is proved, the former generic body-simulation axiom has been eliminated, and the theorem surface makes explicit that the observed transaction-context fields must already be normalized to the bounded source-side `Address`/`Uint256` domains. Remaining Layer 2 work is now about widening the supported fragment and helper-aware completeness, not repairing `sorry` placeholders.
- **Layer 3**: IR → Yul preservation is generic at the proof surface, and the remaining dispatch bridge now lives as an explicit theorem hypothesis rather than a Lean axiom. The checked contract-level theorem surface makes the dispatch-guard safety preconditions explicit: non-payable cases must see word-level zero `msg.value`, and each selected function case must have a non-wrapping calldata-width guard.

Current theorem totals, property-test coverage, and proof status live in [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md).

## Trusted Components

### 1. Solidity Compiler (`solc`)
- **Role**: Compiles Yul → EVM bytecode.
- **Version**: 0.8.33+commit.64118f21 (pinned).
- **Mitigation**: CI enforces pin and Yul compileability checks.

### 2. Lean Axioms
- **Role**: Bridge remaining proof obligations not yet fully discharged.
- **Status**: 0 documented axioms in [AXIOMS.md](AXIOMS.md). The mapping-slot range axiom has been eliminated via the kernel-computable Keccak engine. Selector computation is kernel-computable, the Layer 2 generic body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge remains an explicit theorem hypothesis rather than a Lean axiom.
- **Mitigation**: CI axiom reporting and location checks enforce explicit tracking.

### 3. Keccak-based Selector Computation
- **Role**: Function selector derivation (`bytes4(keccak256(signature))`).
- **Status**: kernel-computable in `Compiler/Selectors.lean` via the vendored unrolled Keccak engine in `Compiler/Keccak/`.
- **Mitigation**: CI cross-checks against `solc --hashes`, selector fixtures, and fixed selector examples.

### 4. Linked Yul Libraries
- **Role**: External functions injected at compile time (e.g., Poseidon hash).
- **Trust**: Semantic correctness of linked code. Compiler validates names, arities, collisions.

### 5. Mapping Slot Derivation
- **Role**: `keccak256(abi.encode(key, baseSlot))` for Solidity-compatible storage (`activeMappingSlotBackend = .keccak`).
- **Trust**: external keccak implementation (`ffi.KEC` via EVMYul FFI) + standard collision-resistance assumptions (same trust class as Solidity/EVM).
- **Mitigation**: Abstraction-boundary CI, selector/hash cross-checks.
- **Audit surface**: machine-readable trust reports now emit the explicit primitive assumption `keccak256_memory_slice_matches_evm` whenever a contract uses `Expr.keccak256`.

### 6. EVM/Yul Semantics and Gas
- **Role**: Runtime execution model.
- **Status (Phase 4: sorry-dependent recursive statement-target fragment + generated runtime equality)**: 25 universal pure bridge theorems (23 fully proven, 2 with sorry-dependent core equivalences) in `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanBridgeLemmas.lean`. All pure bridge cases are now covered by universal symbolic lemmas. Additionally, 11 context/env/storage/helper builtin bridge theorems bring the total to 36 of 36 builtins bridged. The retargeting module `EvmYulLeanRetarget.lean` proves the pointwise theorem `backends_agree_on_bridged_builtins`, the expression-level theorem `evalYulExpr_evmYulLean_eq_on_bridged`, statement-fragment helpers for straight-line, block, if, switch, and for cases, the recursive target theorem `execYulFuelWithBackend_eq_on_bridged_target` for `BridgedTarget` values whose nested statements satisfy `BridgedStmt`, `emitYul_runtimeCode_bridged`, which shows the emitted runtime wrapper satisfies `BridgedTarget` when the IR bodies it embeds satisfy `BridgedStmt`, and `emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies`, which states emitted runtime-code execution through Verity `execYulFuel` equals the EVMYulLean backend executor under the same body hypotheses. `EvmYulLeanBodyClosure.lean` also proves concrete body-closure increments: scalar calldata parameter prologues (`genParamLoads_scalar_bridged`) satisfy `BridgedStmts`, static scalar leaf-load helpers for fixed arrays/tuples (`genStaticTypeLoads_calldataload_bridged`) satisfy `BridgedStmts`, full `genParamLoads` prologues for static scalar parameter lists (`genParamLoads_static_scalar_bridged`) satisfy `BridgedStmts`, scalar-leaf `letVar`/`assignVar` source statement lists (`compileStmtList_binding_leaf_bridged`) compile to `BridgedStmts`, pure-expression `letVar`/`assignVar` source statement lists (`compileStmtList_pure_binding_bridged`) compile to `BridgedStmts`, pure-binding plus unpacked single-slot `setStorage` statement lists (`compileStmtList_storage_fragment_bridged`) compile to `BridgedStmts`, external `stop`/`return` terminator statement lists (`compileStmtList_terminator_external_bridged`) compile to `BridgedStmts`, internal `return` assignment-plus-`leave` statement lists (`compileStmtList_internal_return_bridged`) compile to `BridgedStmts`, plain `Stmt.require` statement lists with bridged failure conditions (`compileStmtList_require_bridged`, using a hypothesis-free `revertWithMessage_bridged` lemma for the generated revert body) compile to `BridgedStmts`, and mixed external/internal source-body fragments composed from those pieces (`compileStmtList_external_body_fragment_bridged`, `compileStmtList_internal_body_fragment_bridged`) compile to `BridgedStmts`. `EvmYulLeanSourceExprClosure.lean` proves scalar source-expression leaf closure (`compileExpr_bridgedSource_leaf`) for `literal`/`param`/`constructorArg`/`localVar` and pure arithmetic/comparison/bit-operation expression closure (`compileExpr_bridgedSource`) for the `BridgedSourceExpr` fragment. Backend-equivalence retargeting theorems transitively depend on the sorry-backed smod/sar core equivalences. It also proves `execYulFuelWithBackend_verity_eq`, so the backend-parameterized executor is known to recover existing Verity semantics at `.verity`. Layer-3 composition and full body closure under `BridgedStmt` are not yet proven. Gas is not modeled.
- **Trust boundary (recursive statement-target fragment with generated runtime equality, conditional)**: For `BridgedExpr` expressions, `BridgedStraightStmts` statement lists (including mapping-slot, literal-slot, and identifier-slot `sstore`), recursive `BridgedTarget` executions, and emitted runtime wrappers whose embedded bodies satisfy `BridgedStmt`, the trust assumption moves from "Verity's custom builtin implementations are correct" to "EVMYulLean's execution model matches the EVM" (backed by upstream Ethereum conformance tests) when builtin dependencies are fully proven. Expressions or statements using smod/sar still inherit the local sorry-backed bridge assumptions until those core equivalences are discharged.
- **Fork dependency**: Verity pins [`lfglabs-dev/EVMYulLean`](https://github.com/lfglabs-dev/EVMYulLean), a fork of [`NethermindEth/EVMYulLean`](https://github.com/NethermindEth/EVMYulLean). The pinned commit is recorded in `lake-manifest.json` under the `evmyul` package. The exact divergence from upstream is enumerated in [`artifacts/evmyullean_fork_audit.json`](artifacts/evmyullean_fork_audit.json), regenerated by `scripts/generate_evmyullean_fork_audit.py` and validated by `make check`. As of the current pin, the fork is 2 commits ahead of `upstream/main` and 0 behind; both commits are non-semantic (one visibility change on an exponentiation accumulator, one Lean 4.22.0 deprecation fix), so upstream Ethereum conformance test coverage applies transitively.
- **Remaining gaps for whole-program retargeting**: (a) 2 bridge lemmas use `sorry` (smod, sar) — blocked by complex Int↔UInt256 sign/bit semantics, not privacy. (b) Body closure is only proved for scalar/static-scalar calldata parameter prologues and mixed pure-binding/single-slot `setStorage`/`require`/terminator fragments; full compiler-produced IR function/entrypoint bodies still need `BridgedStmt` closure. (c) No Layer-3-composed theorem yet connects IR → Yul under `.evmYulLean`.
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
- **Mitigation**: The generic Layer 2 whole-contract theorem, macro-generated `_semantic_preservation` body-alignment checks, and differential tests catch divergence on the current contract set.

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
2. Review [AXIOMS.md](AXIOMS.md); ensure the axiom list is unchanged and justified.
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

**Last Updated**: 2026-04-15
**Maintainer Rule**: Update on every trust-boundary-relevant code change.
