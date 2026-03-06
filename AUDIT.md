# AUDIT

## Architecture & trust boundaries

Components and flow:
1. `Verity/*` EDSL contracts and logical specs (`Prop`).
2. `Compiler/CompilationModel.lean` validates and lowers `CompilationModel` to IR.
3. `Compiler/Codegen.lean` lowers IR to Yul AST.
4. `Compiler/Yul/PrettyPrint.lean` renders Yul text.
5. `solc` compiles Yul to EVM bytecode.
6. The AST compiler backend (`--ast`) has been removed; the active path is `CompilationModel`.

Trust changes:
1. Lean proofs stop at generated Yul; `solc` correctness is trusted.
2. Selector hashing includes a documented keccak axiom (see `AXIOMS.md`).
3. Linked external Yul libraries are trusted TCB code.
4. CI scripts consume repo/workspace files as untrusted input and must validate format before use.

## Security model

Threat assumptions:
1. Adversary may submit malformed source/contracts/docs/artifacts through PRs.
2. CI runners execute checks on attacker-controlled branch contents.
3. Deployers use the proof-backed CompilationModel path (CompilationModel).

Access control and checks:
1. Solidity runtime access control is contract-specific and tested in Foundry suites under `test/`.
2. Build/verification gate is deny-by-default: CI fails on invariant drift (selectors, storage layout, docs/proof counts, property coverage, warning regressions).
3. `scripts/workflow_jobs.py` centralizes top-level `jobs:` parsing (quoted and unquoted keys) for workflow-sync checkers, so cross-job boundary extraction is explicit and shared.
4. `scripts/check_lean_warning_regression.py` validates baseline schema/invariants and fails on mismatch. Uses `type(value) is not int` to reject booleans, raises `ValueError` on malformed UTF-8 log input, and validates `by_file`/`by_message` counter fields strictly.
5. `scripts/verification_metrics.py` uses `_expect_int` with `type(value) is not int` to reject booleans in integer metric fields.
6. `scripts/check_verify_sync.py` is the unified table-driven validator for all workflow invariants (job order, commands, path filters, foundry settings, artifact producers), driven by `scripts/verify_sync_spec.json`.
7. `scripts/check_compiler_boundaries.py` includes builtin-list sync checks that strip Lean comments before `def` extraction, preventing comment-decoy bypass.
8. `scripts/check_solc_pin.py` collects all `SOLC_*` matches via `finditer` and fails on conflicting values across occurrences.
9. `scripts/check_yul.py` uses `scrub_lean_code` to strip comments and string literals before builtin-boundary checks.
10. `scripts/check_compiler_boundaries.py` uses `scrub_lean_code` to strip comments and string literals before mapping-slot boundary checks.
11. `scripts/check_compiler_boundaries.py` detects non-literal builtin dispatch patterns and reports them as fail-closed diagnostics.
12. `Compiler/CompilationModel.lean` recursive validation walkers for unsafe logical call-like detection, array-element usage detection, return/revert reachability, and bind-name collection are totalized (`def` + explicit `termination_by`), reducing reliance on `partial def` in the active compilation path.
13. `Compiler/CompilationModel.lean` additionally totalizes dynamic-parameter scope checks, statement read/write analysis, and statement-list validator walkers (`validateStmtParamReferences`, `validateReturnShapesInStmt`, `validateNoRuntimeReturnsInConstructorStmt`, `validateCustomErrorArgShapesInStmt`) with explicit structural recursion.
15. `Compiler/CompilationModel.lean` further totalizes all Expr/Stmt validation walkers: scoped-identifier validation (`validateScopedExprIdentifiers`, `validateScopedStmtIdentifiers`, `validateScopedStmtListIdentifiers`), interop validation (`validateInteropExpr`, `validateInteropStmt`), internal-call-shape validation (`validateInternalCallShapesInExpr`, `validateInternalCallShapesInStmt`), external-call-target validation (`validateExternalCallTargetsInExpr`, `validateExternalCallTargetsInStmt`), and event-argument-shape validation (`validateEventArgShapesInStmt`) with explicit structural recursion in mutual blocks.
16. `Verity/Macro/Translate.lean` supports explicit `getMappingUint`/`setMappingUint` forms for `Uint256 -> Uint256` storage fields with fail-closed typed diagnostics (`Address` mappings must use `getMapping`/`setMapping`).
17. `Verity/Macro/Bridge.lean` emits per-function `_semantic_preservation` theorem skeletons for macro-generated contracts.
18. `Compiler/Proofs/EndToEnd.lean` composes Layer 2 (CompilationModel→IR) and Layer 3 (IR→Yul) preservation theorems into a single end-to-end result. All 5 universal pure arithmetic bridge theorems proven (add/sub/mul via `Nat.add_mod`/`Nat.mul_mod`/`omega`; div/mod via `Fin.div`/`Fin.mod` unfolding + in-range preconditions).
19. Primitive/algebraic bridge facts needed by semantic hardening are now carried by `Compiler/Proofs/EndToEnd.lean` and `Compiler/Proofs/SemanticBridge.lean` and reused by composed EDSL→IR→Yul proofs.
20. `Compiler/Proofs/SemanticBridge.lean` states the target EDSL≡compiled-IR theorems for SimpleStorage (store, retrieve), Counter (increment, decrement, getCount), Owned (getOwner, transferOwnership), SafeCounter (increment, decrement, getCount), and OwnedCounter (getCount, getOwner, increment, decrement, transferOwnership) and attempts full discharge via direct `simp` unfolding of both EDSL and IR execution — no `sorry` in these proofs. Owned demonstrates Address-typed storage encoding; SafeCounter demonstrates success/revert case-split for checked arithmetic; OwnedCounter demonstrates mixed-type multi-slot encoding and access control composition. Additionally, composed EDSL→IR→Yul end-to-end proofs for SimpleStorage (store, retrieve) and Counter (increment) chain the EDSL≡IR proofs with Layer 3 preservation.

Crypto choices:
1. Function selectors use keccak256 (Ethereum ABI standard interoperability requirement).
2. Mapping slot addressing follows standard keccak-based EVM storage scheme.
3. No custom cryptography is introduced in this repo.

## Design decisions

1. Single compiler front-end (`CompilationModel`/`CompilationModel`); AST backend was removed after migration completed.
2. Use many small explicit CI check scripts rather than one opaque mega-check; each guard maps to one invariant and one failure reason.
3. Keep warning-regression baseline as checked JSON artifact for deterministic CI behavior; validate schema strictly to avoid silent acceptance of malformed data.
4. Prefer generated artifacts and sync checks over handwritten counts/metadata to reduce review-time ambiguity.

## Known risks

1. `solc` is trusted and outside Lean proof scope.
2. The AST compiler backend has been removed; only the `CompilationModel` path is active.
3. Linked external Yul libraries remain trusted dependencies and must be audited separately.
4. Gas bounds are engineering checks, not semantic security proofs.

## External dependencies

1. `solc`: trusted compiler from Yul to EVM bytecode.
2. Foundry (`forge`/`anvil` tooling): trusted test harness/runtime for Solidity tests.
3. Lean toolchain (`lake`, Lean compiler): trusted proof checker and build runtime.
4. Python 3 standard library scripts: trusted CI execution environment; scripts validate untrusted file inputs where used.

## Attack surface

External input entry points:
1. CLI/compiler inputs and contract sources (`Verity/*`, `Compiler/*`).
2. Foundry test inputs, calldata/value fuzzing, and FFI-enabled differential/property test harnesses (`test/*`).
3. CI/workflow-consumed files and generated artifacts (`artifacts/*.json`, docs tables, manifests, gas reports, logs).
4. Newly hardened boundary: `artifacts/lean_warning_baseline.json` consumed by `scripts/check_lean_warning_regression.py`.

Primary review focus:
1. Selector/ABI drift (`Compiler/Selector.lean`, `Compiler/Selectors.lean`, `scripts/check_selectors.py`).
2. Storage slot/type drift across layers (`scripts/check_storage_layout.py`).
3. Cross-path output drift and Yul compileability (`scripts/check_yul.py`).
4. Contract access-control/property behavior (`test/Property*.t.sol`, `test/Differential*.t.sol`).
