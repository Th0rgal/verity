# Parity Packs

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the proposed structure for versioned parity packs that target exact `solc` Yul identity for pinned toolchain tuples.

## Status

Partially implemented:
1. CLI selection via `--parity-pack <id>`.
2. Registry + hard validation in `Compiler/ParityPacks.lean`.
3. Ambiguous selection guard (`--parity-pack` cannot be combined with `--backend-profile`).
4. Codegen now runs a typed two-stage patch pipeline:
   - runtime-scoped `ExprRule`/`StmtRule`/`BlockRule` fixpoint pass,
   - followed by `ObjectRule` pass over the full object.
   This keeps deploy rewrites explicit (object rules only) while preserving runtime patch diagnostics.
5. Verbose parity-pack logs now include `metadataMode` alongside the rest of the pinned tuple.
6. Typed `RewriteCtx` scope/phase/iteration/pack metadata is now threaded through patch execution, and rule scope is enforced at application sites.
7. `--parity-pack` now propagates into patch execution context (`PatchPassConfig.packId`), and rules can gate activation with `packAllowlist`.
8. Patch execution now supports proof registry enforcement (`PatchPassConfig.requiredProofRefs`), and codegen wires the shipped foundation packs to an explicit allowlist (`foundationProofAllowlist`).
9. Parity packs now carry explicit proof-composition metadata (`compositionProofRef`, `requiredProofRefs`) with fail-closed validation at `--parity-pack` selection time.
10. Pack proof registries now propagate through CLI → codegen patch config, with codegen defaulting to the selected rewrite bundle's proof allowlist when no explicit registry is provided.
11. Parity packs now carry `rewriteBundleId`, and `--parity-pack` selection fails closed unless that bundle exists and the pack proof registry is a deduped subset of the bundle's proof allowlist.
12. Shipped rewrite bundles now include a baseline `foundation` bundle and an explicit opt-in `solc-compat-v0` bundle boundary.
13. `solc-compat-v0` now carries compatibility-only object rewrites:
   - `solc-compat-canonicalize-internal-fun-names` for deterministic internal helper naming canonicalization (`internal__*` → `fun_*`) with in-object callsite rewrites;
   - `solc-compat-inline-dispatch-wrapper-calls` for deterministic runtime switch-case inlining from `fun_*()` wrappers to helper bodies;
   - `solc-compat-inline-mapping-slot-calls` for deterministic inlining of runtime `mappingSlot(baseSlot, key)` calls to explicit helper-equivalent scratch writes (`mstore(512, key)`, `mstore(544, baseSlot)`) plus `keccak256(512, 64)`;
   - `solc-compat-inline-keccak-market-params-calls` for deterministic inlining of direct runtime `keccakMarketParams(...)` helper calls to explicit `mstore`/`keccak256` sequences;
   - `solc-compat-rewrite-elapsed-checked-sub` for deterministic rewrite of runtime `sub(timestamp(), prevLastUpdate)` expressions to `checked_sub_uint256(timestamp(), prevLastUpdate)` with conditional top-level helper materialization when referenced and absent;
   - `solc-compat-rewrite-accrue-interest-prologue-temps` for deterministic rewrite of the canonical two-arg runtime `fun_accrueInterest(var_marketParams_46531_mpos, var_id)` compat prologue (`mstore(512, var_id)`, `mstore(544, 3)`, compat slot-0 elapsed check) into Solidity-style `_1.._5` scratch-slot temp bindings, guarded by exact-shape matching and local-name collision checks;
   - `solc-compat-rewrite-accrue-interest-irm-guard` for deterministic rewrite of runtime `if iszero(eq(mload(add(var_marketParams_*, 96)), 0))` guards to Solidity-style masked `cleaned` guards (`let cleaned := and(..., addressMask)` + `if iszero(iszero(cleaned))`) under compat pointer-name guards, without introducing new helper insertion behavior;
   - `solc-compat-rewrite-accrue-interest-checked-arithmetic` for deterministic rewrite of selected runtime `accrueInterest` arithmetic expressions to Solidity-style checked helper calls (`checked_add_uint256`, `checked_add_uint128`, `checked_sub_uint128`, `checked_mul_uint256`, `checked_div_uint256`) and canonical `fun_toSharesDown(...)` callsites, plus compat packed upper-uint128 slot write canonicalization to `update_storage_value_offsett_uint128_to_uint128(slot, value)` under guarded name-shape matching; additionally canonicalizes fee-denominator subtraction (`sub(newTotalSupplyAssets, feeAmount)`) and fee-share total-supply accumulation (`add(totalSupplyShares, feeShares)`) to checked uint128 helpers with explicit `fun_toUint128(...)` casts under suffix-safe compat guards, rewrites `if gt(timestamp(), prevLastUpdate_*)` guards to Solidity-style `checked_sub_uint256(...)` + early `leave`, and reorders the guarded compat timestamp-write block (`__compat_value := timestamp()` + packed-slot `sstore`) to Solidity-style post-IRM placement under strict alias/equality guards, including guarded `iszero(eq(irm_*, 0))` and `iszero(iszero(irm_*))` non-zero forms. It also canonicalizes the contiguous IRM call sequence (`__ecwr_success := call(...)` + failure revert forwarding + `lt(returndatasize(), 32)` + `borrowRate := mload(0)`) in one pass to a deterministic `finalize_allocation_27020 -> finalize_allocation_27033 -> finalize_allocation` prelude, `extract_returndata()` payload forwarding, and success-gated finalize/load block using `__compat_alloc_ptr`; the full prelude shape rooted at `let __compat_alloc_ptr_* := mload(64)` with aligned `finalize_allocation_27020/27033/finalize_allocation` and `call(... __compat_alloc_ptr_* ...)` is also canonicalized under suffix-safe pointer-equality guards before helper-backed failure forwarding, with deterministic post-guard placement of `mstore(0, mload(__compat_alloc_ptr_*))` to match Solidity ordering. The same helper-backed forwarding is applied to intermediate borrow-rate guard shapes rooted at `mstore(0, mload(__compat_alloc_ptr_*))` / `if iszero(__ecwr_success_*)` under suffix-safe compat guards, with deterministic pointer-temp alias equality guards (`returndatacopy`/`revert` must forward from the same local). The same rule also canonicalizes six-argument `fun_accrueInterest` entry signatures positionally (distinct `id`/`loanToken`/`collateralToken`/`oracle`/`irm`/`lltv` parameter bindings, including suffixed variants) to a Solidity-style two-argument `(var_marketParams_46531_mpos, var_id)` form with deterministic in-body identifier lowering for market params fields, and canonicalizes guarded six-argument compat callsites to `fun_accrueInterest(0, id)` under suffix-safe argument-shape guards. Conditional top-level helper materialization remains referenced+absent only, including `fun_toUint128` and its `require_helper_string` / `finalize_allocation_35876` dependencies when rewritten callsites reference them, plus `finalize_allocation_27020(memPtr)`, `finalize_allocation_27033(memPtr)`, `finalize_allocation(memPtr, size)`, and `checked_sub_uint256(x, y)` when timestamp-guard normalization introduces references, with absent-only materialization of Solidity packed-bool helper `update_storage_value_offsett_bool_to_bool` when `fun_accrueInterest` is present; `extract_returndata()` remains referenced+absent-only when already referenced in top-level call sites; `fun_toSharesDown` helper materialization preserves Solidity-style `checked_div_uint256(checked_mul_uint256(...), sum_1)` form after guarded denominator construction; includes suffix-safe matching for canonicalized temporaries (`newTotalSupplyAssets_*`, `feeAmount_*`, `feeDenominator_*`, `totalSupplyShares_*`, `feeShares_*`, `prevLastUpdate_*`, `__compat_alloc_ptr_*`, `__ecwr_success_*`);
   - `solc-compat-rewrite-nonce-increment` for deterministic rewrite of runtime `add(currentNonce, 1)` expressions to `increment_uint256(currentNonce)` with conditional top-level helper materialization when referenced and absent;
   - `solc-compat-prune-unreachable-deploy-helpers` for deterministic pruning of deploy-only top-level helper defs that are unreachable from non-function deploy statements;
   - `solc-compat-drop-unused-mapping-slot-helper` for deterministic removal of top-level runtime `mappingSlot` helper defs after call sites are eliminated;
   - `solc-compat-drop-unused-keccak-market-params-helper` for deterministic removal of top-level runtime `keccakMarketParams` helper defs after call sites are eliminated;
   - `solc-compat-dedupe-equivalent-helpers` for deterministic deduplication of structurally equivalent top-level helpers with callsite rewrites to canonical helpers.
   `solc-compat-prune-unreachable-helpers` remains implemented and tested, but is intentionally not active in `solc-compat-v0` to avoid deleting `solc`-emitted helper families needed for function-level identity comparison.
   `solc-compat-outline-dispatch-helpers` is currently kept out of the default bundle activation to avoid over-outlining runtime entry dispatch on active parity targets.
   Runtime codegen does not provide a separate backend-profile dispatch-helper outlining toggle; compat outlining is object-rule only.
   Parity packs wire `requiredProofRefs` to `solcCompatProofAllowlist`.
14. Shipped parity packs now default `patchMaxIterations` to `6` so the full object-rule sequence can execute (`canonicalize` → `inline-wrapper-calls` → `inline-mapping-slot-calls` → `inline-keccak-market-params` → `rewrite-elapsed-checked-sub` → `rewrite-accrue-interest-irm-guard` → `rewrite-accrue-interest-checked-arithmetic` → `rewrite-accrue-interest-prologue-temps` → `rewrite-nonce-increment` → `prune-unreachable-deploy-helpers` → `drop-unused-mapping-slot-helper` → `drop-unused-keccak-helper` → `dedupe`) without manual CLI overrides.
15. Yul pretty-printing now canonicalizes switch zero-tags to `case 0` (instead of `case 0x0`) so function-level hash comparison aligns with Solidity tokenization in parity reports.
16. Added pinned-solc pack `solc-0.8.33-o200-viair-false-evm-shanghai` (matching CI solc pin `0.8.33+commit.64118f21`) and CI parity-pack metric gates (`onlyInVerity`, `onlyInSolidity`, `hashMismatch`) sourced from machine-readable identity reports.

Not implemented yet:
1. unsupported manifest workflow.

## Purpose

`solidity-parity` currently provides deterministic shape normalization. Parity packs extend this into a versioned, auditable system:

1. select rules by pinned compiler tuple;
2. apply deterministic canonicalization and rewrites;
3. require proof artifacts for each active rewrite;
4. surface unsupported identity gaps explicitly.

## Proposed Pack Key

`solc-<version>-o<optimizerRuns>-viair-<true|false>-evm-<version>`

Example: `solc-0.8.27-o200-viair-false-evm-shanghai`

## Implemented Pack(s)

1. `solc-0.8.28-o200-viair-false-evm-shanghai`
2. `solc-0.8.33-o200-viair-false-evm-shanghai` (pinned-CI tuple)
3. `solc-0.8.28-o999999-viair-true-evm-paris` (Morpho-focused tuple)

## Proposed Pack Contents

1. `compat`: pinned tuple metadata (solc commit/version, flags, EVM version).
2. `rewriteBundleId`: selected typed rewrite bundle.
3. `rules`: ordered typed rewrite rule IDs.
4. `canonicalization`: deterministic naming/ordering/layout policy.
5. `proofRefs`: theorem references for each rule and pack composition.
6. `unsupported`: explicit list of known non-identity constructs.

## Lifecycle

1. Create pack for pinned tuple.
2. Run identity checker on fixture corpus.
3. Add/adjust rules until diffs are either zero or explicitly unsupported.
4. Prove per-rule semantic preservation and pack composition.
5. Gate in CI and publish support matrix.

## Recommended Execution Loop (Efficient Path)

For each parity iteration, apply this loop in order:

1. Compute machine-readable gap report and identify the top hash mismatch function.
2. Author one proof-gated, deterministic rewrite that normalizes a high-impact pattern inside that function.
3. Add/adjust rule smoke tests for positive match + rewrite.
4. Add/adjust rule smoke tests for negative/out-of-scope behavior.
5. Add/adjust rule smoke tests for wrapper-safe behavior.
6. Add/adjust rule smoke tests for helper insertion only when referenced + absent.
7. Re-run identity report and update unsupported manifest only for residual, explicitly-tracked gaps.
8. Stop if `onlyInVerity != 0`; fix drift before proceeding.

Milestone gates:

1. Gate A: eliminate active function hash mismatch (`hashMismatch = 0` for current target function set).
2. Gate B: keep `onlyInVerity = 0` across all parity steps.
3. Gate C: monotonically reduce `onlyInSolidity`.
4. Gate D: enforce unsupported manifest consistency in CI (`unsupportedManifestOk = true`).

## CI Expectations

1. Pack selection must be explicit in build/test command.
2. Identity check artifacts must be uploaded on failure.
3. Pack metadata must be printed in CI logs.
4. Unknown/ambiguous tuple selection must fail hard.

## Related

- [`SOLIDITY_PARITY_PROFILE.md`](SOLIDITY_PARITY_PROFILE.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
