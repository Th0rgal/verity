# Rewrite Rules (Groundwork)

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the target authoring model for proof-carrying Yul subtree rewrites.

## Status

Partially implemented:
1. `ExprRule` (as `ExprPatchRule`) is active in the deterministic patch engine.
2. `StmtRule` (as `StmtPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
3. `BlockRule` (as `BlockPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
4. `ObjectRule` (as `ObjectPatchRule`) is now supported in the patch engine with the same fail-closed metadata gate.
5. Codegen now runs a two-stage typed rewrite pipeline:
   - runtime-scoped fixpoint pass for `ExprRule`/`StmtRule`/`BlockRule`;
   - object pass for `ObjectRule`.
   Foundation packs for `StmtRule`/`BlockRule`/`ObjectRule` are wired but currently empty.
6. Rule activation now supports pack-scoped allowlists (`packAllowlist`) checked against `RewriteCtx.packId`.
7. Patch execution now supports activation-time proof registry enforcement via `PatchPassConfig.requiredProofRefs`.
   In compiler codegen, this defaults to the selected rewrite bundle proof allowlist, so rules with unregistered `proofId` fail closed even if metadata is non-empty.
8. Rewrite bundles are now explicit and versioned (`foundation`, `solc-compat-v0`), with bundle selection propagated by `PatchPassConfig.rewriteBundleId`.
   Object rules are now applied sequentially in deterministic priority order within each object-pass iteration (instead of first-match only), enabling chained compat transforms in one iteration.
   `solc-compat-v0` now includes compatibility-only object rules:
   - `solc-compat-canonicalize-internal-fun-names`: canonicalizes `internal__*` helper names to `fun_*` and rewrites in-object call sites deterministically.
   - `solc-compat-inline-dispatch-wrapper-calls`: inlines runtime dispatch case bodies of the form `fun_*()` to the referenced top-level zero-arity helper body.
   - `solc-compat-inline-mapping-slot-calls`: inlines runtime `mappingSlot(baseSlot, key)` expression calls by materializing helper-equivalent scratch writes (`mstore(512, key)`, `mstore(544, baseSlot)`) plus `keccak256(512, 64)` into fresh collision-safe temporaries.
   - `solc-compat-inline-keccak-market-params-calls`: inlines direct runtime `keccakMarketParams(...)` helper calls into explicit `mstore`/`keccak256` sequences.
   - `solc-compat-rewrite-elapsed-checked-sub`: rewrites runtime `sub(timestamp(), prevLastUpdate)` expressions to `checked_sub_uint256(timestamp(), prevLastUpdate)` and materializes a Solidity-compatible `checked_sub_uint256` helper only when referenced and absent.
   - `solc-compat-rewrite-accrue-interest-prologue-temps`: rewrites the canonical two-arg runtime `fun_accrueInterest(var_marketParams_46531_mpos, var_id)` compat prologue (`mstore(512, var_id)`, `mstore(544, 3)`, compat slot-0 elapsed check) into Solidity-style `_1.._5` scratch-slot temp bindings, with strict shape guards and skip-on-collision behavior when `_1.._5` are already locally bound.
   - `solc-compat-rewrite-accrue-interest-irm-guard`: rewrites runtime `if iszero(eq(mload(add(var_marketParams_*, 96)), 0))` guards to Solidity-style masked `cleaned` guards (`let cleaned := and(..., addressMask)` + `if iszero(iszero(cleaned))`) under compat pointer-name guards, without changing helper insertion behavior.
   - `solc-compat-rewrite-accrue-interest-checked-arithmetic`: composite rule that rewrites the `accrueInterest` function body to match Solidity's checked-arithmetic output. All sub-rewrites use suffix-safe name guards and deterministic matching. The rule performs:
     1. **Arithmetic → checked helpers**: selected expressions rewritten to `checked_add_uint256`, `checked_add_uint128`, `checked_sub_uint128`, `checked_mul_uint256`, `checked_div_uint256`, and canonical `fun_toSharesDown(...)` callsites.
     2. **Packed slot writes**: upper-uint128 slot writes canonicalized to `update_storage_value_offsett_uint128_to_uint128(slot, value)` under name-shape guards.
     3. **Fee arithmetic**: fee-denominator subtraction and fee-share accumulation rewritten to checked uint128 helpers with `fun_toUint128(...)` casts.
     4. **Timestamp guard**: `if gt(timestamp(), prevLastUpdate_*)` rewritten to `checked_sub_uint256(...)` + early `leave`.
     5. **Timestamp-write reordering**: guarded `__compat_value := timestamp()` + packed-slot `sstore` block moved from pre-IRM to post-IRM position under strict alias/equality guards (including `iszero(eq(irm_*, 0))` and `iszero(iszero(irm_*))` forms).
     6. **IRM call sequence**: contiguous `__ecwr_success := call(...)` + failure forwarding + `lt(returndatasize(), 32)` + `borrowRate := mload(0)` canonicalized to `finalize_allocation_27020 → finalize_allocation_27033 → finalize_allocation` prelude + `extract_returndata()` + success-gated finalize/load block using `__compat_alloc_ptr`. The full `let __compat_alloc_ptr_* := mload(64)` prelude shape is pointer-equality-guarded before helper-backed failure forwarding, with `mstore(0, mload(__compat_alloc_ptr_*))` placed after failure/returndatasize guards to match Solidity ordering.
     7. **Borrow-rate guard forwarding**: intermediate shapes rooted at `mstore(0, mload(__compat_alloc_ptr_*))` / `if iszero(__ecwr_success_*)` use the same helper-backed forwarding with pointer-temp alias equality guards.
     8. **Entry signature canonicalization**: six-argument `fun_accrueInterest` signatures (`id`/`loanToken`/`collateralToken`/`oracle`/`irm`/`lltv`, including suffixed variants) rewritten to two-argument `(var_marketParams_46531_mpos, var_id)` form with deterministic in-body identifier lowering. Guarded six-argument callsites rewritten to `fun_accrueInterest(0, id)`.
     9. **Helper materialization** (all referenced+absent-only): `fun_toUint128` chain (`require_helper_string` → `finalize_allocation_35876`), `finalize_allocation_27020/27033/finalize_allocation` and `checked_sub_uint256` from IRM normalization, `extract_returndata()` when already referenced, `update_storage_value_offsett_bool_to_bool` when `fun_accrueInterest` is present. `fun_toSharesDown` preserves Solidity-style `checked_div_uint256(checked_mul_uint256(...), sum_1)` form.
     Suffix-safe temporaries: `newTotalSupplyAssets_*`, `feeAmount_*`, `feeDenominator_*`, `totalSupplyShares_*`, `feeShares_*`, `prevLastUpdate_*`, `__compat_alloc_ptr_*`, `__ecwr_success_*`.
   - `solc-compat-rewrite-nonce-increment`: rewrites runtime `add(currentNonce, 1)` expressions to `increment_uint256(currentNonce)` and materializes a Solidity-compatible `increment_uint256` helper only when referenced and absent.
   - `solc-compat-prune-unreachable-deploy-helpers`: prunes deploy top-level helpers that are unreachable from non-function deploy statements, while leaving runtime code unchanged.
   - `solc-compat-drop-unused-mapping-slot-helper`: drops top-level runtime `mappingSlot` helper definitions when no call sites remain.
   - `solc-compat-drop-unused-keccak-market-params-helper`: drops top-level runtime `keccakMarketParams` helper definitions when no call sites remain.
   - `solc-compat-dedupe-equivalent-helpers`: deduplicates structurally equivalent top-level helper defs and rewrites call sites to the retained canonical helper.
   `solc-compat-prune-unreachable-helpers` remains implemented and tested, but is not activated in `solc-compat-v0` by default because broad helper pruning removes `solc`-emitted helper families needed for exact function-level identity.
   `solc-compat-outline-dispatch-helpers` remains implemented and tested, but is not activated in `solc-compat-v0` by default because broad dispatch outlining introduces non-`solc` helper families on current targets.
   Runtime codegen no longer has a separate backend-profile dispatch-helper outlining path; outlining is centralized in proof-gated object rules.
9. Parity packs now require explicit pack-level proof composition metadata (`compositionProofRef`) and proof registry coverage (`requiredProofRefs`) against the selected rewrite bundle before `--parity-pack` selection is accepted.
10. Yul pretty-printing now canonicalizes switch zero-tags to `case 0` (instead of `case 0x0`) to match `solc` tokenization for function-level parity digests.

## Rule Kinds

1. `ExprRule`: expression subtree rewrites.
2. `StmtRule`: statement-level rewrites.
3. `BlockRule`: block structure rewrites (ordering/grouping/scoping).
4. `ObjectRule`: deploy/runtime object-level rewrites.

## Required Rule Fields

1. `id`: stable rule identifier.
2. `scope`: where the rule may run (`runtime`, `deploy`, `dispatcher`, `abi`, `helper(name)`).
3. `matcher`: typed precondition over target subtree plus context.
4. `rewrite`: transformed subtree.
5. `proofRef`: theorem establishing semantic preservation under matcher preconditions.
6. `deterministic`: explicit guarantee that output is stable.

## Rewrite Context (Implemented Foundation)

Rules now receive a typed `RewriteCtx` with:

1. stage scope (`runtime`, `deploy`, `object`);
2. pass metadata (phase, iteration, pack ID).

Still planned:
1. symbol table and helper registry;
2. selector map / ABI layout facts;
3. canonicalization settings.

## Safety Rules

1. Rules without `proofRef` are not activatable.
2. Rules whose `proofRef` is not in the active proof registry are not activatable.
3. Out-of-scope rewrite attempts fail closed via scope-checked `RewriteCtx`.
4. Overlapping rules must be conflict-checked.
5. Pack composition must have a theorem proving semantics preservation.

## Testing Expectations

1. Unit tests per rule (positive/negative match cases).
2. Determinism tests (repeatability).
3. Blast-radius tests (no unrelated subtree mutation).
4. Differential execution backstop between pre/post rewrite artifacts.

## Efficient Authoring Strategy (Yul Identity)

Use this rule-authoring order to maximize parity progress per change:

1. Target the active hash mismatch function first (currently `fun_accrueInterest#0`) before adding isolated helper-family rewrites elsewhere.
2. Prefer structural normalization rewrites that collapse multiple downstream helper gaps in one pass over micro-rules for single helper names.
3. Add helper materialization only as a consequence of normalized callsites, and only when referenced + absent.
4. Keep rewrites function-scoped and shape-guarded; avoid broad global rewrites that can introduce non-`solc` helper drift.
5. Preserve `onlyInVerity = 0` as a hard invariant for each parity step.

When choosing the next rule, rank candidates by:

1. Expected reduction in `hashMismatch` for the active target function.
2. Number of `onlyInSolidity` entries likely to close with one deterministic rewrite.
3. Blast-radius risk (prefer narrow matcher/scope and auditable proof obligations).

Avoid:

1. Broad runtime pruning in `solc-compat-v0` that removes Solidity-emitted helper families.
2. Outlining/introducing helper families not emitted by `solc` for the pinned tuple.
3. Unsupported-manifest edits without a corresponding proof-gated rewrite + tests.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
