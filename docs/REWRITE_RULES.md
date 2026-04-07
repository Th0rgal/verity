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
8. Rewrite bundles are now explicit and versioned (currently `foundation`), with bundle selection propagated by `PatchPassConfig.rewriteBundleId`.
   Object rules are now applied sequentially in deterministic priority order within each object-pass iteration (instead of first-match only), enabling chained compat transforms in one iteration.
   Contract-specific compatibility bundles (e.g. `solc-compat-v0` for Morpho) have been extracted to external plugin packages (see `morpho-verity`). The core compiler ships only the `foundation` bundle.
   External packages register their bundles by extending `allRewriteBundles` via plugin imports.
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

1. Broad runtime pruning that removes Solidity-emitted helper families.
2. Outlining/introducing helper families not emitted by `solc` for the pinned tuple.
3. Unsupported-manifest edits without a corresponding proof-gated rewrite + tests.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
