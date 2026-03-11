# Parity Packs

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the proposed structure for versioned parity packs that target exact `solc` Yul identity for pinned toolchain tuples.

## Status

**Implemented:**

| Area | What works |
|------|-----------|
| CLI | `--parity-pack <id>` selects a pack; cannot be combined with `--backend-profile` |
| Registry | Hard validation in `Compiler/ParityPacks.lean`; fails closed on unknown/ambiguous tuples |
| Patch pipeline | Two-stage typed pipeline: runtime-scoped `ExprRule`/`StmtRule`/`BlockRule` fixpoint pass, then `ObjectRule` pass over the full object |
| Rewrite bundles | `foundation` (baseline) and `solc-compat-v0` (compatibility-only rewrites); 13 active rules — see [REWRITE_RULES.md](REWRITE_RULES.md) for the full list |
| Proof enforcement | Packs carry `compositionProofRef` + `requiredProofRefs`; fail-closed validation at selection time; proof registries propagate through CLI → codegen |
| Pack metadata | `rewriteBundleId`, `metadataMode`, `patchMaxIterations` (default 6), and `RewriteCtx` scope/phase/iteration data threaded through execution |
| Yul normalization | Switch zero-tags canonicalized to `case 0` (not `case 0x0`) for tokenization-level identity comparison |
| Shipped packs | 3 pinned-solc packs (see [Implemented Packs](#implemented-packs) below); CI metric gates on `onlyInVerity`, `onlyInSolidity`, `hashMismatch` |

Two rules (`solc-compat-prune-unreachable-helpers`, `solc-compat-outline-dispatch-helpers`) are implemented and tested but intentionally inactive in `solc-compat-v0` to preserve helper families needed for function-level identity comparison.

**Not implemented:** unsupported manifest workflow.

## Purpose

`solidity-parity` currently provides deterministic shape normalization. Parity packs extend this into a versioned, auditable system:

1. select rules by pinned compiler tuple;
2. apply deterministic canonicalization and rewrites;
3. require proof artifacts for each active rewrite;
4. surface unsupported identity gaps explicitly.

## Proposed Pack Key

`solc-<version>-o<optimizerRuns>-viair-<true|false>-evm-<version>`

Example: `solc-0.8.27-o200-viair-false-evm-shanghai`

## Implemented Packs

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
