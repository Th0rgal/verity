# Revert-State Modeling Note

Issue: [#1009](https://github.com/lfglabs-dev/verity/issues/1009)

This note clarifies a subtle but important modeling boundary:

- EVM runtime reverts are transaction-atomic: reverted writes are not externally visible.
- Verity's high-level `Contract` interpreter computes through the monadic body and applies rollback at `Contract.run`.

In other words, intermediate states can be produced during evaluation and then discarded by the final revert result.

## Why this matters

For most existing Verity proof patterns, this does not change the result because proofs are phrased over observable post-state outcomes (`success` / `revert` result at run boundary). But proofs that reason about internal intermediate states across revert boundaries can overfit to interpreter internals that EVM users cannot observe.

## Current guidance

1. Phrase contract-correctness theorems over run-boundary behavior, not internal transient states.
2. Preserve checks-before-effects discipline in contract logic.
3. Treat intermediate reverted state as an interpreter artifact, not an externally observable EVM behavior.

## Scope statement

This is a semantic caveat, not a known soundness break in currently verified contract suites. It remains part of the trust-boundary discussion for reviewers and future model hardening.
