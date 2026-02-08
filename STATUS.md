# Status

Last updated: 2026-02-08

## Current Focus

- Keep the DSL compiler minimal while emitting constraints we can formally prove.
- Maintain reliable unit tests for each "goal scenario" and run them in CI.

## In Progress

- Expand the tooling landscape with up-to-date references and gaps.
- Establish a proof pipeline: DSL -> constraint harness -> SMTChecker.

## Completed

- Repository scaffolding and initial draft capture.
- DSL-to-Solidity skeleton for a token transfer spec.
- POC contracts and tests for two goal scenarios (token transfer, health factor).
  - Note: diff validation is no longer the focus for the next phase.

## Next

- Expand the DSL compiler to cover Scenario A without quantifiers.
- Add SMTChecker coverage for additional scenarios and edge cases.
- Explore quantified invariants as off-chain proof obligations.
