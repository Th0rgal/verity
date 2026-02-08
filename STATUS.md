# Status

Last updated: 2026-02-08

## Current Focus

- Map the formal spec/verification landscape and identify gaps that “dumb contracts” can address.
- Iterate on a minimal DSL and proof-oriented execution model.

## In Progress

- Landscape scan of specification languages, verification stacks, and invariant/fuzz tools.
- Defining the MVP constraints for a DSL that remains auditable and non-Turing-complete.

## Completed

- Repository scaffolding and initial draft capture.
- POC: DSL-to-Solidity skeleton for a token transfer spec.

## Next

- Expand the DSL POC to support quantified invariants with off-chain proof obligations.
- Prototype a state-diff validation model (transition proof verifier).
- Compare compilation targets: Solidity subset vs. EVM bytecode, and collect tradeoffs.
