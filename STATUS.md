# Status

Last updated: 2026-02-08

## Current Focus

- Keep the DSL compiler minimal while emitting constraints we can formally prove.
- Maintain reliable unit tests for each "goal scenario" and run them in CI.
- Prioritize spec-to-constraints and formal proof (diff validation is out of scope for now).
- Define a Spec IR and a Lean-backed proof track for a sound checker.
- Build out a Lean-only prototype to validate a DSL-free proof path.

## In Progress

- Establish a proof pipeline: DSL -> constraint harness -> SMTChecker.
- Add bounded scenarios that avoid quantifiers but still exercise `old(...)` and preconditions.
- Prototype a failure case that demonstrates SMTChecker catching a violated constraint.
- Explore quantified invariants as off-chain proof obligations.
- Preserve implementation hints as metadata while keeping constraints minimal.
- Extend the DSL with a quantifier-intent syntax that compiles into witness-based constraints.
- Define a Spec IR and formal semantics as a Lean sketch (prove checker soundness).

## Completed

- Repository scaffolding and initial draft capture.
- DSL-to-Solidity skeleton for a token transfer spec.
- POC contracts and tests for two goal scenarios (token transfer, health factor).
  - Note: diff validation is no longer the focus for the next phase.
- Minimal DSL -> constraint harness compiler and a health-factor scenario.
- SMTChecker-based proof step in CI using a Solidity spec harness.
- `Loan` implementation + `LoanSpecHarness` and unit tests.
- `SimpleToken` + `SimpleTokenSpecHarness` with `old(...)` capture and preconditions.
- DSL compiler now supports multiple `ensure:` lines and named `invariant` assertions.
- `MintableToken` + `MintableTokenSpecHarness` with owner-only mint constraints and unit tests.
- `CappedToken` + `CappedTokenSpecHarness` with cap invariants and unit tests.
- Extended SMTChecker coverage to include mint scenarios (Mintable + Capped).
- Added negative proof case with `BrokenSimpleToken` + spec harness + unit test expecting assertion failure.
- Added a new scenario for negative proof cases.
- Added negative proof case with `BrokenCappedToken` + spec harness + unit test expecting assertion failure.
- Installed Docker tooling; daemon startup currently blocked by missing devices cgroup in this VM.
- Installed Foundry toolchain and ran the full test suite locally.
- Refreshed the tooling landscape with up-to-date references and source links.
- Added `hint:` metadata to the DSL and emitted it into generated harness comments.
- Added a spec manifest (`specs/manifest.txt`) and updated the generator script to consume it.
- Added `SimpleTokenWitness` + spec harness + tests to model "forall other accounts unchanged" via a witness parameter.
- Added `forall` witness syntax to the DSL that compiles into a `require` + `assert` pair.
- Updated `SimpleTokenWitness` spec and regenerated its harness to use the `forall` syntax.
- Sketched a Lean-backed Spec IR path in `research/spec_ir_lean/`.
- Updated proof pipeline notes to include the Lean-backed Spec IR track.
- Refreshed the tooling landscape with Act and Kontrol references.
- Added `docs/formal-approach.md` with a Spec IR + Lean + EVM-bridge plan.
- Expanded the Lean-only prototype with a mint spec + proof.

## Next

- Expand the DSL compiler to cover Scenario A without quantifiers (forall accounts as an off-chain obligation).
- Add SMTChecker coverage for additional scenarios and edge cases.
- Keep adding minimal failure cases to validate proof tooling behavior.
- Prototype a Spec IR -> checker generator (Solidity or another DSL) that can be proved sound in Lean.
