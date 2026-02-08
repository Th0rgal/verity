# Research Log

This log captures decisions, questions, and short summaries as we progress.

## 2026-02-08

- Initialized repository and scaffolding.
- Recorded initial problem framing and MVP scope from the draft.
- Next: produce a literature / tooling landscape scan and outline DSL design constraints.
- Added `STATUS.md` and initial roadmap.
- Added landscape scan notes (Scribble, Certora, SMTChecker, KEVM, Echidna, Foundry invariants).
- Built a minimal DSL-to-Solidity POC generator and example spec.
- Added Foundry-based POCs with unit tests for two goal scenarios: token transfer state-diff validation and a health-factor invariant.
- Captured scenario goals in `docs/scenarios.md` and wired CI to run tests.

- Added a minimal DSL -> constraint harness compiler and a health-factor scenario.
- Added SMTChecker-based proof step in CI using a Solidity spec harness.
- Added `Loan` implementation + `LoanSpecHarness` and unit tests.
