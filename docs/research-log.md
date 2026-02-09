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
- Extended the DSL compiler with `constructor(...)`, `require:`, and `old(...)` support.
- Added `SimpleToken` + `SimpleTokenSpecHarness` with unit tests for pre/post constraints.
- Extended the DSL compiler to accept multiple `ensure:` lines and named `invariant` assertions.
- Regenerated spec harnesses for `SimpleToken` and `Loan` with multi-assert output.
- Added `MintableToken` scenario + spec harness + unit tests to cover access-control constraints.
- Refreshed the tooling landscape with updated references (SMTChecker, Scribble, Certora, KEVM, Echidna, Foundry invariants).

## 2026-02-08 (Later)

- Added a capped-mint scenario (`CappedToken`) with a cap invariant and preconditions.
- Generated `CappedTokenSpecHarness` and added unit tests covering happy path, non-owner, and cap-exceeded cases.
- Extended SMTChecker script to include Mintable + Capped harnesses.
- Refreshed the landscape summary with current source links.

## 2026-02-08 (Current)

- Added a negative proof case with a deliberately broken transfer implementation.
- Added `BrokenSimpleToken` + `BrokenSimpleTokenSpecHarness` and a unit test that expects assertion failure.
- Added a new goal scenario for the negative proof case.
- Updated the DSL generator script to include the new spec harness.
- Began refreshing the research landscape with current documentation sources.

## 2026-02-08 (Later)

- Added a second negative proof case for cap invariants.
- Added `BrokenCappedToken` + `BrokenCappedTokenSpecHarness` and a unit test expecting assertion failure.
- Installed Docker tooling; daemon startup fails in this VM due to missing devices cgroup.
- Added clearer SMTChecker script messaging when the Docker daemon is unavailable.
- Installed Foundry toolchain and ran the full test suite.

## 2026-02-08 (Current)

- Added `hint:` metadata support in the DSL and emitted it as harness comments.
- Introduced a spec manifest (`specs/manifest.txt`) and updated the generator to consume it.
- Updated the proof pipeline and scenarios documentation for the new metadata/manifest flow.
- Refreshed the landscape summary with current documentation links.

## 2026-02-08 (Later)

- Added a witness-based transfer scenario to approximate "forall other accounts" without quantifiers.
- Added `SimpleTokenWitness` + spec harness + unit tests for the witness constraint.
- Updated the manifest and proof pipeline notes for the witness approach.

## 2026-02-08 (Later)

- Added a `forall` witness line to the DSL that expands into a `require` + `assert` pair in the harness.
- Updated `SimpleTokenWitness` spec to use the `forall` syntax and regenerated the harness.
- Updated docs to reflect the witness-based quantifier intent feature.

## 2026-02-08 (Current)

- Sketched a Lean-backed Spec IR path in `research/spec_ir_lean/` (minimal semantics + checker interface).
- Updated the proof pipeline to include the Lean-backed Spec IR track as the next formal step.
- Refreshed the tooling landscape with Act and Kontrol references.
- Added `docs/formal-approach.md` with a Spec IR + Lean + EVM-bridge plan.

## 2026-02-08 (Later)

- Expanded the Lean-only prototype in `research/lean_only_proto/` with a mint example.
- Added `mintSpec` + `mint_sound` proof to show a second, DSL-free spec/implementation proof.

## 2026-02-08 (Current)

- Added a Lean-only lending state model (`LState`) with collateral, debt, and `minHealthFactor`.
- Implemented Euler-style health factor invariant (`collateral >= debt * minHealthFactor`).
- Added Lean specs and proofs for `borrow`, `repay`, and `withdraw` and showed each preserves the invariant.
- Added a minimal ABI dispatcher stub (selector + calldata loads) to the Lean -> Yul compiler output.
- Validated the generated Yul with `solc --strict-assembly`.

## 2026-02-08 (Lean-Only Focus)

- Refocused the repo on a Lean-first spec/impl/proof workflow.
- Updated the formal approach, proof pipeline, and agenda to remove DSL-first framing.
- Added a Lean-first roadmap with a compiler path to Yul/EVM as the end goal.
- Marked the DSL/SMT POCs as legacy while keeping them for reference.

## 2026-02-08 (Lean-Only Compiler)

- Added a Lean contract core module with storage, balances, logs, and generic `Spec`.
- Added a tiny Lean AST subset and a compiler to a minimal Yul AST.
- Implemented a Yul pretty-printer and a Lean executable that emits `out/example.yul`.
- Added scripts to generate Yul and run `solc --strict-assembly` checks.

## 2026-02-08 (Lean-Only Compiler Continued)

- Added a Lean AST operational semantics module (`DumbContracts.Semantics`) with Env + storage evaluation.
- Added `updateStr` helpers in the core for environment updates.
- Updated the Lean -> Yul compiler output to include a top-level `stop()`.
- Added a `solc` installer script and installed a static solc binary for strict-assembly checks.
- Refreshed the research landscape and roadmap to reflect the Lean AST semantics step.

## 2026-02-08 (Return Data)

- Added 32-byte return-data encoding in the Lean -> Yul compiler (`mstore` + `return`).
- Updated the Yul example entry to `getSlot`, returning a storage word.
- Refreshed landscape notes with up-to-date Yul/via-IR/Lean/Act/KEVM references.

## 2026-02-09 (Semantics + Calldata)

- Extended the Lean AST semantics to model calldata and return data.
- Added `calldataload` to the Lean AST and compiler surface.
- Added a small executable semantics example showing `getSlot` returns the storage word.

## 2026-02-09 (Multi-Entry Codegen)

- Added multi-entry codegen with a selector table for `getSlot` + `setSlot`.
- Added a `setSlot` semantics example and proof.
- Confirmed the generated Yul compiles under `solc --strict-assembly`.
