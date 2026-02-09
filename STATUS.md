# Status

Last updated: 2026-02-09

## Current Focus

- Lean-only specs + implementations + proofs as the primary workflow.
- A minimal smart-contract state model tailored to Ethereum semantics.
- A compiler path from Lean implementation -> Yul (or EVM bytecode).
- A correctness story for the compiler (semantic preservation proofs).

## In Progress

- Prove a first semantic preservation lemma for arithmetic + storage updates.
- Add a tiny end-to-end example that compiles Lean -> Yul -> bytecode.
- Extend the Yul output with a small ABI return stub for non-`return` paths.

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
- Added a Lean-only lending model with a health factor invariant and proofs that
  borrow/repay/withdraw preserve it.
- Implemented a Lean contract core module with storage, balances, logs, and `Spec`.
- Added a Lean AST subset and a compiler to a minimal Yul AST.
- Added a Yul pretty-printer and a Lean executable that emits `out/example.yul`.
- Added scripts to generate Yul and run `solc --strict-assembly` checks.
- Added a Lean AST operational semantics module (Env + storage) for compiler proofs.
- Added a `solc` installer script and installed a static solc binary in the VM.
- Updated compiler output to include a safe top-level `stop()` in generated Yul.
- Added a minimal ABI dispatcher stub (selector + calldata loads) in the Yul output.
- Verified the generated Yul with `solc --strict-assembly`.
- Added 32-byte return-value encoding in the Lean -> Yul compiler (`mstore` + `return`).
- Switched the Yul example entry point to `getSlot` returning a storage word.
- Added calldata + return-data modeling to the Lean semantics.
- Added a tiny executable semantics example (`getSlot`) to validate the return path.
- Added multi-entry codegen with a selector table (`getSlot`, `setSlot`).
- Added a `setSlot` semantics example and proof.

## Next

- Prove the first compiler correctness lemma for the arithmetic subset.
- Add an end-to-end example that compiles a Lean implementation and checks Yul with solc.
- Add a second storage-mutating entry to stress selector collisions and slot updates.
