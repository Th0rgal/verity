# Research Landscape (Current State)

## Specification & Runtime Verification

- Scribble is a runtime verification tool that transforms spec annotations into concrete assertions in Solidity.
- It is explicitly positioned to work with testing, fuzzing, or symbolic execution rather than replace implementations.

## Formal Verification (Contract-Level)

- Certora Prover verifies contracts against rules written in CVL, which supports rules and invariants.
- Solidity SMTChecker provides bounded model checking (BMC) and CHC-based reasoning via compiler options and can check `assert` targets.
- VeriSol is a Microsoft Research verifier for Solidity, but the repository notes it is no longer actively maintained.

## Semantics-Based Verification

- KEVM (K Framework) provides a formal EVM semantics and proof tooling; it is a rigorous foundation but heavier-weight than most developer workflows.

## Fuzzing / Invariant Testing (Practical Assurance)

- Property-based fuzzing and invariant tests remain practical for validating specs, but they still assume an implementation and are not spec-first.

## Implications for Dumb Contracts

1. The dominant workflow is still “verify implementation against properties,” not “spec-first validation of transitions.”
2. Spec languages exist, but they are typically embedded in Solidity or tightly coupled to implementation semantics.
3. A minimal DSL that compiles to constraints is still missing from mainstream workflows.
