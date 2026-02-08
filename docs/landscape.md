# Research Landscape (Current State)

## Specification & Runtime Verification

- Scribble transforms specification annotations into concrete Solidity assertions for runtime checking; it is designed to integrate with testing, fuzzing, or symbolic execution rather than replace implementations.

## Formal Verification (Contract-Level)

- Certora Prover verifies Solidity contracts against rules and invariants written in CVL.
- Solidity SMTChecker uses BMC and CHC model-checking engines and can prove or refute `assert`-based properties.
- The SMTChecker’s BMC engine analyzes functions in isolation, while CHC models system-level behavior across transactions.

## Semantics-Based Verification

- KEVM (K Framework) provides a formal EVM semantics and proof tooling; it is a rigorous foundation but heavier-weight than most developer workflows.

## Fuzzing / Invariant Testing (Practical Assurance)

- Echidna is a property-based fuzzer that searches for sequences of calls that violate user-defined invariants.
- Foundry’s invariant testing executes randomized call sequences and asserts invariants after each call.

## Implications for Dumb Contracts

1. The dominant workflow is still “verify implementation against properties,” not “spec-first validation of transitions.”
2. Spec languages exist, but they are typically embedded in Solidity or tightly coupled to implementation semantics.
3. A minimal DSL that compiles to constraints is still missing from mainstream workflows.

## Sources (Quick Links)

```text
https://docs.soliditylang.org/en/latest/smtchecker.html
https://docs.scribble.codes/
https://docs.certora.com/en/latest/docs/cvl/invariants.html
https://github.com/runtimeverification/evm-semantics
https://github.com/crytic/echidna
https://learnblockchain.cn/docs/foundry/i18n/en/forge/invariant-testing.html
```
