# Research Landscape (Current State)

## Specification & Runtime Verification

- Scribble is an annotation language + instrumentation tool that injects runtime assertions into Solidity contracts for downstream testing/analysis.
- Act is a specification language for EVM contracts with integration into hevm-based tooling.

## Formal Verification (Contract-Level)

- Certora Prover checks Solidity implementations against CVL rules/invariants.
- Solidity SMTChecker uses model-checking engines (BMC/CHC) to prove or refute `assert` properties at compile time.
- Kontrol (Runtime Verification) is a symbolic execution and formal verification toolchain for EVM smart contracts built on the K framework.

## Semantics-Based Verification

- KEVM (K Framework) provides formal EVM semantics and proof tooling, enabling semantics-level verification beyond contract-level checks.

## Proof Assistants (Spec-First)

- Lean 4 is a theorem prover and functional language suited to writing specs directly as executable math, then proving implementations satisfy them.

## Fuzzing / Invariant Testing (Practical Assurance)

- Echidna is a property-based fuzzer focused on invariant violation discovery.
- Foundry supports invariant testing with randomized call sequences and invariant checks after each step.
- Halmos provides symbolic testing for EVM bytecode with property-style checks.

## Other References

- VeriSol (Microsoft Research) is a notable historical baseline for Solidity verification and is flagged as no longer actively maintained.

## Implications for Dumb Contracts

1. The dominant workflow remains “verify implementation against properties,” not “spec-first validation of transitions.”
2. Spec languages exist, but they are typically embedded in Solidity or tightly coupled to implementation semantics.
3. A minimal DSL that compiles to constraints and feeds a formal proof backend is still missing from mainstream workflows.
4. A Lean-first track can bypass the DSL-to-proof mismatch by treating specs as proofs directly.

## Sources (Quick Links)

```text
https://docs.scribble.codes/
https://ethereum.github.io/act/
https://docs.certora.com/en/latest/docs/cvl/overview.html
https://docs.soliditylang.org/en/latest/smtchecker.html
https://docs.runtimeverification.com/kontrol/
https://docs.runtimeverification.com/kevm/
https://github.com/runtimeverification/evm-semantics
https://lean4.dev/
https://github.com/crytic/echidna
https://book.getfoundry.sh/forge/invariant-testing
https://github.com/a16z/halmos
https://github.com/microsoft/verisol
```
