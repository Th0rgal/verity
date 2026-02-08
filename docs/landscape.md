# Research Landscape (Current State)

## Specification & Runtime Verification

- Scribble (ConsenSys Diligence) provides a spec language that annotates Solidity and instruments contracts with runtime assertions. It is meant to work with fuzzers and other analysis tools rather than replacing them.
  - https://docs.scribble.codes/
  - https://diligence.security/scribble/

## Formal Verification (Contract-Level)

- Certora Prover uses CVL (Certora Verification Language) to express rules, invariants, and method behaviors that are proven against contract implementations.
  - https://docs.certora.com/

- Solidity SMTChecker (in `solc`) provides bounded model checking and CHC-based reasoning, tied to Solidity semantics and supported constructs.
  - https://docs.solidity.org/en/latest/smtchecker.html

## Semantics-Based Verification

- KEVM (K Framework) models EVM semantics and supports proof-oriented verification with a formal EVM definition.
  - https://github.com/runtimeverification/evm-semantics
  - https://jellopaper.org/

## Fuzzing / Invariant Testing (Practical Assurance)

- Echidna is a property-based fuzzer that checks invariants expressed as Solidity functions (e.g., `echidna_*`).
  - https://github.com/crytic/echidna

- Foundry invariant testing runs randomized call sequences and asserts invariants after each call.
  - https://book.getfoundry.sh/forge/invariant-testing

## Implications for Dumb Contracts

1. Most tools verify *implementations* against properties rather than validating state diffs against a spec.
2. Spec languages exist, but they are typically embedded in Solidity or tightly coupled to implementation semantics.
3. Quantified invariants and global sums are still expensive; a “dumb contract” DSL should make off-chain obligations explicit.
4. A spec-first, state-diff validator is still not a mainstream workflow in today’s toolchain.
