# Research Landscape (Current State)

## Specification & Runtime Verification

- Scribble (ConsenSys Diligence) provides a specification language that annotates Solidity with properties, then translates them into runtime assertions. It is oriented toward testing and fuzzing rather than full formal verification.
  - https://diligence.security/scribble/
  - https://consensys.io/blog/introducing-scribble-by-consensys-diligence

## Formal Verification (Contract-Level)

- Certora Prover uses its own CVL (Certora Verification Language) to specify properties and prove them against EVM contract code. It is a leading industrial formal verification tool for smart contracts.
  - https://docs.certora.com/

- Solidity SMTChecker (built into `solc`) provides model checking capabilities, including property verification, CHC/BMC engines, and inferred invariants. It is tied to Solidity and has known unsupported constructs.
  - https://docs.solidity.org/en/latest/smtchecker.html

## Semantics-Based Verification

- KEVM (K Framework) models EVM semantics and supports symbolic execution and proof-oriented verification. It underpins a body of verified contracts and provides a semantic ground truth for EVM behavior.
  - https://github.com/runtimeverification/evm-semantics
  - https://docs.runtimeverification.com/kevm

## Fuzzing / Invariant Testing (Practical Assurance)

- Echidna is a widely used property-based fuzzer that checks invariants expressed as Solidity functions.
  - https://github.com/crytic/echidna

- Foundry invariant testing provides randomized call sequences and invariant checks inside the Forge test framework.
  - https://learnblockchain.cn/docs/foundry/i18n/en/forge/invariant-testing.html

## Implications for Dumb Contracts

1. Existing tools center on verifying *implementations* against properties, not on enforcing state-diff rules for variable ownership.
2. Most systems assume the contract code defines the transition function; “dumb contracts” invert this by letting external parties propose state diffs with proofs.
3. Quantifiers and global invariants remain expensive or require off-chain proof systems; DSL design should treat these as first-class but likely off-chain obligations.
4. Tooling gaps: a spec-first DSL that compiles to verifiable transition checkers is not a mainstream workflow today.
