# Proof Pipeline (POC)

This repository's first proof path focuses on a minimal, auditable flow:

1. **DSL spec** in `specs/*.dc`.
2. **Constraint harness** generated into `src/*SpecHarness.sol`.
3. **Formal check** via `solc` SMTChecker (CHC engine) on the harness contract.
4. **Unit tests** in `test/` to validate concrete behavior.

The goal is a small, reliable pipeline that can be extended as the DSL grows.
