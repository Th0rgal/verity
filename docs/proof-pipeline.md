# Proof Pipeline (POC)

This repository's first proof path focuses on a minimal, auditable flow:

1. **DSL spec** in `specs/*.dc`.
2. **Constraint harness** generated into `src/*SpecHarness.sol`.
3. **Formal check** via `solc` SMTChecker (CHC engine) on the harness contract.
4. **Unit tests** in `test/` to validate concrete behavior.

The goal is a small, reliable pipeline that can be extended as the DSL grows.

Generation now uses a manifest (`specs/manifest.txt`) so new specs can be added without editing scripts.

Note: deliberate negative cases (e.g., `BrokenSimpleToken`, `BrokenCappedToken`) are exercised in tests to demonstrate harness failures and are not included in SMTChecker runs.

Quantified invariants are approximated with witness parameters for now (see `SimpleTokenWitness`), keeping the SMTChecker inputs quantifier-free while still capturing the "all other accounts unchanged" intent. The DSL supports a `forall` witness line that expands into a `require` + `assert` pair in the harness.

## Next Proof Track (Lean-Backed Spec IR)

We are sketching a formal path where the DSL compiles into a small Spec IR with
well-defined semantics in Lean. The goal is to prove a checker for this IR is
sound, then connect the checker to the generated Solidity harness (or a future
EVM-level proof).

Sketch artifacts live in `research/spec_ir_lean/` as a starting point.
