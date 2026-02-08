# Formal Approach Sketch

This document proposes a stronger proof path for the dumb-contracts DSL.
The key idea is to separate a small Spec IR from the DSL surface syntax and
prove that a checker for the IR is sound.

## Proposed Architecture

1. DSL -> Spec IR
   - Parse into a minimal IR: requires, ensures, modifies, invariants.
   - Remove all syntax sugar and hints before proof.

2. Spec IR Semantics (Lean)
   - Define a formal semantics for transitions on a contract state.
   - Use Lean to state and prove properties about the IR.

3. Verified Checker
   - Implement a checker that decides whether a (pre, post) state pair
     satisfies the IR.
   - Prove in Lean: if checker accepts, the IR semantics hold.

4. Bridging to Solidity
   - The current bridge is a generated Solidity harness with asserts.
   - A stronger future bridge is to generate proof obligations for a
     semantics-level EVM tool (KEVM/K or Act/hevm).

## Why This Is Better

- The DSL can evolve without expanding the proof surface.
- We get a formal guarantee for the IR checker, independent of the compiler.
- We can use multiple backends (SMTChecker, Kontrol, hevm, KEVM) to
  validate or prove transitions.

## Next POC Targets

- Implement a Spec IR encoder (JSON) and emit it from the DSL compiler.
- Add a minimal Lean model (see research/spec_ir_lean/SpecIR.lean).
- Add a toy checker in Solidity or Python and connect it to the IR.
