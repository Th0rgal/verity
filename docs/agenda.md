# Research Agenda (Lean-Only)

## Phase 1: Lean Spec + Impl + Proof

- Define a minimal contract state model aligned with Ethereum concepts.
- Build a tiny spec library (requires/ensures/invariants) and proof combinators.
- Prove simple token and lending examples (transfer, mint, health factor).

## Phase 2: Lean Contract Core

- Add storage maps, events/logs, and msg context to the model.
- Define a small-step operational semantics for the contract core.
- Provide re-usable lemmas for frame conditions and invariants.

## Phase 3: Lean -> Yul Compiler

- Define a Lean AST subset for implementations.
- Implement a Yul AST and pretty-printer.
- Generate Yul text for the Lean implementation subset.
- Validate output by compiling Yul with `solc --strict-assembly`.

## Phase 4: Semantic Preservation

- Prove a compiler correctness theorem for the core subset.
- Extend the subset until it covers the prototype examples.
