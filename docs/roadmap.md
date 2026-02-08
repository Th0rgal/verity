# Roadmap (Lean-Only)

## Goal

Write very small specs in Lean, implement them in Lean, prove correctness, and
compile to valid Ethereum bytecode (via Yul) with a semantic preservation story.

## Milestone 1: Lean Contract Core

- Define a minimal contract state model (storage maps, balances, events/logs).
- Define msg context (sender, value, block) and execution context.
- Add reusable lemmas for frame conditions and invariants.

## Milestone 2: Spec/Impl/Proof Library

- Provide a small library of spec combinators (requires, ensures, modifies).
- Provide proof helpers for common patterns (transfer, mint, borrow/repay).
- Extend the Lean-only prototype to cover the token and lending examples.

## Milestone 3: Lean -> Yul Compiler Skeleton

- Define a small Lean AST subset for implementations (arithmetic, maps, conditionals).
- Define a Yul AST and a pretty-printer.
- Emit Yul and compile it with `solc --strict-assembly`.

## Milestone 4: Semantic Preservation (Subset)

- Prove correctness for the initial subset (arith + map updates + if/else).
- Validate with small end-to-end examples (transfer, mint, borrow).

## Milestone 5: Expand Coverage

- Add events/logs and error/revert handling.
- Add loops and bounded quantifiers.
- Expand the Yul subset until it covers the example suite.

## Milestone 6: EVM-Level Anchoring (Optional)

- Connect to an EVM semantics framework (e.g., KEVM/Act) for stronger guarantees.
