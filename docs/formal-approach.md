# Formal Approach (Lean-Only)

This repository is now centered on a Lean-only specification workflow.
The DSL-to-checker track is no longer the primary plan. Instead, we
write specs and implementations directly in Lean, prove correctness
in Lean, and compile the implementation to Yul (or EVM bytecode).

## Proposed Architecture

1. Lean Spec + Impl + Proof
   - Specs are Lean predicates on pre/post state.
   - Implementations are Lean functions over state.
   - Proofs connect each implementation to its spec.

2. Lean Contract Core
   - A minimal state model with storage maps, events, and msg context.
   - A small-step semantics for the Lean contract core.
   - Re-usable lemmas for frame conditions and invariants.

3. Lean -> Yul Compiler
   - Define a Lean AST subset for implementations.
   - Compile to a Yul AST and then to Yul source.
   - Use `solc --strict-assembly` to validate Yul output.

4. Semantic Preservation
   - Prove that the Yul code preserves the Lean semantics for the subset.
   - Expand the subset iteratively until it covers target examples.

## Why This Is Better

- Specs and proofs are written in the same language as the implementation.
- The proof surface is small and explicit; there is no DSL-to-proof mismatch.
- The compiler can be verified incrementally as the subset grows.

## Next POC Targets

- Add a Lean "contract core" module and port the token + lending examples.
- Define the initial Lean AST subset and a Yul printer.
- Prove the first end-to-end lemma for arithmetic + map updates.
