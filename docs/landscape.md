# Research Landscape (Lean-Only Focus)

## Lean as the Spec + Proof Language

- Lean 4 provides a single language for specifications, implementations, and proofs.
- This removes the DSL-to-proof mismatch and keeps the proof surface explicit.

## Yul as the Compilation Target

- Yul is Solidity’s intermediate language and can be compiled to EVM bytecode.
- It is designed for readability, verification, and straightforward translation to bytecode.
- Stand-alone Yul can be compiled via `solc --strict-assembly`.
- Solidity’s “via-IR” pipeline uses Yul as the IR.

## Semantics Anchors (EVM-Level)

- KEVM provides a formal semantics for the EVM in K.
- Act is a spec language oriented around EVM state transitions with links to proof backends.

## Implications for Dumb Contracts

1. Lean-first specs and proofs can be compiled to Yul without a DSL in the loop.
2. Yul is a pragmatic compilation target with a clear path to bytecode.
3. KEVM/Act provide semantics anchors if we later want EVM-level proof alignment.

## Sources (Quick Links)

```text
https://lean4.dev/
https://docs.soliditylang.org/en/v0.8.30/yul.html
https://soliditylang.org/blog/2024/07/12/a-closer-look-at-via-ir/
https://ethereum.github.io/act/
https://github.com/runtimeverification/evm-semantics
```
