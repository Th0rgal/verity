# Proof Pipeline (Lean-Only)

The active proof pipeline is now:

1. **Lean spec**: `Spec` is a pre/post predicate on state.
2. **Lean implementation**: total functions on state.
3. **Lean proof**: each implementation satisfies its spec.
4. **Lean -> Yul**: compile the implementation to Yul source.
5. **Yul -> Bytecode**: compile with `solc --strict-assembly`.
6. **Compiler correctness**: prove the Lean semantics are preserved by Yul.

The Lean-only prototype lives in `research/lean_only_proto/` and provides
token and lending examples plus the proofs.

## Roadmap Snapshot

- Expand the Lean contract core (storage maps, events, msg context).
- Define a small Lean AST subset and Yul AST + printer.
- Prove semantic preservation for a tiny subset, then grow it.
