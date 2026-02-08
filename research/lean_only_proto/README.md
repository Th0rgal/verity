# Lean-Only Prototype

This is a minimal Lean-only proof prototype for the "dumb contracts" idea.
There is no DSL here. The spec and implementation are written directly in Lean,
then the proof shows the implementation satisfies the spec.

What this includes
- A minimal state model (`State`) and a `Spec` structure.
- A Lean implementation of `transfer`.
- A Lean spec (`transferSpec`) with requires/ensures and a frame condition.
- A proof (`transfer_sound`) that the implementation satisfies the spec.
- A Lean implementation of `mint` with a simple supply increase.
- A Lean spec (`mintSpec`) and proof (`mint_sound`).

How to build (if Lean is installed)
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
lake build
```

Notes
- This is intentionally small and focused on proof shape, not EVM semantics.
- It is a starting point for a Lean-first workflow and can be extended with
  additional specs, invariants, and a richer state model.
