# Dumb Contracts Research (Lean-Only)

This repo now focuses on a Lean-first workflow for “dumb contracts”: write a
very small spec in Lean, write the implementation in Lean, and prove the
implementation satisfies the spec. The long-term goal is to compile the Lean
implementation to Yul (or EVM bytecode) while preserving the proof.

## What’s Here

- `research/lean_only_proto/` is the canonical prototype (specs, impls, proofs).
- `docs/roadmap.md` defines the Lean-first roadmap, including codegen to Yul/EVM.
- `docs/landscape.md` tracks relevant formal-methods tooling and semantics work.
- `STATUS.md` is the current project status and near-term plan.
- `docs/research-log.md` is the running research journal.

Legacy DSL/SMT POCs still live in `specs/`, `src/`, `test/`, and `script/`, but
they are no longer the active path.

## Quick Start (Lean)

```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
PATH=/opt/lean-4.27.0/bin:$PATH lake build
```

This builds the Lean-only prototype and checks the proofs.
