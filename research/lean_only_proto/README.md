# Lean-Only Prototype

This is a Lean-only proof prototype for the "dumb contracts" idea.
There is no DSL here. The spec and implementation are written directly in Lean,
then the proof shows the implementation satisfies the spec.

What this includes
- A minimal contract core (`DumbContracts.Core`) with storage, balances, logs, and `Spec`.
- A small-step semantics for the Lean AST subset (`DumbContracts.Semantics`), including
  calldata and 32-byte return data modeling.
- Lean implementations and specs for `transfer` and `mint` with proofs.
- A lending state model (`LState`) with Euler-style health factor rules.
- Proofs that `borrow`, `repay`, and `withdraw` preserve the global health invariant.
- A tiny Lean AST (`DumbContracts.Lang`) and a compiler to Yul (`DumbContracts.Compiler`).
- A minimal Yul AST + pretty-printer (`DumbContracts.Yul`).
- A tiny executable semantics example (`DumbContracts.Examples`).

How to build (Lean installed in `/opt/lean-4.27.0`)
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
PATH=/opt/lean-4.27.0/bin:$PATH lake build
```

Generate a Yul file
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
./scripts/gen_yul.sh
```

Check with `solc --strict-assembly`
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
./scripts/check_yul.sh out/example.yul
```

Install `solc` (Linux static binary)
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
./scripts/install_solc.sh
```

Notes
- The Yul example now exposes two entry points (`getSlot`, `setSlot`) behind a
  selector-based dispatcher, exercising multi-entry codegen.
- A minimal ABI dispatcher stub is included (selector + calldata loads), but no
  complex ABI encoding is modeled yet. Return values are encoded as a single
  32-byte word at offset 0, and the Lean semantics model return data as a list
  of words (first word only for now).
- This is intentionally small and focused on proof shape, not full EVM semantics.
- The Lean->Yul pipeline will be expanded toward a proper compiler target.
