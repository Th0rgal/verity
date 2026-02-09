# Lean-only prototype

Start:
```bash
cd /workspaces/mission-a7986e44/dumbcontracts/research/lean_only_proto
PATH=/opt/lean-4.27.0/bin:$PATH lake build
./scripts/end_to_end.sh
```

Write a contract:
1. Add a `Fun` under `DumbContracts/Examples/` (e.g. `StoreOps.lean`).
2. Add a `Spec` or `SpecR` + proof next to it.
3. Wire the selector in `DumbContracts/Compiler.lean`.
4. Re-run `./scripts/end_to_end.sh`.

Convenience helpers:
- Small EDSL helpers live in `DumbContracts/Stdlib.lean` (`require`, `unless`, `assert`, slot helpers).

Minimal spec pattern:
```
def mySpecR : SpecR Store := { requires := ..., ensures := ..., reverts := ... }
theorem mySpec_ok : mySpecR.requires s -> ... := by ...
theorem mySpec_reverts : mySpecR.reverts s -> ... := by ...
```

Artifacts in `out/`.
