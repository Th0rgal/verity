# Audit Registry

This file records trust-boundary changes and the evidence that keeps them
reviewable. Keep it synchronized with `TRUST_ASSUMPTIONS.md` and `AXIOMS.md`
whenever semantics, trusted components, generated audit artifacts, or CI
boundary checks change.

## Current Audit State

- Lean proof placeholders: 0 `sorry` in compiler/proof modules.
- Project-level Lean axioms: 0. See `AXIOMS.md`.
- Authoritative safe-body Yul runtime target: pinned `lfglabs-dev/EVMYulLean`.
- Legacy custom Yul execution files are retained as a reference oracle under
  `Compiler/Proofs/YulGeneration/ReferenceOracle/`.
- Yul-to-bytecode compilation remains trusted through pinned `solc` 0.8.33.
- Gas safety is not modeled by the semantic preservation theorems.

## Issue #1722: EVMYulLean Semantic Target

Status: full semantic integration for safe compiler-produced bodies.

The EVMYulLean transition moved the safe-body EndToEnd runtime target from
Verity's custom Yul builtin semantics to `interpretYulRuntimeWithBackend
.evmYulLean`. The current proof surface has:

- 36 of 36 builtin bridge theorems proven.
- 0 admitted bridge lemmas.
- `smod` and `sar` bridge equivalences fully discharged.
- `compileStmtList_always_bridged` proven for `BridgedSafeStmts`.
- Public `layers2_3_ir_matches_yul_evmYulLean` wrappers that derive raw
  `BridgedStmts` body witnesses from `SupportedSpec`, static parameter
  witnesses, and source-level safe-body witnesses.

The remaining scope limit is the external-call/function-table family
(`internalCall`, `internalCallAssign`, `externalCallBind`, and `ecm`). These
constructors stay outside `BridgedSafeStmts` until a function-table simulation
theorem is proved.

## Audit Artifacts

| Artifact | Purpose | Check |
|----------|---------|-------|
| `artifacts/evmyullean_adapter_report.json` | Adapter coverage, admitted bridge lemmas, safe-body integration status | `python3 scripts/generate_evmyullean_adapter_report.py --check` |
| `artifacts/evmyullean_fork_audit.json` | Pinned fork divergence and non-semantic fork delta | `python3 scripts/generate_evmyullean_fork_audit.py --check` |
| `artifacts/evmyullean_capability_report.json` | EVMYulLean capability surface and reference-oracle paths | `python3 scripts/generate_evmyullean_capability_report.py --check` |
| `PrintAxioms.lean` / generated axiom report | Axiom dependency visibility | `python3 scripts/generate_print_axioms.py --check` and `lake build PrintAxioms` |

## CI Guards

- `make check` validates generated reports, bridge coverage synchronization,
  builtin bridge matrix synchronization, Lean hygiene, proof length, and
  documentation counters.
- `make test-evmyullean-fork` validates the pinned fork audit, rebuilds the
  universal bridge lemmas, and runs the concrete bridge-equivalence tests.
- `.github/workflows/evmyullean-fork-conformance.yml` runs the EVMYulLean fork
  conformance probe weekly. During the burn-in ending 2026-05-04, failures are
  warnings; after burn-in, scheduled/manual failures open or update a GitHub
  issue and fail the workflow.

## Update Checklist

1. Update `TRUST_ASSUMPTIONS.md` for the human-readable trust boundary.
2. Update `AXIOMS.md` if axioms, non-axiom trusted primitives, or soundness
   controls changed.
3. Update this file with the changed audit state, artifacts, and CI guards.
4. Regenerate deterministic artifacts with the relevant `scripts/generate_*.py`
   command.
5. Run `make check`; run targeted Lean builds for changed proof modules.

**Last Updated**: 2026-04-21
