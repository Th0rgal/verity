# Architecture RFC: Split Verity into EDSL, Compiler, and Examples Packages

Status: Proposed
Issue: #1307

## Objective

Restructure the repository into strict package boundaries so canonical contract implementations are not mixed into framework internals.

Target packages:

1. `verity-edsl`
2. `verity-compiler`
3. `verity-examples`

This RFC assumes a clean break with no compatibility aliases.

## Why split this way

- `verity-edsl` should define language semantics, macros, and verification interfaces.
- `verity-compiler` should consume EDSL artifacts and produce backend output without embedding concrete example contracts.
- `verity-examples` should own contracts, proofs, parity fixtures, and end-to-end test harnesses.

This enforces one dependency direction:

`verity-examples -> verity-compiler -> verity-edsl`

No reverse imports are allowed.

## Current package boundaries

CI enforces import-direction checks and package-glob ownership checks on `main`. Current export surfaces:

- `verity-edsl` exports only `Verity.*` modules.
- `verity-examples` exports only `Contracts.*` modules.
- `verity-compiler` exports `Compiler.*` plus a small `Verity.*` bridge surface (`Verity.Macro` and proof automation helpers) that still sits above compiler types.

**Remaining work**: move the shared interface types out of `Compiler`, then shrink or eliminate the temporary `Verity.*` bridge surface in `verity-compiler`.

## Package responsibilities

## `verity-edsl`

Owns:

- `Verity/*` EDSL, semantics, macro implementation, proof utility infrastructure.

Must not depend on:

- `Compiler/*`
- Any concrete contract modules.

Public API:

- Stable imports for contract authors.
- Macro entrypoints used by examples.

## `verity-compiler`

Owns:

- `Compiler/*` lowering, codegen, CLI, backend integration, proofs for compilation pipeline.

Depends on:

- `verity-edsl`

Must not depend on:

- Concrete contracts from examples.

Design change required:

- Replace internal global registry assumptions with explicit input manifest/module list provided at invocation time.

## `verity-examples`

Owns:

- Canonical contracts and proofs.
- Solidity reference contracts used for differential testing.
- Foundry and differential test harnesses.

Depends on:

- `verity-edsl`
- `verity-compiler`

Contract source policy:

- One contract per canonical file/module.
- No mixed multi-contract buckets such as a monolithic `Core.lean` containing unrelated contracts.

Suggested layout:

- `examples/contracts/core/Counter.lean`
- `examples/contracts/core/Owned.lean`
- `examples/contracts/token/ERC20.lean`
- `examples/contracts/token/ERC721.lean`
- `examples/contracts/security/ReentrancyExample.lean`
- `examples/solidity-ref/*.sol`
- `examples/foundry/*`

## Build and CLI implications

Required compiler changes:

1. Remove default baked-in "compile all known contracts" behavior from core internals.
2. Add explicit manifest-based selection:
   - `--manifest <path>` for batch compilation.
   - Optional `--module <Lean.Module.Name>` repeatable flag.
3. Keep deterministic output ordering based on manifest order.

Manifest responsibility moves to `verity-examples`.

## CI migration

Replace monolithic coupling with package-scoped jobs plus integration:

1. `edsl` job:
   - Build/test only `verity-edsl`.
2. `compiler` job:
   - Build/test `verity-compiler` against published/local `verity-edsl`.
3. `examples` job:
   - Build examples/proofs against pinned `verity-edsl` + `verity-compiler`.
4. `parity` job:
   - Generate Yul via compiler and run Foundry differential tests using `examples/solidity-ref`.
5. `integration` job:
   - End-to-end smoke across all three packages.

Also add import-boundary linting per package to fail reverse dependencies.

## Migration plan (no compatibility aliases)

Phase 1: Introduce package skeletons and dependency boundaries.

- Create package directories/workspace config.
- Move files without semantic edits.
- Keep all checks green.

Phase 2: Decouple compiler from contract registry.

- Introduce manifest/module-input compilation path.
- Remove direct contract imports from compiler binaries/tests.

Phase 3: Move examples and tests.

- Relocate contracts/proofs/foundry/parity fixtures into `verity-examples`.
- Split macro contract definitions to one contract per module.

Phase 4: Purge legacy coupling.

- Remove old mixed-location modules.
- Remove any scripts that assume single-package roots.
- Enforce boundary checks in CI.

## Risks and mitigations

Risk: Build and cache churn due to package graph changes.
Mitigation: Introduce a root workspace orchestrator and cache keys per package.

Risk: Script breakage from hardcoded paths.
Mitigation: Add package-aware path discovery and migrate scripts in the same PR series.

Risk: Temporary contributor confusion during transition.
Mitigation: Add one architecture page per package and a root migration guide.

## Acceptance criteria

1. `verity-edsl` builds without importing compiler/examples modules.
2. `verity-compiler` builds without importing concrete contracts.
3. `verity-examples` builds against pinned versions of the two lower layers.
4. Differential tests consume `examples/solidity-ref` fixtures.
5. New contracts are added one contract per module, no multi-contract bucket modules.
6. CI enforces the dependency direction.
