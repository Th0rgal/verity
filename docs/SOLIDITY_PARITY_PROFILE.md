# Solidity-Parity Backend Profile

Issue: [#802](https://github.com/Th0rgal/verity/issues/802)
Roadmap extension: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the opt-in backend profile used for deterministic output-shape alignment with Solidity-style workflows.

## Current Meaning

After protocol-specific bundle extraction, backend profiles are only the core normalization surface:

1. `semantic` keeps default codegen behavior.
2. `solidity-parity-ordering` applies deterministic ordering only.
3. `solidity-parity` enables the generic patch pipeline in `verity-compiler-patched`, but the core compiler still ships only the `foundation` rewrite bundle.
4. Exact tuple-pinned parity requires `--parity-pack <id>` from an external plugin package.

## Profile Levels (v1)

`v1` exposes three explicit levels:

1. `semantic` (default)
2. `solidity-parity-ordering`
3. `solidity-parity`
4. `--parity-pack <id>` (tuple-pinned selection that maps to a backend profile + patch defaults)

All levels preserve Verity's semantic guarantees. Parity levels only normalize output shape.

## Normalization Rules (v1)

| Rule ID | Description | `semantic` | `solidity-parity-ordering` | `solidity-parity` |
|---|---|---|---|---|
| `dispatch.selector.sort.asc` | Sort runtime dispatch `case` blocks by selector (ascending) | no | yes | yes |
| `helpers.funcdef.sort.lex` | Sort compiler-generated/internal helper function declarations lexicographically by name | no | yes | yes |
| `patch.pass.enable` | Enable the generic deterministic patch pipeline | no (opt-in only) | no (opt-in only) | yes (forced on) |

## Reproducibility Contract

For a fixed source, fixed profile, fixed tool version, and fixed CLI options:

- emitted Yul output is deterministic;
- profile-normalized ordering is stable across repeated runs;
- profile behavior is fully opt-in (`semantic` remains default).

For parity-pack mode, reproducibility is additionally keyed by the pack ID and compatibility tuple metadata.

## Non-Goals (v1)

`v1` does not attempt full byte-for-byte `solc` output identity on its own. In particular:

- it does not rewrite all helper naming patterns to mirror `solc` internals;
- it does not force ABI/content layout rewrites beyond documented deterministic normalizations;
- it does not weaken verification constraints to chase shape parity.

Exact parity now comes from an external parity pack layered on top of this profile surface.

## Arithmetic Semantics (Invariant Across Profiles)

All backend profiles use identical **wrapping modular arithmetic at 2^256**. Profiles differ only in output-shape normalization (selector sorting, helper sorting, patch pass enablement), not semantic behavior. A contract compiled with `--backend-profile semantic` and `--backend-profile solidity-parity` will produce semantically equivalent Yul with identical arithmetic.

See [`docs/ARITHMETIC_PROFILE.md`](ARITHMETIC_PROFILE.md) for the full arithmetic specification and proof coverage.

## Identity Track (Groundwork)

Issue [#967](https://github.com/Th0rgal/verity/issues/967) defines the path from output-shape parity to exact `solc` Yul identity for pinned compiler tuples.

Planned extensions (beyond current `--parity-pack` registry/selection support):

1. Versioned parity packs (`solc-version + optimizer + evm version`) with explicit compatibility metadata.
2. Typed rewrite rules (`ExprRule`, `StmtRule`, `BlockRule`, `ObjectRule`) with strict scope boundaries.
3. Proof-carrying rule activation and pack-level composition theorem.
4. AST-level identity checker with mismatch localization and machine-readable reports.
5. Canonicalization phase for helper naming/order/layout normalization.

See:
- [`docs/PARITY_PACKS.md`](PARITY_PACKS.md)
- [`docs/REWRITE_RULES.md`](REWRITE_RULES.md)
- [`docs/IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)
- [`docs/SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
