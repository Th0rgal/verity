# Yul Identity Checker

Issue: [#967](https://github.com/Th0rgal/verity/issues/967)

This document defines the target workflow for checking AST-level identity between Verity-generated Yul and `solc`-generated Yul for pinned toolchain tuples.

## Status

`scripts/generate_yul_identity_diff_report.py` is now available for deterministic, machine-readable identity diff reports suitable for CI artifacts.
`scripts/check_parity_pack_metrics.py` is now available to gate report-derived parity metrics (`onlyInVerity`, `onlyInSolidity`, `hashMismatch`) in CI.

## Goals

1. Compare Yul at AST level (not text-only).
2. Localize mismatches to stable node paths and source/IR origins.
3. Produce machine-readable reports for CI and rule authoring.
4. Distinguish `non-identity` from `unsupported`.

## CLI Shape

```bash
python3 scripts/generate_yul_identity_diff_report.py \
  --solc-dir <path> \
  --verity-dir <path> \
  --output <path.json>

python3 scripts/check_parity_pack_metrics.py \
  --report <path.json> \
  --max-only-in-verity 0 \
  --max-only-in-solidity 0 \
  --max-hash-mismatch 0
```

## Report Schema

1. `status`: `identical | non_identical`.
2. `summary`: file + mismatch counts (and by-kind totals).
3. `mismatches[]`: stable entries with:
   - `file`
   - `path` (function/subtree-localized path)
   - `kind`
   - `verity` and `solc` values

## CI Integration

1. Run identity checker on pinned fixture corpus.
2. Fail on `non_identical`.
3. Allow `unsupported` only if listed in tracked manifest.
4. Upload JSON reports as workflow artifacts.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
