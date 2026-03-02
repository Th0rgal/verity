# Scripts Quickstart

Use this file for day-to-day operation. Detailed script inventory lives in [REFERENCE.md](REFERENCE.md).

## High-signal commands

```bash
# Local CI-equivalent subset
make check

# Issue #1060 fast gate
make ci-fast
make ci-fast-build

# Strict PR startup sync sequence for #1060
make pr-sync
make pr-sync-build

# Keep artifact/docs counters fresh
make refresh-status

# Post/update one roadmap progress comment
make post-1060-comment ITEM=2.2

# Regenerate PR/issue trackers from the ledger
make sync-1060-trackers
```

## Sources of truth

- Roadmap status: `artifacts/issue_1060_progress.json`
- Verify workflow sync contract: `scripts/verify_sync_spec.json`
- Unified verify workflow validator: `scripts/check_verify_sync.py`

## Notes

- Legacy `check_verify_*` scripts remain for compatibility and focused unit tests.
- CI now enforces verify workflow invariants through `check_verify_sync.py`.
