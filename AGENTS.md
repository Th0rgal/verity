# Agent Guide for Verity

This file is the operator quickstart. Keep it short and enforceable.

## Non-Negotiables

1. Keep `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, and `AXIOMS.md` synchronized with any semantic/trust/CI boundary change.
2. For issue #1060, `artifacts/issue_1060_progress.json` is the single source of truth for roadmap status.
3. Keep exactly one active roadmap item (`partial` or `in_progress`) in the ledger at a time.
4. Never claim completion without evidence and passing checks.

## Required Loop for #1060

1. `make pr-sync` (or `make pr-sync-build`) before coding.
2. Implement exactly one roadmap item.
3. Update `artifacts/issue_1060_progress.json` with acceptance criteria, changed files, verification commands/results, theorem/test evidence.
4. Run `make ci-fast`.
5. Post/update progress comment: `make post-1060-comment ITEM=<id>`.
6. Sync generated trackers from ledger: `make sync-1060-trackers`.

## Core Commands

```bash
lake build
make check
make ci-fast
make pr-sync
make post-1060-comment ITEM=2.2
make sync-1060-trackers
```

## Reference Docs

- Project overview: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- #1060 execution prompt: [docs/ISSUE_1060_AGENT_PROMPT.md](docs/ISSUE_1060_AGENT_PROMPT.md)
- Script reference: [scripts/REFERENCE.md](scripts/REFERENCE.md)
