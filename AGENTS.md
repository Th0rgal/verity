# Agent Guide for Verity

Quick operational guide for AI agents. Human overview: [README.md](README.md).

## Documentation Safety (Critical)

The following files are safety-critical and MUST stay synchronized with source code:

- `AUDIT.md`
- `TRUST_ASSUMPTIONS.md`
- `AXIOMS.md`

If code changes and these files are not updated in the same change set, trust boundaries become stale and the system is unsafe to assess correctly.

Mandatory rule:

1. Every source-code change that affects architecture, semantics, trust boundaries, assumptions, axioms, CI safety checks, or compilation paths MUST update these files immediately.
2. Never defer these updates to a later PR.
3. Treat stale trust and audit documentation as a security issue.

## Workflow

### Before starting

1. Read [docs/ROADMAP.md](docs/ROADMAP.md).
2. Read [CONTRIBUTING.md](CONTRIBUTING.md).
3. Read the local README for the area you are modifying.

### While coding

Do:

- Read files before editing.
- Run `lake build`.
- For issue #1060 runs, update `artifacts/issue_1060_progress.json` and run `python3 scripts/check_issue_1060_integrity.py` before claiming completion.
- Use `[Category]` prefixes.
- Update `docs/ROADMAP.md` for architecture changes.
- Keep `AUDIT.md`, `TRUST_ASSUMPTIONS.md`, and `AXIOMS.md` in sync.

Do not:

- Add files without need.
- Add undocumented `sorry`.
- Skip builds.
- Force-push without approval.

## Issues and PRs

- Title format: `[Category] Brief description`
- Use templates in `.github/ISSUE_TEMPLATE/`
- Categories: `[Trust Reduction]`, `[Property Coverage]`, `[Compiler Enhancement]`, `[Documentation]`, `[Infrastructure]`

## Approval Boundaries

Ask before:

- Force-push
- Merge
- Delete branches
- Change compiler semantics
- Add axioms
- Run destructive operations

Proceed without approval:

- Read files
- Create local branches and commits
- Run builds and tests
- Create issues
- Update docs

## Navigation

| Need | File |
|------|------|
| Project overview | README.md |
| Conventions | CONTRIBUTING.md |
| Current progress | docs/ROADMAP.md |
| Verification status | docs/VERIFICATION_STATUS.md |
| Proof guide | Compiler/Proofs/README.md |
| EDSL semantics | Verity/Core.lean |
| Compiler specs | Compiler/Specs.lean |
| IR semantics | Compiler/Proofs/IRGeneration/IRInterpreter.lean |
| Yul semantics | Compiler/Proofs/YulGeneration/Semantics.lean |

## Standard Commands

```bash
lake build
make ci-fast
FOUNDRY_PROFILE=difftest forge test
```

Optional one-time setup to enforce the fast gate before every push:

```bash
make install-fast-hook
```

## Notes

- Layer 3 proofs are complete.
- For new contracts, scaffold with `python3 scripts/generate_contract.py <Name>` and follow `/add-contract`.
- For compiler changes, read `Compiler/Specs.lean` and verify proofs still build.
- For strict non-inflation #1060 execution protocol, use `docs/ISSUE_1060_AGENT_PROMPT.md`.
