# Contributing to DumbContracts

Quick conventions for contributing. See [README.md](README.md) for project overview, [docs/ROADMAP.md](docs/ROADMAP.md) for status.

## Issue Format

**Title**: `[Category] Brief description`

**Categories**: `[Layer 3]` `[Trust Reduction]` `[Property Coverage]` `[Compiler Enhancement]` `[Documentation]` `[Infrastructure]`

**Labels**: Use `layer-3` `lean` `proof` `enhancement` `bug` `documentation` `help-wanted` `good-first-issue`

**Structure**: Use issue templates in `.github/ISSUE_TEMPLATE/`
- Goal (what needs doing)
- Effort estimate (hours/weeks)
- Implementation approach
- Acceptance criteria
- References (file paths, issues)

## PR Format

**Title**: Same `[Category]` prefix as issues

**Body**:
```markdown
## Summary
- Bullet points of changes

## Test Plan
How you verified it works

## Related Issues
Closes #X, addresses #Y
```

**Before submitting**:
```bash
lake build  # Must pass
# No new `sorry` without documentation
# Update docs/ROADMAP.md if architectural changes
```

## Code Style

**Lean**:
- 2-space indentation
- Meaningful names (`irState` not `s`)
- Proofs under 20 lines when possible
- Document complex proof strategies

**Commits**:
```
type: description

[optional body]

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```

Types: `feat` `fix` `proof` `docs` `refactor` `test` `chore`

## Development

**Layer 3 proofs**: Read [Compiler/Proofs/README.md](Compiler/Proofs/README.md), study completed proofs (`assign_equiv`, `storageLoad_equiv`), use templates

**New contracts**: Follow `SimpleStorage` pattern: Spec → Invariants → Implementation → Proofs → Tests

**Compiler changes**: Check [Compiler/Specs.lean](Compiler/Specs.lean), ensure proofs still build

## Key Files

- `DumbContracts/` - EDSL, specs, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen
- `Compiler/Proofs/` - Layer 2 & 3 proofs
- `docs/ROADMAP.md` - Progress tracking
- `test/` - Foundry tests

Full details: [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)
