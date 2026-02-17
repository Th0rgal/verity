# Agent Guide for Verity

Quick reference for AI agents. Humans: see [README.md](README.md).

## Agent Workflow

### Before Starting
1. Check [docs/ROADMAP.md](docs/ROADMAP.md) for current status
2. Read [CONTRIBUTING.md](CONTRIBUTING.md) for conventions
3. Read relevant README in working directory

### When Writing Code

**DO**: Read before editing · Run `lake build` · Follow `[Category]` prefixes · Update docs/ROADMAP.md for arch changes

**DON'T**: Create files unnecessarily · Add `sorry` without docs · Skip builds · Force-push without approval · Create docs proactively

### Creating Issues/PRs

**Format**: `[Category] Brief description` - use templates in `.github/ISSUE_TEMPLATE/`

**Categories**: `[Layer 3]` `[Trust Reduction]` `[Property Coverage]` `[Compiler Enhancement]` `[Documentation]` `[Infrastructure]`

See [CONTRIBUTING.md](CONTRIBUTING.md) for full conventions.

### Human Approval Required

**Ask before**: Force-push, merge, delete branches, change compiler semantics, add axioms, any destructive operations

**Proceed freely**: Read files, create local branches/commits, run builds/tests, create issues, update docs

## Navigation

| Need | Read |
|------|------|
| Project overview | README.md |
| Conventions | CONTRIBUTING.md |
| Current progress | docs/ROADMAP.md |
| Verification details | docs/VERIFICATION_STATUS.md |
| Proof guide | Compiler/Proofs/README.md |
| EDSL semantics | Verity/Core.lean |
| Compiler specs | Compiler/Specs.lean |
| IR semantics | Compiler/Proofs/IRGeneration/IRInterpreter.lean |
| Yul semantics | Compiler/Proofs/YulGeneration/Semantics.lean |

## Task Workflows

**Layer 3 Proofs**:
1. Read docs/ROADMAP.md for Layer 3 status
2. Read Compiler/Proofs/README.md for patterns
3. Study completed proofs: `assign_equiv`, `storageLoad_equiv`
4. Use template: `.github/ISSUE_TEMPLATE/layer3-statement-proof.md`

**New Contracts**:
1. Read README.md - "Adding a Contract"
2. Follow SimpleStorage pattern
3. Spec → Invariants → Implementation → Proofs → Tests

**Compiler Changes**:
1. Read Compiler/Specs.lean
2. Ensure proofs still build
3. Use template: `.github/ISSUE_TEMPLATE/compiler-enhancement.md`

## Architecture

```
Layer 1 ✅ EDSL ≡ ContractSpec
Layer 2 ✅ ContractSpec → IR
Layer 3 ✅ IR → Yul
```

See [docs/ROADMAP.md](docs/ROADMAP.md) for detailed status.

**Directories**:
- `Verity/` - EDSL, specs, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen
- `Compiler/Proofs/` - Layer 2 & 3 proofs
- `docs/` - Roadmap, verification status
- `test/` - Foundry tests
- `.github/ISSUE_TEMPLATE/` - Issue templates

## Common Pitfalls

❌ Generic titles | ✅ `[Layer 3] Prove conditional statement equivalence`
❌ Edit without reading | ✅ Read tool before Edit tool
❌ Undocumented `sorry` | ✅ Document blockers, create issues
❌ Force-push without approval | ✅ Ask first
❌ Create files proactively | ✅ Edit existing when possible
❌ Docs drift from code | ✅ Update docs with code changes

## Agent Patterns

**Systematic Proof Work**: Prove first completely → Document approach → Apply to rest → Update ROADMAP.md → Close issues

**Safe Exploration**: Read ROADMAP → Use Grep/Glob for definitions → Read specific files → Build mental model → Verify with `lake build`

**Documentation Updates**: Code + verify → Update docs → Check consistency → Commit together

## Commands

```bash
lake build                           # Required before commits
FOUNDRY_PROFILE=difftest forge test  # All tests (FFI needed for property/differential tests)
```

## Resources

- Lean 4: [docs](https://lean-lang.org/documentation/) | [theorem proving](https://lean-lang.org/theorem_proving_in_lean4/)
- Tactics: [Mathlib reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- Start here: `Verity/Specs/SimpleStorage/Proofs.lean`

---

**Status**: [docs/ROADMAP.md](docs/ROADMAP.md) · **Humans**: [README.md](README.md) · **Conventions**: [CONTRIBUTING.md](CONTRIBUTING.md)
