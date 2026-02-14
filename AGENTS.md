# Agent Guide for DumbContracts

Quick reference for AI agents working in this repository. For humans, see `README.md`.

## 🎯 Agent Workflow

### Before Starting Any Task

1. **Read project state**: Check `docs/ROADMAP.md` (currently 97% complete)
2. **Understand standards**: Review `CONTRIBUTING.md` for conventions
3. **Check context**: Read relevant README files in the working directory

### When Writing Code

**✅ DO:**
- Follow semantic prefixes for issues/PRs: `[Layer 3]`, `[Trust Reduction]`, `[Property Coverage]`, `[Compiler Enhancement]`
- Read files before editing them (Read tool before Edit tool)
- Keep proofs under 20 lines when possible
- Use `lake build` to verify changes compile
- Update `docs/ROADMAP.md` for architectural changes
- Add tests for new features in `test/` using Foundry

**❌ DON'T:**
- Create new files unless absolutely necessary - prefer editing existing files
- Add `sorry` placeholders without documenting them as blockers
- Skip running the build after changes
- Use destructive git operations (force-push, hard reset) without approval
- Create documentation files (*.md) or README files proactively - only when explicitly requested
- Change compiler semantics without considering proof impact

### When Creating Issues

Use issue templates in `.github/ISSUE_TEMPLATE/`:
- `layer3-statement-proof.md` - For Layer 3 statement equivalence proofs
- `trust-reduction.md` - For Yul ↔ EVM trust assumption work
- `property-coverage.md` - For property verification improvements
- `compiler-enhancement.md` - For new compiler features

**Title format**: `[Category] Brief description`
**Required sections**: Goal, Effort Estimate, Implementation Strategy, Acceptance Criteria

See `CONTRIBUTING.md` for full issue and PR conventions.

### When Creating Pull Requests

**Before submitting:**
```bash
lake build                    # Must pass
# Verify no new `sorry` added (unless documented)
# Update docs/ROADMAP.md if needed
# Add/update tests where appropriate
```

**PR format**:
- **Title**: Same semantic prefix as issues (`[Layer 3] Description`)
- **Body**: Summary (bullets), Motivation, Test Plan, Related Issues
- **Commits**: Follow conventional commit style (see `CONTRIBUTING.md`)

### When to Ask for Human Approval

**Always ask before:**
- Destructive operations (force-push, hard reset, deleting branches/files)
- Publishing actions (pushing to remote, merging PRs, closing issues, creating releases)
- Changing compiler semantics or IR/Yul definitions (affects all proofs)
- Adding new trust assumptions or axioms (document soundness extensively)
- Non-reversible operations that affect shared state

**Can proceed directly:**
- Reading files and exploring codebase
- Creating local branches and commits
- Running builds and tests
- Creating issues with proper templates
- Updating documentation to match code changes

## 📚 Navigation Guide

### Quick File Finder

**Need...** → **Read...**
- Project overview → `README.md`
- Contribution standards → `CONTRIBUTING.md`
- Current priorities & progress → `docs/ROADMAP.md`
- Detailed verification status → `docs/VERIFICATION_STATUS.md`
- Proof development guide → `Compiler/Proofs/README.md`
- EDSL core semantics → `DumbContracts/Core.lean`
- Compiler specs → `Compiler/Specs.lean`
- IR semantics → `Compiler/Proofs/IRGeneration/IRInterpreter.lean`
- Yul semantics → `Compiler/Proofs/YulGeneration/Semantics.lean`

### By Task Type

**Layer 3 Proof Work:**
1. Read `docs/ROADMAP.md` - Layer 3 section (currently 97% complete)
2. Read `Compiler/Proofs/README.md` - Proof patterns and tactics
3. Read `Compiler/Proofs/YulGeneration/StatementEquivalence.lean` - Current proofs
4. Study completed proofs (e.g., `assign_equiv`, `storageLoad_equiv`) for patterns
5. Follow issue template: `.github/ISSUE_TEMPLATE/layer3-statement-proof.md`

**New Contract Development:**
1. Read `README.md` - "Adding a Contract" section
2. Use `SimpleStorage` as reference implementation
3. Follow file layout: Spec → Invariants → Implementation → Proofs
4. Add tests in `test/` using Foundry (property + differential)

**Compiler Enhancement:**
1. Read `Compiler/Specs.lean` for declarative compilation semantics
2. Check `Compiler/Proofs/` - changes must not break existing proofs
3. Use issue template: `.github/ISSUE_TEMPLATE/compiler-enhancement.md`
4. Add tests and update documentation

**Property Coverage Work:**
1. Read `docs/VERIFICATION_STATUS.md` - Property Test Coverage section
2. Use scripts: `scripts/check_property_coverage.py`, `scripts/check_property_manifest.py`
3. Add infrastructure in `DumbContracts/Proofs/Stdlib/` if needed
4. Use issue template: `.github/ISSUE_TEMPLATE/property-coverage.md`

## 🧩 Project Architecture

**3-Layer Verification Stack:**
```
Layer 1 (✅ 100%): EDSL ≡ ContractSpec          (228 properties proven)
Layer 2 (✅ 100%): ContractSpec → IR            (7 contracts, all proven)
Layer 3 (🟡 97%):  IR → Yul                     (8/10 statement proofs complete)
```

**Directory Structure:**
- `DumbContracts/` - EDSL core, specs, examples, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen implementation
- `Compiler/Proofs/` - Layer 2 & 3 correctness proofs
- `docs/` - Roadmap, verification status, design notes
- `test/` - Foundry property and differential tests
- `scripts/` - Automation (issue creation, property checking)
- `.github/ISSUE_TEMPLATE/` - Structured issue templates

**Current Work:** Layer 3 completion (2-6 hours remaining), see `docs/ROADMAP.md`

Full architectural details: `docs/VERIFICATION_STATUS.md`

## ⚠️ Common Pitfalls for Agents

### Issue/PR Creation
- ❌ Generic titles like "Fix bug" or "Update code"
- ✅ Semantic prefixes: `[Layer 3] Prove conditional statement equivalence`

### Code Changes
- ❌ Editing files without reading them first
- ✅ Always use Read tool before Edit/Write tools

### Proof Development
- ❌ Adding `sorry` without explanation or tracking
- ✅ Document blockers, create issues for remaining work

### Git Operations
- ❌ Force-pushing or destructive operations without approval
- ✅ Ask before any operation affecting remote state

### File Creation
- ❌ Creating README.md, docs, or new files proactively
- ✅ Prefer editing existing files; create only when necessary

### Documentation
- ❌ Letting docs drift out of sync with code
- ✅ Update ROADMAP.md and relevant docs when making changes

## 🤖 Agent-Specific Patterns

### Pattern: Systematic Proof Work

When proving multiple similar theorems:

1. **Establish pattern** - Prove first theorem completely
2. **Document approach** - Add comments explaining strategy
3. **Apply systematically** - Use same pattern for remaining theorems
4. **Track progress** - Update `docs/ROADMAP.md` as you complete proofs
5. **Close issues** - Close GitHub issues with references to commits

**Example**: Issues #28-35 (statement equivalence proofs) - proved 7/8 systematically

### Pattern: Safe Exploration

When understanding unfamiliar code:

1. **Start broad** - Read `docs/ROADMAP.md` and relevant README
2. **Find entry points** - Use Grep/Glob to locate key definitions
3. **Read carefully** - Use Read tool on specific files
4. **Build mental model** - Understand types, semantics, dependencies
5. **Verify understanding** - Check with `lake build` or ask questions

### Pattern: Documentation Updates

When making changes:

1. **Code first** - Implement the change and verify it builds
2. **Docs second** - Update affected documentation in same commit
3. **Consistency check** - Ensure ROADMAP.md, VERIFICATION_STATUS.md, and code align
4. **Commit together** - Include docs and code changes in one commit

### Pattern: Issue-Driven Development

For multi-step tasks:

1. **Create tracking issues** - Use appropriate templates for work breakdown
2. **One issue at a time** - Complete fully before moving to next
3. **Close with commits** - Reference commits/PRs when closing issues
4. **Update roadmap** - Keep `docs/ROADMAP.md` synchronized with issue status

## 📖 Documentation Index

- `AGENTS.md` - This file (agent-specific guide)
- `README.md` - User-facing project overview (examples, build, structure)
- `CONTRIBUTING.md` - Contribution conventions and standards (issues, PRs, code style)
- `docs/ROADMAP.md` - Current progress and priorities (97% complete, 3-6 hours remaining)
- `docs/VERIFICATION_STATUS.md` - Comprehensive verification architecture (3 layers, status)
- `Compiler/Proofs/README.md` - Proof development guide (patterns, tactics, infrastructure)
- `.github/ISSUE_TEMPLATE/` - Structured issue templates (4 templates for different work types)

## 🔧 Useful Commands

```bash
# Build and verify
lake build                              # Type-check all Lean code (required before commits)
lake build dumbcontracts-compiler       # Build compiler executable
forge test                              # Run all Foundry tests (unit + property + differential)

# Property coverage validation
python3 scripts/check_property_coverage.py   # Verify all theorems have tests
python3 scripts/check_property_manifest.py   # Verify test tags reference real theorems
python3 scripts/check_selectors.py           # Verify keccak256 selector hashes

# Issue management
./scripts/create_layer3_issues.sh       # Create Layer 3 tracking issues (idempotent)
gh issue list --label "layer-3"         # View Layer 3 issues
gh issue view <number>                  # View specific issue details

# Git workflow
git checkout -b category/description    # Create feature branch (e.g., proof/conditional-equiv)
git commit -m "type: description"       # Conventional commits (feat, fix, proof, docs, etc.)
# Always ask before: git push, git merge, git push --force, destructive operations
```

## 🎓 Learning Resources

- **Lean 4**: [Documentation](https://lean-lang.org/documentation/) | [Theorem Proving Guide](https://lean-lang.org/theorem_proving_in_lean4/)
- **Proof Tactics**: [Mathlib Tactics Reference](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- **This Project**: Start with completed proofs in `DumbContracts/Specs/SimpleStorage/Proofs.lean`

---

**Last Updated**: 2026-02-14
**Project Status**: 97% complete (Layer 3: 2-6 hours remaining)
**For Humans**: See `README.md` | **For Conventions**: See `CONTRIBUTING.md` | **For Progress**: See `docs/ROADMAP.md`
