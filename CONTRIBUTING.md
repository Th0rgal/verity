# Contributing to Verity

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
lake build  # Must pass — verifies all proofs
FOUNDRY_PROFILE=difftest forge test  # Must pass — runs all Foundry tests
# FOUNDRY_PROFILE=difftest is required because property and differential
# tests use vm.ffi() to invoke the Lean-based interpreter
# No new `sorry` without documentation
# No new `axiom` without documenting in AXIOMS.md
# Update docs/ROADMAP.md if architectural changes
# If adding a new contract, run the checklist below
```

**When adding a new contract**, also update:
- `test/property_manifest.json` — Run `python3 scripts/extract_property_manifest.py`
- `README.md` — Contracts table (theorem count and description)
- `docs/VERIFICATION_STATUS.md` — Contract table and coverage stats
- `docs-site/public/llms.txt` — Quick Facts and theorem breakdown table
- `docs-site/content/verification.mdx` — Snapshot section
- `docs-site/content/examples.mdx` — Contract descriptions and count
- Plus any other files that reference theorem/test/contract counts (e.g., `compiler.mdx`, `research.mdx`, `index.mdx`, `layout.tsx`, `ROADMAP.md`, `TRUST_ASSUMPTIONS.md`, `test/README.md`)
- Run `python3 scripts/check_contract_structure.py` to verify file structure is complete
- Run `python3 scripts/check_doc_counts.py` to verify all counts are synchronized (validates 14 doc files + property test headers)
- Run `python3 scripts/check_lean_hygiene.py` to verify no `#eval` in proof files and `allowUnsafeReducibility` count is correct

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

Co-Authored-By: Claude <noreply@anthropic.com>
```

Types: `feat` `fix` `proof` `docs` `refactor` `test` `chore`

## Code Comment Conventions

Follow these conventions to keep documentation accurate and maintainable.

### Proof Status

**For Theorems**:
- `sorry` - Incomplete proof (blocked by CI in proof files)
- No marker - Complete proof
- **DON'T** use TODO/STUB in proven theorems

```lean
-- ✅ GOOD: Complete proof, no marker needed
theorem my_theorem : ... := by
  unfold ...
  simp [...]

-- ❌ BAD: Complete proof but has misleading TODO
theorem my_theorem : ... := by
  -- TODO: This actually works fine
  unfold ...
  simp [...]
```

**For Incomplete Proofs**:
```lean
-- Only in draft branches, NOT in main
theorem draft_theorem : ... := by
  sorry  -- Strategy: Use induction on List structure
           -- See issue #123 for details
```

### Module Documentation

**Module Headers** should reflect current status:

```lean
/-! ## Module Name

Brief description of what this module does.

**Status**: Complete | Partial | Draft
**Dependencies**: List axioms/external dependencies
**Related**: Links to other relevant modules
-/
```

**Status Definitions**:
- **Complete**: All theorems proven, no sorry
- **Partial**: Some proven, some sorry (specify which)
- **Draft**: Structural outline only

**Example**:
```lean
/-! ## Layer 3: Statement-Level Equivalence

Proves IR statement execution is equivalent to Yul statement execution
when states are aligned.

**Status**: Complete - All statement types proven
**Dependencies**: Uses keccak256 axiom (see AXIOMS.md)
-/
```

### Future Work Comments

For planned improvements or known limitations:

```lean
-- FUTURE: Add support for delegatecall
-- See issue #123 for design discussion
def currentImplementation := ...
```

**DON'T** use:
- ~~`TODO:`~~ (implies incomplete current work)
- ~~`FIXME:`~~ (implies broken code)
- ~~`HACK:`~~ (use `NOTE:` with explanation instead)

### Implementation Notes

For non-obvious design choices:

```lean
-- NOTE: We use fuel-based recursion here because Lean cannot prove
-- termination for mutually recursive functions with this structure.
-- See Equivalence.lean for the proof strategy this enables.
def execIRStmtFuel (fuel : Nat) : ... := ...
```

### Axiom Documentation

All axioms **must** be documented inline **and** in AXIOMS.md:

```lean
/-- AXIOM: keccak256 selector computation

This is an axiom because Lean cannot natively compute keccak256.
Validated by CI fixture checks against solc-computed selectors.
See AXIOMS.md for full soundness justification.
-/
axiom keccak256_first_4_bytes (sig : String) : Nat
```

### Property Test Tags

Property tests must match Lean theorem names exactly:

```solidity
/// Property: store_retrieve_roundtrip
function testProp_StoreRetrieveRoundtrip(...) public { ... }
```

Tag format: `/// Property: exact_theorem_name`

### What NOT to Include

❌ **Stale TODOs** in completed code
❌ **Difficulty estimates** after proof is done
❌ **Verbose explanations** of obvious code
❌ **Status claims** that don't match reality

✅ **Brief descriptions** of what code does
✅ **Links** to related issues for context
✅ **Explanations** of non-obvious design choices
✅ **Accurate status** in module headers

## Development

**Layer 3 proofs**: Read [Compiler/Proofs/README.md](Compiler/Proofs/README.md), study completed proofs (`assign_equiv`, `storageStore_equiv`), use templates

**New contracts**: Use `python3 scripts/generate_contract.py <Name>` to scaffold all boilerplate files, then follow the `SimpleStorage` pattern: Spec → Invariants → Implementation → Proofs → Tests

**Compiler changes**: Check [Compiler/Specs.lean](Compiler/Specs.lean), ensure proofs still build

## Adding Axioms

Axioms should be **avoided whenever possible** as they introduce trust assumptions. If you must add an axiom:

1. **Exhaust all alternatives first**:
   - Can you prove it? (even if difficult)
   - Can you use a weaker lemma?
   - Can you refactor to avoid the need?

2. **Document in AXIOMS.md**:
   - State the axiom clearly
   - Provide soundness justification
   - Explain why a proof isn't feasible
   - Note future work to eliminate axiom
   - Assess risk level

3. **Add inline comment in source**:
   ```lean
   /--
   AXIOM: Brief explanation
   See AXIOMS.md for full soundness justification
   -/
   axiom my_axiom : ...
   ```

4. **CI will validate**: The CI workflow automatically detects axioms and ensures they're documented in AXIOMS.md. Undocumented axioms will fail the build.

See [AXIOMS.md](AXIOMS.md) for current axioms and detailed guidelines.

## Key Files

- `Verity/` - EDSL, specs, Layer 1 proofs
- `Compiler/` - IR, Yul, codegen
- `Compiler/Proofs/` - Layer 2 & 3 proofs
- `docs/ROADMAP.md` - Progress tracking
- `test/` - Foundry tests

Full details: [docs/VERIFICATION_STATUS.md](docs/VERIFICATION_STATUS.md)
