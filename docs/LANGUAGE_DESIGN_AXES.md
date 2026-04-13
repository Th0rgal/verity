# Language Design Axes — Implementation Plan

> Tracking issues: #1726 (umbrella), #1727 (Axis 1), #1728 (Axis 2), #1729 (Axis 3), #1730 (Axis 4)
> Connects to: #1724 (Solidity parity), #1723 (proven fragment extension)

## Overview

This document describes the plan to take Verity's `verity_contract` EDSL beyond Solidity feature parity by fixing Solidity's systemic design flaws at the language level. Four axes of improvement have been identified, each with concrete features, implementation strategies, and integration points with the existing codebase.

**Design philosophy**: Easy to translate from Solidity, hard to introduce Solidity's bugs.

## Suggested Implementation Order

The order is driven by **impact x effort x unblocking power**:

### Phase 1: Effect System & Auto-Theorem Generation (Axis 3, #1729)

**Why first**: Lowest friction, highest proof payoff.

- `@[view]` verification already exists in `Validation.lean` (`stmtWritesState`) — the infrastructure is 80% there
- Frame condition theorems are the #1 bottleneck in compositional verification — every annotated function instantly contributes to #1723
- No `verity_contract` grammar changes needed — only extends existing function-level attributes
- Builds the **auto-theorem generation machinery** that Axis 2 reuses

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 1a | Strengthen `@[view]` with auto-generated `_is_view` theorem | 1 week | Keep existing validation; add theorem emission in `Macro/Elaborate.lean` |
| 1b | Add `@[modifies slot1, slot2]` with `_frame` theorem | 2–3 weeks | New validation pass (enumerate write targets vs declared set); generate universally-quantified frame theorem |
| 1c | Add `@[no_external_calls]` with `_no_calls` theorem | 1 week | Reject external call statements; generate no-calls theorem |
| 1d | Annotation composition | 1 week | Multiple annotations on one function; conjunction theorem |

**Files touched**: `Macro/Elaborate.lean`, `Macro/Translate.lean`, `CompilationModel/Validation.lean`
**Estimated total**: 3–4 weeks

### Phase 2: CEI Enforcement + Access Control (Axis 2 partial, #1728)

**Why second**: Reuses Phase 1's theorem generation infrastructure.

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 2a | CEI static analysis | 1–2 weeks | Walk function body AST, track external call position, error on writes after calls |
| 2b | CEI opt-out ladder | 1 week | `@[cei_safe by proof]` (machine-checked), `nonReentrant` recognition (low trust), `@[allow_post_interaction_writes]` (trust surface) |
| 2c | `roles` section + `@[requires Role]` | 2–3 weeks | New grammar section; macro-generated require + auto-generated access control theorem |

**Escalation ladder** (consistent across all safety features):
```
SAFE BY DEFAULT (compiler enforces)
  → LEAN PROOF (machine-checked, zero trust)
    → KNOWN-SAFE GUARD (nonReentrant, require)
      → EXPLICIT ANNOTATION (trust surface in --trust-report)
```

**Files touched**: `Macro/Syntax.lean` (roles section), `Macro/Translate.lean`, new `Macro/CEICheck.lean`
**Estimated total**: 4 weeks

### Phase 3: Semantic Newtypes (Axis 1 partial, #1727)

**Why third**: Standalone grammar change, doesn't depend on Phase 1–2.

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 3a | `types` section in grammar | 1 week | Add to `Macro/Syntax.lean`; parse `TypeName : BaseType` entries |
| 3b | `ParamType.newtypeOf` | 1 week | Extend `ParamType` inductive; update `valueTypeFromSyntax` to resolve user-defined types |
| 3c | Type checking + Yul erasure | 1 week | Reject mismatched newtype operations at elaboration; compile to base type (zero overhead) |

**Key insight from research**: `ParamType` is a closed inductive with 11 variants and `valueTypeFromSyntax` only accepts fixed identifiers. Custom types cannot be done at contract level today — this is a necessary language change.

**Files touched**: `Macro/Syntax.lean`, `CompilationModel/Types.lean`, `Macro/Translate.lean`, `Macro/Elaborate.lean`, `CompilationModel/Compile.lean`
**Estimated total**: 2–3 weeks

### Phase 4: Namespaced Storage (Axis 4, #1730)

**Why fourth**: Standalone, doesn't depend on other phases.

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 4a | Namespace computation | 1 week | Compute `keccak256("{ContractName}.storage.v0")` at elaboration time using kernel Keccak |
| 4b | Slot offsetting | 1 week | All `slot N` declarations become `slot (namespace_base + N)` |
| 4c | Override attributes | 0.5 weeks | `@[no_namespace]` to opt out; `@[namespace "custom"]` for custom string |
| 4d | ABI + tooling integration | 0.5 weeks | Emit namespace in ABI JSON; `--print-storage-layout` flag |

**Files touched**: `Macro/Elaborate.lean`, `Macro/Translate.lean`, `CompilationModel/AbiHelpers.lean`
**Estimated total**: 2–3 weeks

### Phase 5: ADTs + Pattern Matching + Result Types (Axis 1 remainder, #1727)

**Why last**: Largest change, touches the most files, benefits from all prior infrastructure.

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 5a | `inductive` section in grammar | 1 week | Parse variant definitions with typed fields |
| 5b | New CompilationModel constructs | 2 weeks | `ParamType.adt`, `Expr.adtConstruct/adtTag/adtField`, `Stmt.matchAdt` |
| 5c | Storage encoding (tagged unions) | 1 week | Tag byte + max-width fields in consecutive slots |
| 5d | Yul lowering | 1 week | `matchAdt` → `YulStmt.switch`; `adtConstruct` → sequential `sstore` |
| 5e | ABI encoding | 1 week | `(uint8 tag, fields...)` with max-width encoding |
| 5f | `Call.Result` + `!` sugar | 2 weeks | Built-in ADT for external call results; `externalCall!` desugars to match+revert |

**Key design decisions**:
- Storage layout uses max-width of all variants (like Rust enum layout)
- Exhaustiveness is free — Lean's kernel checks it during elaboration
- `YulStmt.switch` already exists in the Yul AST (used by the dispatcher) — no Yul-level changes needed

**Files touched**: `Macro/Syntax.lean`, `CompilationModel/Types.lean`, `Macro/Translate.lean`, `CompilationModel/Compile.lean`, `CompilationModel/Validation.lean`, `CompilationModel/AbiHelpers.lean`
**Estimated total**: 6–8 weeks

### Phase 6: Unsafe Blocks (Axis 2 remainder, #1728)

| Step | Feature | Effort | Detail |
|---|---|---|---|
| 6a | `unsafe "reason" do` syntax | 1 week | Add to grammar; track safe/unsafe context |
| 6b | Restricted operation gating | 1 week | Error if `delegatecall`/raw `sstore`/raw `mstore`/`rawLog` appears outside `unsafe` |
| 6c | Trust report + deny flag | 0.5 weeks | Each `unsafe` block → `--trust-report` entry; `--deny-unsafe` flag |

**Files touched**: `Macro/Syntax.lean`, `Macro/Translate.lean`, trust report infrastructure
**Estimated total**: 2 weeks

---

## Total Estimated Timeline

| Phase | Axis | Weeks | Parallelizable with |
|---|---|---|---|
| 1 | Effect system (#1729) | 3–4 | — |
| 2 | CEI + access control (#1728) | 4 | Phase 3 |
| 3 | Newtypes (#1727) | 2–3 | Phase 2 |
| 4 | Namespaced storage (#1730) | 2–3 | Phase 5 |
| 5 | ADTs + Result types (#1727) | 6–8 | Phase 4 |
| 6 | Unsafe blocks (#1728) | 2 | Phase 5 |

**Critical path**: Phase 1 → Phase 2 → Phase 5 (13–16 weeks)
**With parallelization**: ~12–14 weeks total

## Integration with #1724 Parity Waves

| #1724 Wave | Language Design Enrichment |
|---|---|
| Wave 1: Type System (widths, enum) | + Newtypes (Phase 3), ADTs (Phase 5) |
| Wave 2: Control Flow & Safety | + CEI (Phase 2), `@[requires]` (Phase 2), effect annotations (Phase 1) |
| Wave 3: Storage | + EIP-7201 namespaces (Phase 4) |
| Wave 4: ABI & Memory | + `Call.Result` + `!` sugar (Phase 5) |
| Wave 5: Composition | + `unsafe` blocks (Phase 6) |
