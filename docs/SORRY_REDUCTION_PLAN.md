# Sorry Reduction Plan — Pass 5

## Current State

**Active `by sorry`**: 32 (all in `GenericInduction.lean`)
**TYPESIG_SORRY blocks**: ~60 commented-out theorems with broken type signatures
  - `GenericInduction.lean`: ~30 blocks
  - `FunctionBody.lean`: 15 blocks
  - `Contract.lean`: 15 blocks
  - `Function.lean`: 2 blocks

**FunctionBody.lean**: Fully proven (0 active sorries)
**All contract proofs** (SimpleToken, Counter, Ledger, etc.): Fully proven

## Progress (Pass 5)

| Commit | Sorries | What was proved |
|--------|---------|-----------------|
| Start | 44 | — |
| `5cefbc49` | 39 | `compiledStmtStep` + cascade for mstore and tstore (−5) |
| `2adf22f7` | 33 | setMappingChain + setMapping2 preserves + cascades (−6) |
| `a4d79b2b` | 32 | `compiledStmtStep_setStorage_singleSlot` + singleton cascade (−1) |

### Key changes in pass 5
- Added `findFieldWriteSlots_of_findFieldWithResolvedSlot` bridge lemma
- Added `isMapping_false_of_findFieldWithResolvedSlot_uint256` in Types.lean
- Proved `compiledStmtStep_setStorage_singleSlot` with `hNotMapping` parameter
- Proved `stmtListGenericCore_singleton_setStorage_singleSlot`
- Proved mstore/tstore compiled step + cascade theorems
- Proved setMappingChain/setMapping2 preserves theorems + cascades

### Remaining 32 sorries — blocked categories
1. **Genuinely false** (line 2730): `ExprCompileCore` lacks constructors for `sdiv`, `smod`, etc.
2. **`__immutable_` architecture** (line 5955): `validateIdentifierShapes` permits `__immutable_*`
3. **Forward reference blocked** (6 at lines 9563–9756): cascade theorems reference helpers defined later in file
4. **Mapping slot modulus** (5 at lines 7209–8298, 5 at lines 10299–10522): keccak output opaque
5. **Address modulus** (via setStorageAddr): needs `value < 2^160` but only have `< 2^256`
6. **Scope-irrelevance** (3 at lines 11748–11769): `compileStmtList` uses `inScopeNames` vs `scope`
7. **Deep dependency chain** (9 at lines 10833–13577): exec/effectiveFields/function depend on upstream
8. **Commented-out structures**: several structures needed for TYPESIG_SORRY theorems are `-- SORRY'D:`
9. **setStorage existence** (line 8604): `compiledStmtStep_setStorage_of_validateIdentifierShapes` needs upstream

---

## Root Causes

Three root causes block nearly all remaining sorries:

### Root Cause A: `scopeNamesPresent` gap (blocks ~30 sorries + ~20 TYPESIG blocks)

`stmtNextScope scope stmt` computes `collectStmtNames stmt ++ scope`. For storage-mutating
statements, `collectStmtNames` includes the storage field name:

```
collectStmtNames (.setMappingUint fieldName key value) = fieldName :: collectExprNames key ++ collectExprNames value
```

But `scopeNamesPresent scope bindings` requires every name in `scope` to have a binding in
`runtime.bindings`. Storage field names are NOT local variable bindings — they reference
persistent storage. So proofs can't show `scopeNamesPresent (stmtNextScope scope stmt) runtime.bindings`
for any storage-mutating statement.

**Fix**: Remove the leading `field` from `collectStmtNames` for storage-mutating cases in
`ValidationHelpers.lean`. The field name is a storage reference, not a binding name.

**Affected statements**: `setStorage`, `setStorageAddr`, `setMapping`, `setMappingUint`,
`setMappingChain`, `setMappingWord`, `setMappingPackedWord`, `setStructMember`,
`setMapping2`, `setMapping2Word`, `setStructMember2`, `storageArrayPush`, `mstore`, `tstore`

**Ripple effects**: Changing `collectStmtNames` will require updating:
- `foldl_stmtNextScope_*` lemmas
- Any theorem that pattern-matches on `collectStmtNames` or `stmtNextScope` for these cases
- Possibly `collectExprNames` if field names in sub-expressions also leak through

### Root Cause B: `ExprCompileCore` missing constructors (blocks 1 sorry + downstream)

`exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false` (line 2733) claims that
if an expression doesn't touch unsupported contract surface, then `ExprCompileCore` holds.
This is **genuinely false** because `ExprCompileCore` lacks constructors for 20+ operators
that pass the surface check: `sdiv`, `smod`, `bitAnd`, `bitOr`, `bitXor`, `bitNot`, `sgt`,
`slt`, `shl`, `shr`, `sar`, `signextend`, `min`, `max`, `wMulDown`, `wDivUp`, `mulDivDown`,
`mulDivUp`, `ite` (expression-level).

**Fix**: Either:
- (a) Add constructors to `ExprCompileCore` in `ExprCore.lean` for each missing operator,
  plus corresponding `compileExpr` and `eval_compileExpr_core` correctness proofs, OR
- (b) Tighten `exprTouchesUnsupportedContractSurface` to return `true` for operators not
  in `ExprCompileCore`, narrowing the scope of whole-contract theorems

### Root Cause C: TYPESIG_SORRY `= 0` on `Option Nat` (blocks 76 commented-out theorem blocks)

During an earlier migration from `Nat` to `Option Nat` for `evalExpr`, many theorem
signatures were left with `evalExpr ... = 0` or `evalExpr ... != 0` which requires
`OfNat (Option Nat) 0` — a type error. The correct signatures use
`evalExpr ... = some condValue` with a separate `condValue = 0` or `condValue != 0` hypothesis.

**Fix**: For each TYPESIG_SORRY block, update the type signature to use the split
`some condValue` pattern. Many already have active proven replacements (5 in FunctionBody.lean).
The remaining ones need their signatures corrected and proofs updated.

---

## Sorry Inventory

### Category 1: Proofs blocked by `scopeNamesPresent` gap (Root Cause A)

**Prerequisite**: Fix `collectStmtNames` in `ValidationHelpers.lean`

#### Tier 1 — Storage mutation `_preserves` theorems (9 active sorries)
These are the leaf-level proofs that show compiled storage writes preserve semantics.

| Line | Theorem | Statement type |
|------|---------|---------------|
| 6299 | `compiledStmtStep_setMappingUint_singleSlot_of_slotSafety_preserves` | setMappingUint |
| 6433 | `compiledStmtStep_setMappingChain_singleSlot_of_slotSafety_preserves` | setMappingChain |
| 6566 | `compiledStmtStep_setMapping_singleSlot_of_slotSafety_preserves` | setMapping |
| 6700 | `compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves` | setMappingWord |
| 6926 | `compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves` | setMappingPackedWord |
| 7235 | `compiledStmtStep_setStructMember_singleSlot_of_slotSafety_preserves` | setStructMember |
| 7391 | `compiledStmtStep_setMapping2_singleSlot_of_slotSafety_preserves` | setMapping2 |
| 7566 | `compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves` | setMapping2Word |
| 7758 | `compiledStmtStep_setStructMember2_singleSlot_of_slotSafety_preserves` | setStructMember2 |

All have SORRY'D proof bodies showing the intended proof structure.

#### Tier 1b — TYPESIG_SORRY storage mutation theorems (~12 blocks)
The corresponding `CompiledStmtStep` wrappers and `_singleSlot_preserves` for setStorage,
setStorageAddr, mstore, tstore. Need type sig fixes + the `scopeNamesPresent` fix.

#### Tier 2 — `compiledStmtStep_setStorage` existence chain (1 active sorry)

| Line | Theorem |
|------|---------|
| 8015 | `compiledStmtStep_setStorage_of_validateIdentifierShapes` |

Depends on `compiledStmtStep_setStorage_singleSlot` (TYPESIG_SORRY). Has SORRY'D proof body.

#### Tier 3 — Singleton StmtListGenericCore theorems (13 active sorries)

| Line | Theorem | Depends on |
|------|---------|------------|
| 8860 | `stmtListGenericCore_singleton_setStorage_singleSlot` | Tier 1b |
| 8887 | `stmtListGenericCore_singleton_setStorageAddr_singleSlot` | Tier 1b |
| 8907 | `stmtListGenericCore_singleton_mstore_single` | Tier 1b |
| 8929 | `stmtListGenericCore_singleton_tstore_single` | Tier 1b |
| 9792 | `stmtListGenericCore_singleton_setMappingUint_singleSlot` | Tier 1 |
| 9829 | `stmtListGenericCore_singleton_setMappingChain_singleSlot` | Tier 1 |
| 9864 | `stmtListGenericCore_singleton_setMapping_singleSlot` | Tier 1 |
| 9900 | `stmtListGenericCore_singleton_setMappingWord_singleSlot` | Tier 1 |
| 9942 | `stmtListGenericCore_singleton_setMappingPackedWord_singleSlot` | Tier 1 |
| 9988 | `stmtListGenericCore_singleton_setStructMember_singleSlot` | Tier 1 |
| 10033 | `stmtListGenericCore_singleton_setMapping2_singleSlot` | Tier 1 |
| 10081 | `stmtListGenericCore_singleton_setMapping2Word_singleSlot` | Tier 1 |
| 10134 | `stmtListGenericCore_singleton_setStructMember2_singleSlot` | Tier 1 |

#### Tier 4 — Composite require+storage theorems (6 active sorries)

| Line | Theorem |
|------|---------|
| 8961 | `stmtListGenericCore_of_requireClausesThenSetStorageLiteral` |
| 9032 | `stmtListGenericCore_of_requireClausesThenLetSetStorageLocalLiteral` |
| 9069 | `stmtListGenericCore_of_requireClausesThenLetAssignSetStorageLocalLiteral` |
| 9111 | `stmtListGenericCore_of_requireClausesThenLetAssignAddSetStorageLocalLiteral` |
| 9157 | `stmtListGenericCore_of_requireClausesThenLetAssignSubSetStorageLocalLiteral` |
| 9203 | `stmtListGenericCore_of_requireClausesThenLetAssignMulSetStorageLocalLiteral` |

All depend on Tier 3 singleton theorems + `stmtListGenericCore_append` (proven).

#### Tier 5 — Main interface theorem (1 active sorry)

| Line | Theorem |
|------|---------|
| 10421 | `stmtListGenericCore_of_supportedStmtList_of_surface` |

Depends on all Tier 3 + Tier 4 theorems. This is the main gateway theorem.

### Category 2: Proofs provable NOW (3 active sorries)

These are not blocked by any root cause. They just need file reorganization (they're
defined before their dependencies in the file).

| Line | Theorem | Fix |
|------|---------|-----|
| 8948 | `stmtListGenericCore_of_requireClausesOnly` | Move after `stmtListGenericCore_of_stmtListCompileCore` (line 11114) |
| 8981 | `stmtListGenericCore_of_requireClausesThenReturnLiteral` | Same + uses `stmtListGenericCore_append` |
| 9002 | `stmtListGenericCore_of_requireClausesThenLetReturnLocalLiteral` | Same |

All have complete SORRY'D proof bodies.

### Category 3: Identifier shapes theorem (1 active sorry)

| Line | Theorem |
|------|---------|
| 5965 | `validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix` |

**What it claims**: If `validateIdentifierShapes` succeeds, no field name starts with `"__"`.
**Why it's stuck**: `validateIdentifierShapes` was changed to permit `"__"`-prefixed field
names for internal immutable storage. The theorem statement is now too strong.
**Fix**: Thread stronger field-shape classification through the generic induction scope
invariant. Requires spec change to distinguish mutable vs immutable fields in the
validation pipeline.

### Category 4: Downstream cascade theorems (blocked by Categories 1/3)

These are higher-level theorems that would be provable once their dependencies are fixed.

#### Compilation success (3 active sorries)

| Line | Theorem | Blocked by |
|------|---------|------------|
| 11282 | `compileStmtList_ok_of_stmtListGenericCore` | Need induction proof |
| 11293 | `compileStmtList_ok_of_stmtListGenericWithHelpers` | Depends on 11282 |
| 11306 | `compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR` | Depends on 11293 |

#### Execution with fuel (2 active sorries)

| Line | Theorem | Blocked by |
|------|---------|------------|
| 11539 | `exec_compileStmtList_generic_sizeOf_extraFuel_step` | Depends on 11282 |
| 11695 | `exec_compileStmtList_generic_with_helpers_sizeOf_extraFuel_step` | Depends on 11293 |

#### State matching (2 active sorries)

| Line | Theorem | Blocked by |
|------|---------|------------|
| 12167 | `stmtListHelperFreeStepInterface_of_supportedStmtList_of_surface` | Depends on Tier 5 |
| 12262 | `stmtListHelperFreeStepInterface_of_supportedStmtList_of_featureClosed` | Depends on 12167 |

#### Top-level function body correctness (4 active sorries)

| Line | Theorem | Blocked by |
|------|---------|------------|
| 12648 | `supported_function_body_correct_from_exact_state_generic` | All above |
| 12712 | `supported_function_body_correct_from_exact_state_generic_with_helpers` | 12648 |
| 13001 | `supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir` | 12712 |
| 13181 | `supported_function_body_correct_from_exact_state` | 13001 |

### Category 5: `ExprCompileCore` false theorem (Root Cause B)

| Line | Theorem |
|------|---------|
| 2733 | `exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false` |

Genuinely false. Fix requires expanding `ExprCompileCore` with 20+ new constructors.

---

## Recommended Execution Order

### Phase 1: Quick wins (no dependency changes needed)
1. Prove 3 `requireClauses*` theorems (Category 2) — relocate after dependencies
2. **Impact**: 44 → 41 active sorries

### Phase 2: Fix `scopeNamesPresent` gap (Root Cause A)
1. Modify `collectStmtNames` in `ValidationHelpers.lean` to exclude field names
2. Propagate changes through `stmtNextScope`-dependent lemmas
3. Uncomment + prove Tier 1 `_preserves` theorems (9 sorries)
4. Uncomment + fix TYPESIG_SORRY `_singleSlot` wrapper theorems (Tier 1b)
5. Prove Tier 2 existence chain (1 sorry)
6. Prove Tier 3 singleton theorems (13 sorries)
7. Prove Tier 4 composite theorems (6 sorries)
8. Prove Tier 5 main interface theorem (1 sorry)
9. **Impact**: 41 → 11 active sorries

### Phase 3: Fix TYPESIG_SORRY blocks in FunctionBody.lean
1. Fix type signatures for the 10 `_of_scope` theorems (let, assign, require chains)
2. These are independently provable — they don't depend on `scopeNamesPresent` gap
3. **Impact**: Reduces TYPESIG_SORRY count by 10

### Phase 4: Prove downstream cascade (Category 4)
1. `compileStmtList_ok_of_stmtListGenericCore` — needs new induction proof
2. Cascade: execution, state matching, top-level correctness (11 sorries)
3. **Impact**: 11 → 0 active sorries

### Phase 5: Fix identifier shapes (Category 3)
1. Strengthen field-shape classification in validation pipeline
2. Prove `validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix`
3. **Impact**: 1 sorry (already counted in Phase 4 cascade)

### Phase 6: Expand `ExprCompileCore` (Root Cause B)
1. Add 20+ constructors to `ExprCompileCore` in `ExprCore.lean`
2. Prove `compileExpr` and `eval_compileExpr_core` for each
3. Prove `exprCompileCore_of_exprTouchesUnsupportedContractSurface_eq_false`
4. Uncomment TYPESIG_SORRY theorems that depend on it
5. **Impact**: Removes the last false theorem + unblocks Contract.lean TYPESIG_SORRYs

### Phase 7: Fix remaining TYPESIG_SORRY blocks
1. Contract.lean: 15 blocks (depend on Phases 2, 5, 6)
2. Function.lean: 2 blocks (depend on Phase 4)
3. GenericInduction.lean: remaining TYPESIG blocks
4. **Impact**: 0 TYPESIG_SORRY blocks remaining

---

## Parallelism Opportunities

These can be worked on simultaneously:

| Stream | What | Blocked by |
|--------|------|------------|
| A | Phase 1 (requireClauses quick wins) | Nothing |
| B | Phase 2 (scopeNamesPresent fix) | Nothing |
| C | Phase 3 (FunctionBody TYPESIG fixes) | Nothing |
| D | Phase 6 (ExprCompileCore expansion) | Nothing |
| E | Phase 5 (identifier shapes) | Nothing |
| F | Phase 4 (downstream cascade) | Phases 2, 3 |
| G | Phase 7 (remaining TYPESIG) | Phases 2, 4, 5, 6 |

Streams A through E are fully independent and can run in parallel.
