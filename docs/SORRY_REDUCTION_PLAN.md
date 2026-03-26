# Sorry Reduction Plan — Pass 5

## Current State (as of commit a4c29009)

**Active `sorry`**: 10 (all in `GenericInduction.lean`)
**TYPESIG_SORRY blocks**: ~60 commented-out theorems with broken type signatures
**Build status**: Green (compiles with warnings only)

## Progress (Pass 5)

| Commit | Sorries | What was proved |
|--------|---------|-----------------|
| Start | 44 | — |
| `5cefbc49` | 39 | `compiledStmtStep` + cascade for mstore and tstore (−5) |
| `2adf22f7` | 33 | setMappingChain + setMapping2 preserves + cascades (−6) |
| `a4d79b2b` | 32 | `compiledStmtStep_setStorage_singleSlot` + singleton cascade (−1) |
| `aa4cbd18` | 26 | scope-independence of compileStmt/compileStmtList success (−6) |
| `07ff14c6` | 19 | removed inScopeNames indirection, proved 4 generic induction theorems (−7) |
| `d47c51fd` | 18 | stmtListGenericCore_of_supportedStmtList_of_surface by induction (−1) |
| Various | 13 | helper-free/surface/legacy bridge chain, exec with helpers and helper-IR (−5) |
| `a4c29009` | 10 | bridge theorems (LegacyCompatible + CallsDisjoint) + 3 downstream (−3) |

## Remaining 10 Sorries — All Architecturally Blocked

Every remaining sorry depends on fundamental design issues that cannot be resolved
by proof work alone. They require either upstream code changes or new axioms.

### 1. ExprCompileCore false theorem (line 2725)
**Theorem**: `exprCompileCore_of_exprTouchesUnsupportedContractSurface`
**Blocker**: `exprTouchesUnsupportedContractSurface` returns `false` for `sdiv`, `smod`,
`sgt`, `slt`, but source semantics returns `none` for those ops. This makes the theorem
genuinely unprovable — `ExprCompileCore` constructors would need to handle operations
whose semantics are intentionally unsupported.
**Fix**: Add constructors to `ExprCompileCore` for all operators that pass the surface
check, plus their `eval_compileExpr_core` correctness proofs. Large cascading effort.

### 2. Identifier shapes (line 5950)
**Theorem**: `validateIdentifierShapes_fieldName_avoidReservedCompilerPrefix`
**Blocker**: Claims no field name starts with `"__"`, but `__immutable_*` fields are
explicitly allowed by the validation pipeline.
**Fix**: Thread stronger field-shape classification that distinguishes mutable vs
immutable fields through the generic induction scope invariant.

### 3. Mapping slot modulus — setMappingWord (line 7204)
**Theorem**: `compiledStmtStep_setMappingWord_singleSlot_of_slotSafety_preserves`
**Blocker**: In the `wordOffset ≠ 0` branch, needs
`solidityMappingSlot slot keyNat + wordOffset < evmModulus` (2^256).
`solidityMappingSlot` is defined via keccak256 FFI, making its output size opaque.
**Fix**: Add axiom `solidityMappingSlot_lt_evmModulus` or prove keccak output bounds.

### 4. Mapping slot modulus — setMappingPackedWord (line 7398)
**Theorem**: `compiledStmtStep_setMappingPackedWord_singleSlot_of_slotSafety_preserves`
**Blocker**: Same keccak FFI modulus issue as #3, plus the proof needs rewriting from
the old `evalExpr : Nat` API to the current `evalExpr : Option Nat` API. Even with the
API fix, the `wordOffset ≠ 0` sub-goals would remain sorry'd.

### 5. Mapping slot modulus — setMapping2Word (line 7781)
**Theorem**: `compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves`
**Blocker**: Same keccak FFI modulus issue as #3 (double-nested mapping slot).

### 6. Mapping slot modulus — setMapping2Word variant (line 8193)
**Theorem**: `compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves` (wordOffset≠0)
**Blocker**: Same keccak FFI modulus issue.

### 7. Mapping slot modulus — setMapping2Word variant (line 8443)
**Theorem**: `compiledStmtStep_setMapping2Word_singleSlot_of_slotSafety_preserves` (wordOffset≠0)
**Blocker**: Same keccak FFI modulus issue.

### 8. setStorage with aliasSlots (line 8813)
**Theorem**: `compiledStmtStep_setStorage_of_validateIdentifierShapes`
**Blocker**: The `aliasSlots ≠ []` branch needs `compiledStmtStep_setStorage_aliasSlots`
which is TYPESIG_SORRY'd. The `aliasSlots = []` case is provable but can't close the
overall theorem without the non-empty case.

### 9. setStorageAddr — Address modulus (line 9703)
**Theorem**: `compiledStmtStep_setStorageAddr_singleSlot_of_slotSafety`
**Blocker**: `runtimeStateMatchesIR_writeAddressSlot` needs `value < Address.modulus`
(2^160) but `evalExpr` only gives `< evmModulus` (2^256). Source semantics truncates
to 160 bits via `wordToAddress` but IR stores full 256 bits.
**Fix**: Either add a truncation step in the IR compilation of address storage, or
add a hypothesis that the value is already within address range.

### 10. setMappingPackedWord singleton (line 10307)
**Theorem**: `stmtListGenericCore_singleton_setMappingPackedWordSingle_of_slotSafety`
**Blocker**: Depends on #4 being resolved first (the `_preserves` theorem it wraps).

## Root Causes Summary

| Root Cause | Sorries Blocked | Fix Complexity |
|-----------|----------------|----------------|
| Keccak FFI opaque output bounds | #3, #4, #5, #6, #7, #10 | Need axiom or keccak bound proof |
| ExprCompileCore missing constructors | #1 | 20+ new constructors + proofs |
| `__immutable_*` field prefix | #2 | Validation pipeline change |
| Address modulus semantic mismatch | #9 | IR compilation change or hypothesis |
| TYPESIG_SORRY dependency | #8 | Type signature fix in wrapper |

## Conclusion

The sorry count cannot be reduced below 10 without architectural changes. All remaining
sorries are fundamentally blocked by design decisions (keccak FFI opacity, Address/Uint256
modulus mismatch, `__immutable_*` naming convention, and missing ExprCompileCore constructors).

The most impactful single fix would be adding an axiom `solidityMappingSlot_lt_evmModulus`
stating that keccak256 output is less than 2^256, which would unblock sorries #3-7 and #10
(6 of 10 remaining sorries).
