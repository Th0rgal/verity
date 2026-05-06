# Verity Roadmap

**Goal**: End-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Current Status

- ✅ **Layer 1 Complete**: see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md) for the current theorem totals and contract coverage table
- 🟢 **Layer 2 Generic Theorem**: the generic whole-contract `CompilationModel.compile` theorem is proved for the current supported fragment; theorem-shape work is complete under [#1510](https://github.com/lfglabs-dev/verity/issues/1510), and widening/completeness work now follows the ranked plan in [#1630](https://github.com/lfglabs-dev/verity/issues/1630)
- ✅ **Layer 3 Complete**: All 8 statement equivalence proofs + universal dispatcher (PR #42)
- ✅ **Property Testing**: see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md) for current coverage totals and exclusions
- ✅ **Differential Testing**: Production-ready with 70k+ tests
- ✅ **Trust Reduction Phase 1**: keccak256 axiom + CI validation (PR #43, #46)
- ✅ **External Linking**: Cryptographic library support (PR #49)
- ✅ **CompilationModel Real-World Support**: Loops, branching, arrays, events, multi-mappings, internal call mechanics, verified extern linking (#153, #154, #179, #180, #181, #184)

---

## Migration + Optimization Execution Tracker (P0 -> P2)

This tracker is the execution order for migration-oriented compiler work. Later phases are blocked on earlier phases unless noted.

| Priority | Milestone | Issues | Dependency | Exit Criteria |
|---|---|---|---|---|
| P0 | Canonical equivalence baseline | [#581](https://github.com/lfglabs-dev/verity/issues/581) | none | Canonical Yul equivalence check in CI for at least one real contract pair |
| P1 | Proven optimization foundation | [#582](https://github.com/lfglabs-dev/verity/issues/582), [#583](https://github.com/lfglabs-dev/verity/issues/583), [#584](https://github.com/lfglabs-dev/verity/issues/584) | blocked by #581 | Proven patch framework + initial patch pack + warning non-regression gate |
| P2 | Interop + verification docs hardening | [#585](https://github.com/lfglabs-dev/verity/issues/585), [#586](https://github.com/lfglabs-dev/verity/issues/586) | blocked by P0/P1 outputs | Generated verification artifact consumed by docs + published interop support profile |

Current P0 baseline artifact coverage:
- `artifacts/evmyullean_capability_report.json` tracks builtin overlap boundaries and explicit unsupported adapter nodes.
- `artifacts/evmyullean_unsupported_nodes.json` provides a dedicated machine-readable unsupported-node list for adapter-lowering gaps.
- `artifacts/evmyullean_adapter_report.json` tracks adapter AST-lowering coverage (`supported`/`partial`/`gap`) and runtime seam status.

Current P1 foundation coverage (Issue #582):
- Deterministic expression patch DSL + pass engine in `Compiler/Yul/PatchFramework.lean`
- Initial patch pack in `Compiler/Yul/PatchRules.lean` with explicit metadata (`pattern`, `rewrite`, `side_conditions`, `proof_id`, `pass_phase`, `priority`)
- Proof hooks + preservation theorems in `Compiler/Proofs/YulGeneration/PatchRulesProofs.lean`
- Opt-in compiler path via `Compiler.emitYulWithOptions` (`YulEmitOptions.patchConfig`)
- Report-capable compiler path via `Compiler.emitYulWithOptionsReport` to surface patch manifest/iteration metadata to CI and tooling
- `verity-compiler` patch coverage emission (`--patch-report`) now writes per-contract/rule TSV output and CI uploads it as an artifact for Issue #583 tuning
- Static gas delta gate for patch impact (`scripts/check_patch_gas_delta.py`) now compares baseline vs patch-enabled reports in CI with median/p90 non-regression and measurable-improvement requirements
- CI now runs `check_yul.py` + `check_gas.py coverage` on `artifacts/yul-patched` as part of Issue #582 fail-closed hardening for patch-enabled output, including filename-set parity checks against baseline Yul output
- CI now runs a dedicated Foundry patched-Yul smoke gate (`DIFFTEST_YUL_DIR=artifacts/yul-patched`) so differential/property harnesses execute against patch-enabled output

Execution policy:
1. Do not start patch-pack expansion in `#583` before `#582` proof hooks are merged.
2. Treat `#584` as a release gate for ongoing compiler work after initial warning cleanup lands.
3. Enforce Lean warning non-regression via `artifacts/lean_warning_baseline.json` + CI check (`scripts/check_lean_warning_regression.py`) until warning count reaches zero.
4. Treat `#585` docs generation as authoritative source for public metrics before broader docs expansion.
5. Keep issue bodies and this section synchronized when scope/order changes.

### Solidity Interop Profile (Issue #586)

Interop priority is based on migration friction observed in the Morpho integration path.

Status legend:
- `supported`: available end-to-end for migration use
- `partial`: usable with limits or missing proof/diagnostics coverage
- `unsupported`: no first-class support yet

| Priority | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
|---|---|---|---|---|---|---|
| 1 | Custom errors + typed revert payloads | partial | partial | n/a | partial | partial |
| 2 | Low-level calls (`call`/`staticcall`/`delegatecall`) + returndata handling | partial | partial | n/a | partial | partial |
| 3 | `fallback` / `receive` / payable entrypoint modeling | partial | partial | n/a | partial | partial |
| 4 | Full event ABI parity (indexed dynamic + tuple hashing) | supported | supported | supported | supported | supported |
| 5 | Storage layout controls (packed fields + explicit slot mapping) | partial | partial | partial | partial | partial |
| 6 | ABI JSON artifact generation | partial | partial | n/a | partial | partial |

Recent progress for storage layout controls (`#623`):
- `CompilationModel.Field` now supports optional explicit slot assignment (`slot := some <n>`), with backward-compatible positional slots when omitted.
- Compiler now fails fast on conflicting effective slot assignments with an issue-linked diagnostic.
- `CompilationModel.Field` now supports compatibility mirror-write slots (`aliasSlots := [...]`), so `setStorage`/`setMapping`/`setMapping2` write to canonical and alias slots in one declarative policy.
- `CompilationModel` now supports slot remap policies (`slotAliasRanges := [{ sourceStart := a, sourceEnd := b, targetStart := c }, ...]`) so compatibility windows like `8..11 -> 20..23` can be declared once and applied automatically to canonical field writes.
- `CompilationModel` now supports declarative reserved storage slot ranges (`reservedSlotRanges := [{ start := a, end_ := b }, ...]`) with compile-time overlap checks and fail-fast diagnostics when field canonical/alias write slots intersect reserved intervals.
- `CompilationModel.Field` now supports packed subfield placement (`packedBits := some { offset := o, width := w }`) so multiple fields can share a slot with disjoint bit ranges; codegen performs masked read-modify-write updates and masked reads directly from layout metadata.
- `FieldType.mappingStruct` / `FieldType.mappingStruct2` plus `Expr.structMember` / `Stmt.setStructMember` now make struct-valued mappings and packed submembers first-class in the CompilationModel surface, and `verity_contract` now exposes matching `MappingStruct(...)` / `MappingStruct2(...)` storage declarations so Morpho-style layouts no longer require handwritten CompilationModel shims.
- Migration-faithful packed-slot writes can now be expressed without unsafe raw Yul: build the packed word with first-class word operations and call `setPackedStorage root offset word`, which lowers through `Stmt.setStorageWord` to an explicit full-word write at `root.slot + offset`.
- `verity_contract` now accepts scalar `Int256` storage fields as signed views over normal 256-bit storage words. The compiler-facing model stays word-level (`FieldType.uint256`), while macro typechecking preserves signed reads/writes at the DSL boundary.

Recent progress for low-level calls + returndata handling (`#622`):
- `CompilationModel.Expr` now supports first-class low-level call primitives (`call`, `staticcall`, `delegatecall`) with explicit gas/value/target/input/output operands and deterministic Yul lowering.
- `CompilationModel.Expr.returndataSize`, `Stmt.returndataCopy`, and `Stmt.revertReturndata` now provide first-class returndata access and revert-data forwarding without raw Yul builtin injection.
- `CompilationModel.Expr.returndataOptionalBoolAt(outOffset)` now provides a first-class ERC20 compatibility helper for optional return-data bool decoding (`returndatasize()==0 || (returndatasize()==32 && mload(outOffset)==1)`), so low-level token call acceptance paths can be expressed without raw Yul builtins.
- `Compiler.Modules.Calls.callWithValue` now provides a standard assumed-status ECM for generic `call{value:v}` over an already prepared calldata slice, with revert-data bubbling. `Calls.callWithValueBytes` adds the higher-level `(target, value, data)` wrapper for `Bytes` payloads by copying the payload to memory before calling. This covers adapter/router patterns that need arbitrary calldata and ETH value transfer while keeping the trust surface visible in reports, with distinct `callWithValue` / `callWithValueBytes` module names in audit manifests.
- `verity-compiler --trust-report <path>` now emits a machine-readable per-contract trust surface covering low-level mechanics usage, raw `rawLog` event emission, linked external assumptions, ECM axioms, explicit `proved` / `assumed` / `unchecked` proof-status buckets for foreign surfaces, constructor/function-level `usageSites`, site-localized `localObligations` for unsafe/refinement escape hatches, and dedicated `notModeledEventEmission` / `notModeledProxyUpgradeability` / `partiallyModeledLinearMemoryMechanics` / `partiallyModeledRuntimeIntrospection` slices for the current event, proxy/upgradeability, memory/ABI, and runtime-context proof gaps; `--verbose` now includes matching human-readable summaries, `--deny-unchecked-dependencies` upgrades unchecked foreign usage from a warning to a fail-closed verification gate with site-localized diagnostics, `--deny-assumed-dependencies` provides a proof-strict gate for any remaining assumed or unchecked foreign dependency, `--deny-axiomatized-primitives` fails closed on contracts that still rely on axiomatized primitives such as `keccak256`, `--deny-local-obligations` fails closed on any undischarged local unsafe/refinement obligation, `--deny-linear-memory-mechanics` fails closed on contracts that still rely on partially modeled linear-memory mechanics, `--deny-event-emission` fails closed on raw `rawLog` event emission, `--deny-low-level-mechanics` fails closed on first-class low-level call / returndata usage, `--deny-proxy-upgradeability` fails closed on `delegatecall`-based proxy / upgradeability mechanics tracked under issue `#1420`, and `--deny-runtime-introspection` does the same for partially modeled runtime-introspection primitives.
- Raw `Expr.externalCall` interop names for low-level/builtin opcodes remain fail-fast rejected, preserving explicit migration diagnostics while the first-class surface continues to expand.

Recent progress for dynamic ABI-shaped parameters:
- `verity_contract` now accepts dynamic array parameters whose element type is a static tuple of ABI words, e.g. `Array (Tuple [Uint256, Uint256, Int256])`, on tuple destructuring and tuple-return `arrayElement` paths. Those paths lower to checked word reads with the tuple element stride, which covers Solidity memory arrays of small fixed-size structs such as `CurveCut[]`; plain scalar `arrayElement` remains limited to single-word static element arrays.
- `verity_contract` now accepts named `struct` declarations for function parameters as ABI tuple aliases. Executable contracts get Lean structures and field projection syntax, while the compilation model keeps the existing tuple ABI lowering. Nested static struct fields are supported for parameter field reads, covering the #1750 TermMax-style `config.feeConfig.borrowTakerFeeRatio` shape.
- Top-level named `struct` storage fields remain unsupported (#1758) and now fail fast with a targeted diagnostic. Until first-class top-level storage structs exist, flatten nested Solidity storage structs into explicit scalar fields with fixed slots; use `MappingStruct(...)` / `MappingStruct2(...)` only for struct-valued mappings.

Recent progress for arithmetic modeling:
- `Stdlib.Math` now exposes `mulDiv512Down?` and `mulDiv512Up?` as proof-facing full-precision multiply-divide helpers. They compute `a * b` in unbounded natural-number precision and return `none` only when the divisor is zero or the final floor/ceil quotient does not fit in `uint256`, removing the artificial intermediate-product overflow hypothesis when modeling Solidity `Math.mulDiv` behavior. A compiled Yul primitive using the usual 512-bit division algorithm is still tracked by #1761.
- ABI artifact emission now reflects explicit function mutability markers (`isView`, `isPure`) as `stateMutability: "view" | "pure"` in generated JSON.
- Internal function-pointer parameters remain unsupported at the `verity_contract` boundary and now fail fast with an issue-linked diagnostic (#1747). Until the CompilationModel gets first-class higher-order internal calls, model these cases with an explicit mode/enum plus direct internal helper calls, or inline each helper call at the call site.

Recent progress for custom errors (`#586`):
- `Stmt.requireError` / `Stmt.revertError` now support ABI encoding for tuple/fixed-array/array/bytes payloads (including nested dynamic composites) when arguments are direct `Expr.param` references.
- Static scalar payload args remain expression-friendly (`uint256`, `address`, `bool`, `bytes32`), while composite/dynamic payload args fail fast with issue-linked diagnostics when not provided as direct parameter references.

Recent progress for ABI JSON artifact generation (`#688`):
- `verity-compiler --abi-output <dir>` emits one `<Contract>.abi.json` file per compiled CompilationModel in the supported compilation path.

Recent progress for ABI-level string support (`#1159`):
- `ParamType.string` now compiles through the existing dynamic-bytes ABI path for macro parsing/lowering, calldata loading, ABI JSON/signature rendering, `Stmt.returnBytes`, event emission, and custom errors.
- Direct parameter `String` / `Bytes` equality and inequality now lower through the dedicated dynamic-bytes equality helper on both the macro and compilation-model paths.
- This support is intentionally ABI-only for now: Solidity-style string storage/layout and typed-IR string lowering remain unsupported and should continue to fail fast with explicit diagnostics.

Recent progress for constants and immutables (`#1569`):
- `verity_contract` now exposes `constants` and `immutables` sections in the macro surface, with smoke, invariant, round-trip, and generated Foundry property coverage.
- Constants are validated as compile-time expressions, elaborated as Lean definitions, and can reference earlier constants while failing fast on runtime-dependent expressions and recursive definitions.
- Immutables support `Uint256`, `Uint8`, `Address`, `Bytes32`, and `Bool` values bound from constructor-visible expressions, materialized as hidden storage-backed fields in the compilation model, and reintroduced as read-only bindings in function bodies.
- Name-collision and type-mismatch diagnostics now fail fast for storage/constant/immutable/function conflicts and unsupported immutable payload types.

Delivery policy for unsupported features:
1. Compiler diagnostics must identify the exact unsupported construct.
2. Error text must suggest the nearest currently-supported pattern.
3. Error text must include the tracking issue reference.

### Unlink Audit Readiness: Verity-Core Scope

The Unlink audit should keep Verity focused on generic Solidity-modeling
capabilities and move Unlink-specific cryptographic or protocol assumptions to
a separate `unlink-verity` package. Verity should not grow built-in Poseidon,
Permit2, Lazy-IMT, or Groth16 verifier semantics. Instead, Verity should provide
the generic call, ABI, loop, helper-return, and trust-report surfaces needed for
a clean line-by-line model, while `unlink-verity` declares the protocol-specific
assumed boundaries with explicit axiom names and proof-status tags.

Priority work for Verity core:

| Priority | Work item | Scope | Exit criteria |
|---|---|---|---|
| P0 | ETH-aware generic external call ECM | Add a reusable ECM for Solidity-style arbitrary `call{value: v}(data)` with explicit target, ETH value, input offset/size or bytes-like calldata source, returndata bubbling on failure, and configurable output/returndata handling. | `Compiler/Modules/Calls.lean` exposes `bubblingValueCall` for explicit memory-slice calls and `bubblingValueCallNoOutput` / `bubblingValueCallNoOutputModule` for adapter/router calls that ignore successful returndata, including `verity_contract` `ecmDo` usage; generated Yul forwards revert returndata exactly; CEI/mutability/trust-report metadata are covered by compile-time tests for call lowering, value forwarding, revert bubbling, argument validation, and assumption reporting. |
| P0 | ECM and trust-boundary documentation | Make the Verity-core vs `unlink-verity` package split explicit. | `docs/EXTERNAL_CALL_MODULES.md`, `docs/INTERPRETER_FEATURE_MATRIX.md`, and this roadmap document which generic surfaces are modeled by Verity and which Unlink-specific dependencies should be package-local assumptions. |
| P1 | `forEach` mutable-local verification/docs | Confirm accumulator-style loop bodies can update local variables via `Stmt.assignVar`, and document the current macro-source limitation. | A feature test demonstrates `Stmt.letVar ...; Stmt.forEach ... [Stmt.assignVar ...]` lowering to Yul assignment inside the loop; macro docs state that `let mut` reassignment from inside a `verity_contract` `forEach` body is still rejected by the executable fallback, so source authors should use scratch memory until that limitation is removed. |
| P1 | Multi-value internal return verification/docs | Confirm helper functions can return multiple values and callers can bind them cleanly from macro syntax. | A smoke or feature test demonstrates `_buildPublicSignals`-style helper returns, including `Stmt.internalCallAssign` or equivalent macro syntax; docs point users to the pattern. |
| P1 | `abiEncodePacked` helper | Reduce hash-preimage offset mistakes in ZK/audit models. | `Compiler.Modules.Hashing.abiEncodePackedWords` covers the static 32-byte word subset, with `abiEncodePacked` as a short alias for the same semantics; `Compiler.Modules.Hashing.abiEncodePackedStaticSegments` covers static 1- to 32-byte segments such as address-sized values. Both lower to contiguous memory writes plus exact-length `keccak256` and have generated-Yul/trust-report tests. Dynamic Solidity packed encoding remains future work. |
| P1 | `sha256` / `sha256Packed` helper | Avoid hand-rolled SHA-256 precompile calls in public-signal construction. | `Compiler.Modules.Precompiles.sha256Memory` covers existing memory slices, with `sha256` as a short alias; `Compiler.Modules.Hashing.sha256PackedWords` covers static-word packed preimages, with `sha256Packed` as a short alias; `Compiler.Modules.Hashing.sha256PackedStaticSegments` covers static 1- to 32-byte segments. SHA-256 helpers route through precompile 0x02 with failure reverts and generated-Yul/trust-report tests. |
| P2 | BN254 scalar field helper | Improve readability of circuit-facing reductions. | `Verity.Stdlib.Math` exposes documented `SNARK_SCALAR_FIELD` and `modField` helpers with basic simp lemmas. |

Already-supported items that should not become new roadmap work:

- Named struct field access for calldata array elements is already available
  through `struct` declarations and `arrayElement` field projection, lowering to
  `Expr.arrayElementDynamicWord` where needed.
- ERC-20 `balanceOf`, `allowance`, and `totalSupply` ECMs already exist under
  `Compiler/Modules/ERC20.lean` alongside the safe token write modules.

Package-boundary rule for the Unlink audit:

- Keep Permit2, Poseidon, Lazy-IMT, and Groth16 verifier assumptions in
  `unlink-verity` as external declarations or package-local ECMs with precise
  axiom names, proof-status tags, and a trust manifest.
- Keep Verity-core additions protocol-agnostic. A feature belongs in Verity core
  only if it models ordinary Solidity/EVM behavior or reusable audit ergonomics.

---

## Lessons from UnlinkPool (#185)

UnlinkPool, a ZK privacy pool, was the first non-trivial contract built with Verity (37 theorems, 0 `sorry`, 64 Foundry tests). It exposed gaps in the CompilationModel compilation path that prevented real-world contracts from using the verified pipeline (Layers 2+3).

### What was added

| Feature | Issue | CompilationModel | Core/Interpreter |
|---------|-------|-------------|-----------------|
| If/else branching | #179 | `Stmt.ite` | `execStmt` mutual recursion |
| ForEach loops | #179 | `Stmt.forEach` | `execStmtsFuel` + `expandForEach` desugaring |
| Array/bytes params | #180 | `ParamType.bytes32`, `.array`, `.fixedArray`, `.bytes` | `arrayParams` in `EvalContext` |
| Storage dynamic arrays | #1571 | `FieldType.dynamicArray`, `Expr.storageArrayLength` / `.storageArrayElement`, `Stmt.storageArrayPush` / `.storageArrayPop` / `.setStorageArrayElement` | compile-time/Yul lowering, source-side runtime semantics, and macro surface are in place; whole-contract proofs still pending |
| Internal function calls | #181 | `Stmt.internalCall`, `Expr.internalCall`, `FunctionSpec.isInternal` | Statement + expression evaluation |
| Multi-mapping types | #154 | `Expr.mapping2`, `Stmt.setMapping2`, `MappingType`, `FieldType.mappingTyped` | `storageMap2`/`storageMapUint` in `ContractState` |
| Events/logs | #153 | `EventDef`, `EventParam`, `Stmt.emit` | `Event` struct, `emitEvent`, LOG opcodes in codegen |
| Verified extern linking | #184 | `ExternalFunction` with axiom names | Axiom-tracked external calls |

### What this enables

A developer can now write a `CompilationModel` for contracts with conditional logic, loops over arrays, nested mappings (`address → address → uint256` for ERC20 allowances), event emission, internal helper functions, and linked external libraries, and compile through the verified pipeline (Layers 2+3). Previously only simple counter/token contracts were supported.

### Remaining gap

The EDSL path remains more expressive (supports arbitrary Lean, `List.foldl`, pattern matching). Contracts like UnlinkPool that use advanced Lean features still need the EDSL path. The CompilationModel path now covers the subset needed for standard DeFi contracts (ERC20, ERC721, governance, simple AMMs).

Internal helper call mechanics are available end-to-end, but first-class compositional proof reuse at the helper boundary is still incomplete. Today, internal helpers compile, validate, and execute through `execStmtsFuel`; the source-semantics layer now has explicit helper-summary soundness and direct-call consumption lemmas, but those summaries are not yet threaded through the body/IR preservation proofs across callers. That remaining proof-level gap is tracked in the Layer 2 completeness roadmap under [#1630](https://github.com/lfglabs-dev/verity/issues/1630), with the current interface/boundary refactor landing in [#1633](https://github.com/lfglabs-dev/verity/pull/1633).

### Interpreter feature-support contract

A comprehensive feature matrix documents which CompilationModel constructs each interpreter supports, their proof status, and known limitations:

- **Human-readable**: [`docs/INTERPRETER_FEATURE_MATRIX.md`](INTERPRETER_FEATURE_MATRIX.md)
- **Machine-readable**: `artifacts/interpreter_feature_matrix.json`
- **Smoke tests**: `Compiler/Proofs/InterpreterFeatureTest.lean` (22 `native_decide` proofs)

Key: the default path is `execStmtsFuel` (fuel-based), which supports the full construct set including loops and internal calls. The basic `execStmts` path is used only for proofs that do not need these features.

---

## Remaining Work Streams

### 🟡 **Layer 2 Completeness Track** (Issue #1630)
**What**: turn the current explicit supported fragment into a proof-complete target for the
macro-lowered EDSL image, using compositional proof interfaces instead of an ever-growing
exclusion list.
**Status**: generic theorem shape complete; completeness/generalization work active

Machine-readable boundary catalog:
- `artifacts/layer2_boundary_catalog.json` records the theorem target, the `SupportedSpec` split, and the current temporary helper gate.
- The compiled-side helper blocker is tracked separately in [#1638](https://github.com/lfglabs-dev/verity/issues/1638), because source-side helper summaries alone still cannot strengthen the generic theorem until the conservative-extension equalities for the helper-aware compiled semantics are proved and fed into the new helper-aware wrapper theorems now exposed from `Function.lean`, `Dispatch.lean`, and `Contract.lean`.

Execution priorities:
1. Define the theorem target precisely as the proof-complete macro-lowered `verity_contract` image, not arbitrary Lean-generated `CompilationModel` terms.
2. Split `SupportedSpec` into persistent global invariants plus feature-local proof interfaces.
   Current status: the top-level witness is split into invariants vs surface, and the body witness is now split into `core` / `state` / `calls` / `effects` interfaces in `Compiler/Proofs/IRGeneration/SupportedSpec.lean`. The `calls` interface is further split into `helpers` / `foreign` / `lowLevel`, and `calls.helpers` now carries an explicit per-callee helper-summary inventory with a reusable semantic postcondition contract (`InternalHelperSummaryContract`) plus a well-founded helper-rank interface (`helperRank` with strictly decreasing direct-callee ranks). The current fail-closed helper gate is no longer a separate witness field: it is derived from the body fragment itself through `SupportedStmtList.helperSurfaceClosed`. Expression-position helper callees are now tracked separately via `exprHelperCallNames` and must prove world preservation on success, which matches the current helper-aware expression semantics without forcing the same restriction onto statement-position helper summaries. `Compiler/Proofs/IRGeneration/SourceSemantics.lean` now turns that summary inventory into a proof-carrying source-side interface via `InternalHelperSummarySound` / `SupportedBodyHelperSummariesSound`, direct-call consumption lemmas for `Expr.internalCall`, `Stmt.internalCall`, and `Stmt.internalCallAssign`, the helper-free collapse goal `ExecStmtListWithHelpersConservativeExtensionGoal`, and a reusable global helper-summary proof catalog (`SupportedHelperSummaryProofCatalog`) that feeds `SupportedSpecHelperProofs`, so each internal helper summary can be proved once and reused across every caller. `SupportedSpec.lean` now also exposes the compiled-side glue `SupportedCompiledInternalHelperWitness` / `SupportedRuntimeHelperTableInterface`, and `Contract.lean` proves `compile_ok_yields_supportedRuntimeHelperTableInterface`, so future exact helper-step proofs can consume a reusable source-helper-to-runtime-helper-table mapping instead of quantifying over an arbitrary helper table. `SupportedSpec.lean` also separates the coarse current helper exclusion (`stmtTouchesUnsupportedHelperSurface`) from the narrower exact-seam predicate `stmtTouchesInternalHelperSurface`, and further splits that genuine-helper surface into direct statement-position heads, expression-position heads, and structural recursive heads. The direct statement-position side is now itself split by source-summary shape into void helper calls vs helper-return bindings, so future helper work can target the exact obligation shape rather than one monolithic helper bucket. `GenericInduction.lean` now also exposes the helper-aware induction interfaces `CompiledStmtStepWithHelpers` / `StmtListGenericWithHelpers`, the lifting lemmas `CompiledStmtStep.withHelpers_of_helperSurfaceClosed` / `stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed`, the induction-level body theorem `supported_function_body_correct_from_exact_state_generic_helper_steps`, the exact helper-aware compiled induction seam `CompiledStmtStepWithHelpersAndHelperIR` / `StmtListGenericWithHelpersAndHelperIR`, the strong compiled-side lifting witness/interface `StmtListCompiledLegacyCompatible`, the weaker future-proof exact-seam witness `StmtListHelperFreeCompiledLegacyCompatible`, the weaker source-side reuse witness `StmtListHelperFreeStepInterface`, the split exact helper-step interfaces `StmtListInternalHelperSurfaceStepInterface` / `StmtListResidualHelperSurfaceStepInterface`, the finer genuine-helper cut `StmtListDirectInternalHelperCallStepInterface` / `StmtListDirectInternalHelperAssignStepInterface` / `StmtListDirectInternalHelperStepInterface` / `StmtListExprInternalHelperStepInterface` / `StmtListStructuralInternalHelperStepInterface`, the assembly bridges `stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface`, `stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface`, and `stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface`, the exact-seam lifting lemmas `CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible` / `stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible`, the split bridges `stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible` / `stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible` together with the coarser compatibility wrappers over `StmtListDirectInternalHelperStepInterface`, the body-level split bridge `supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir`, the compatibility wrapper `supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir`, the induction-level exact body theorem `supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir`, the transitional legacy-compiled-body target `SupportedFunctionBodyWithHelpersIRPreservationGoal`, and the exact future helper-aware compiled-body target `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`; `Function.lean` exposes the matching function-level wrapper `supported_function_correct_with_helper_proofs_body_goal`. The older goal wrappers `supported_function_body_correct_from_exact_state_generic_with_helpers_goal` and `supported_function_correct_with_helper_proofs_goal` are now documented as abstract helper-free discharge paths into the transitional target rather than the eventual helper-rich theorem target, while the concrete current-fragment wrapper already routes through the helper-aware induction seam by lifting legacy helper-free step proofs. The feature-local `state` / `calls` / `effects` scans now recurse through nested `ite` / `forEach` bodies, so these interfaces describe whole bodies rather than only top-level statements.
3. Add compositional helper-call proof reuse across callers.
   Current unblocker: `Compiler/Proofs/IRGeneration/SourceSemantics.lean` now has a spec-aware helper execution target (`evalExprWithHelpers`, `execStmtListWithHelpers`, `interpretInternalFunctionFuel`), the public Layer 2 theorems already target that helper-aware semantics through the canonical `SupportedSpec.helperFuel` bound, and direct helper-call source lemmas now consume proof-carrying summary contracts. `Compiler/Proofs/IRGeneration/IRInterpreter.lean` now also defines the compiled-side target `execIRFunctionWithInternals` / `interpretIRWithInternals` that can resolve `IRContract.internalFunctions`, so the blocker has moved from “no compiled semantics target exists” to “the proof stack still targets the helper-free IR interpreter”.
   More precisely, `artifacts/layer2_boundary_catalog.json` now records that callers still derive generic body proofs through the helper-free `SupportedStmtList` witness, whose current helper exclusion is proved directly as `SupportedStmtList.helperSurfaceClosed`; `GenericInduction.lean` now exposes the missing source-side replacement seam as `CompiledStmtStepWithHelpers` / `StmtListGenericWithHelpers` plus `supported_function_body_correct_from_exact_state_generic_helper_steps`, and it now also proves the fail-closed lifting bridge from existing helper-free step/list proofs into that helper-aware source seam on helper-surface-closed statements via `CompiledStmtStep.withHelpers_of_helperSurfaceClosed` / `stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed`. It now also exposes the exact helper-aware compiled induction seam as `CompiledStmtStepWithHelpersAndHelperIR` / `StmtListGenericWithHelpersAndHelperIR` plus `supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir`, and it now splits both reuse boundaries: the compiled-side reuse boundary is weakened to `StmtListHelperFreeCompiledLegacyCompatible`, the source-side reuse boundary is weakened to `StmtListHelperFreeStepInterface`, and the helper-positive exact-step work is split first into genuine internal-helper execution versus residual coarse-surface non-helper heads, then further inside the genuine-helper side into direct helper calls, direct helper-return bindings, expression-position helper heads, and structural recursive heads. Those are combined by `stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible`, with coarser compatibility wrappers still available over `StmtListDirectInternalHelperStepInterface` and the existing `StmtListGenericCore`-based bridge retained as a derivation path through `stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible`; the corresponding body-level finer split bridge is `supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir`, with the older coarser direct-helper wrapper retained as `supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir`. On today's supported fragment the weaker compiled witness is derived directly from the supported-body surface via `stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface` / `SupportedBodyInterface.compiledHelperFreeLegacyCompatible`, the weaker source witness is derived from the existing helper-free library via `stmtListHelperFreeStepInterface_of_core`, and the current-fragment wrapper `supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir` therefore lands in the exact compiled target without a caller-supplied witness. It now also makes the compiled-side body seam explicit: `SupportedFunctionBodyWithHelpersIRPreservationGoal` is only the current legacy-compiled-body bridge, while the exact future helper-rich target is `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal` over `execIRStmtsWithInternals`, with a conservative-extension bridge from the legacy target on `LegacyCompatibleExternalStmtList` bodies when `IRContract.internalFunctions = []`. Summary-soundness evidence is not yet consumed through the exact helper-aware compiled induction seam into a direct proof of that exact helper-aware compiled-body target for the genuinely new internal-helper cases, but those cases are now cut along the same direct-helper-call / direct-helper-assign / expression-helper / structural-recursion lines as the existing source-side summary lemmas in `SourceSemantics.lean`. The older source-side goal `SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal` remains in the stack only as the abstract helper-free discharge path into the `_goal` helper wrappers. This is the helper-aware conservative extension of `interpretIR` on the helper-free runtime subset, and that helper-free conservative-extension goal is now closed: `IRInterpreter.lean` formalizes the intended legacy-compatible external-body Yul subset as `LegacyCompatibleExternalStmtList`, splits out the weaker contract-level witness `LegacyCompatibleExternalBodies`, packages the stronger helper-free runtime-contract shape as `LegacyCompatibleRuntimeContract`, encodes the exact retarget theorem as `InterpretIRWithInternalsZeroConservativeExtensionGoal`, and now proves its closed form as `interpretIRWithInternalsZeroConservativeExtensionGoal_closed`. The intermediate proof architecture remains explicit in code through `InterpretIRWithInternalsZeroConservativeExtensionInterfaces`, `InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal`, `interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal`, `InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`, and `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`; the dedicated expr-statement builtin classifier `exprStmtUsesDedicatedBuiltinSemantics` plus direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore` are now part of a finished helper-free conservative-extension proof rather than the remaining blocker. `Dispatch.runtimeContractOfFunctions` now also has a `runtimeContractOfFunctions_legacyCompatible` bridge, and `Contract.lean` exposes the helper-aware `_goal` / `_closed` wrappers `compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal` and `compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`. It now also proves that successful `CompilationModel.compile` on the current `SupportedSpec` fragment yields the full `LegacyCompatibleRuntimeContract` witness, exposing a directly consumable helper-aware whole-contract theorem `compile_preserves_semantics_with_helper_proofs_and_helper_ir_supported` with no extra caller-supplied compiled-side premise. The helper-aware compiled target remains available as total fuel-indexed helper-aware IR semantics. The remaining blocker on today's theorem domain is therefore helper-summary soundness plus decreasing helper-rank consumption in the genuinely new internal-helper cases of the exact helper-aware compiled induction seam and then in a direct proof of `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal` while widening or replacing the helper-excluding statement fragment and proving the exact helper step interface at those heads. A later widening step still needs a weaker retarget boundary that can tolerate helper tables once helper-rich features move inside the theorem domain; that later compiled-side blocker remains tracked in [#1638](https://github.com/lfglabs-dev/verity/issues/1638).
4. Add low-level call / returndata / proxy-upgradeability proof modeling.
5. Extend preserved observables to events/logs and typed errors.
6. Widen storage/layout-rich whole-contract coverage, then constructor / `fallback` / `receive`.

### 🟡 **Trust Reduction** (2 Remaining Components)
**What**: Eliminate or verify remaining trusted components
**Status**: 1/3 complete (function selectors resolved)
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | ~~Function Selectors~~ | keccak256 axiom + CI | — | ✅ **DONE** (PR #43, #46) |
| 2 | Yul/EVM Semantics Bridge | EVMYulLean integration | 1-3m | 🟡 **BRIDGE COMPLETE, NATIVE TARGET PENDING** |
| 3 | EVM Semantics | Strong testing + documented assumption | Ongoing | ⚪ TODO |

**Yul/EVM Semantics Bridge** (Issue [#1722](https://github.com/lfglabs-dev/verity/issues/1722)): EVMYulLean (NethermindEth) provides formally-defined Yul AST types and UInt256 operations. Current integration status:
- AST adapter: all 11 statement types + 5 expression types lower to EVMYulLean AST (0 gaps)
- Builtin bridge: 36 of 36 builtins bridged (25 pure + 11 context/env/storage/helper), with all 36 fully proven and 0 sorry'd
- 123 concrete bridge tests + 7 adapter correctness theorems + 36 context-lifted bridge theorems
- `bridgedBuiltins` definition enumerates all 36 builtins where `.evmYulLean` and `.verity` backends agree
- Unbridged: none; `mappingSlot` is bridged via the shared keccak-faithful `abstractMappingSlot` derivation
- Phase 2 state bridge scaffolding: type conversions, storage round-trip, env field bridges (0 sorry)
- **Phase 4 (safe-body EndToEnd retarget)**: `EvmYulLeanRetarget.lean` privately proves `backends_agree_on_bridged_builtins` and `evalYulExpr_evmYulLean_eq_on_bridged`, establishing isolated transition evidence that `.verity` and `.evmYulLean` agree for `BridgedExpr` expressions built from bridged builtin calls plus backend-independent `tload`/`mload`. It also privately defines `execYulFuelWithBackend`, privately proves `execYulFuelWithBackend_verity_eq`, the straight-line/block/if/switch/for statement-fragment helpers, `execYulFuelWithBackend_eq_on_bridged_target`, `emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies`, and the backend-wrapper codegen retarget facts. These remain isolated lower-level transition evidence rather than public proof authority, including the generated-runtime closure witnesses. `EvmYulLeanBodyClosure.lean` proves universal `compileStmtList_always_bridged` coverage for `BridgedSafeStmts`; the external-call family remains carved out behind explicit function-table simulation work. `EvmYulLeanSourceExprClosure.lean` proves scalar leaf closure (`compileExpr_bridgedSource_leaf`) and source-expression closure (`compileExpr_bridgedSource`) for arithmetic/comparison/bit-operation expressions, parameter length identifiers, storage, storage-array length, and ADT tag/field reads whose field lookup succeeds, singleton and nested mapping reads (`mapping`, `mappingWord`, `mappingUint`, `mapping2`, `mapping2Word`) through the abstract `mappingSlot` bridge, mapping struct-member reads (`structMember`, `structMember2`), the reserved exponentiation builtin surface, calldata/memory/transient reads, and syntactic `keccak256(offset, size)` emission in the `BridgedSourceExpr` fragment, with `compileExpr_keccak256_bridgedSource_of_exprCompileCore` exposing the compile-core argument case directly. `mappingSlot` remains an abstraction boundary for mapping-slot memory+keccak equivalence, while `keccak256` remains a source-semantics boundary for full end-to-end expression correctness until the source evaluator models memory-slice hashing. `EvmYulLeanBodyClosure.lean` also packages singleton `let`/`assign` bindings of syntactic `keccak256(offset, size)` into `BridgedSafeStmts` via `bridgedSafeStmts_letKeccak_of_exprCompileCore` and `bridgedSafeStmts_assignKeccak_of_exprCompileCore`, plus the external two-statement memory-preimage shape via `bridgedSafeStmts_externalMstoreLetKeccak_of_exprCompileCore`.
- **Native runtime follow-up (#1737)**: `EvmYulLeanNativeHarness.lean` provides the executable native path through `EvmYul.Yul.callDispatcher`; `EndToEnd.lean` keeps the public theorem seams on the native result surface (`nativeResultsMatchOn` / `sourceResultMatchesNativeOn`), the generated direct call-dispatcher `compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match` theorem, the helper-free call-dispatcher lowering wrapper `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping`, the mapping-helper call-dispatcher lowering wrapper `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping`, and the concrete SimpleStorage native theorem. The public call-dispatcher and SimpleStorage native theorems expose source/native obligations directly over projected `EvmYul.Yul.callDispatcher` results; the older generated dispatcher-exec/runtime adapter wrappers have been removed from `EndToEnd.lean`. The no-mapping and mapping call-dispatcher wrappers still accept concrete generated-dispatcher lowering results while exposing the direct projected `EvmYul.Yul.callDispatcher` result. `docs/NATIVE_EVMYULLEAN_TRANSITION.md` tracks the remaining state/result bridge lemmas and theorem work needed to retire the isolated lower-level retargeting evidence completely.
- **Remaining to make retargeting whole-program**: extend `BridgedSafeStmts` or add a separate function-table simulation for the external-call family (`internalCall`, `internalCallAssign`, `externalCallBind`, and `ecm`)

**EVM Semantics**: Mitigated by differential testing against actual EVM execution (Foundry). Likely remains a documented fundamental assumption.

### 🟡 **Parity-Pack Identity Track** (Issue #967)
**What**: Move from deterministic output-shape parity to exact pinned-`solc` Yul identity with proof-carrying rewrites.
**Status**: Groundwork + initial implementation (pack registry + CLI selection + validation guard).

Planned phases:
1. versioned parity packs keyed to pinned compiler tuples;
2. typed subtree rewrite model with mandatory semantic-preservation proof refs;
3. AST-level identity checker + CI gate + unsupported-manifest workflow.

Reference docs:
- `docs/SOLIDITY_PARITY_PROFILE.md`
- `docs/PARITY_PACKS.md`
- `docs/REWRITE_RULES.md`
- `docs/IDENTITY_CHECKER.md`
### ✅ **Ledger Sum Properties** (Complete)
**What**: Prove total supply equals sum of all balances
**Status**: All 7/7 proven with zero `sorry` (PR #47, #51, Issue #65 resolved)

| # | Property | Description |
|---|----------|-------------|
| 1 | ~~`deposit_sum_equation`~~ | ✅ Deposit increases total by amount |
| 2 | ~~`withdraw_sum_equation`~~ | ✅ Withdraw decreases total by amount |
| 3 | ~~`transfer_sum_preservation`~~ | ✅ Transfer preserves total |
| 4 | ~~`deposit_sum_singleton_sender`~~ | ✅ Singleton set deposit property |
| 5 | ~~`withdraw_sum_singleton_sender`~~ | ✅ Singleton set withdraw property |
| 6 | ~~`transfer_sum_preserved_unique`~~ | ✅ Transfer with unique addresses preserves sum |
| 7 | ~~`deposit_withdraw_sum_cancel`~~ | ✅ Deposit then withdraw cancels out |

---

## Ecosystem & Scalability (🔵 Medium Priority)

### 1. Realistic Example Contracts

**Goal**: Demonstrate scalability beyond toy examples.

**Completed Contracts**:
1. **ERC721** (NFT standard): implemented with 11 theorems, differential + property tests

**Proposed Contracts**:
1. **Governance** (voting/proposals)
   - Proposal lifecycle (created → active → executed)
   - Vote tallying
   - Timelock enforcement
   - **Effort**: 2-3 weeks

3. **AMM** (Automated Market Maker)
   - Constant product formula (x * y = k)
   - Swap calculations
   - Liquidity provision/removal
   - **Effort**: 3-4 weeks

**Total Estimated Effort**: 2-3 months for all three

**Impact**: Proves verification approach scales to production contracts

### 2. Developer Experience

**Improvements**:
- **IDE Integration**: VS Code extension with proof highlighting, tactics suggestions
- **Interactive Proof Development**: Lean InfoView integration
- **Better Error Messages**: Context-aware proof failure diagnostics
- **Documentation**: Comprehensive tutorials and proof patterns guide

**Estimated Effort**: 2-3 months

**Impact**: Lowers barrier to entry for new contributors

### 3. Performance Optimization

**Areas for Improvement**:
- Proof automation (faster tactics, better lemma libraries)
- CI optimization (caching, incremental builds)
- Property test generation (smarter fuzzing)

**Estimated Effort**: Ongoing

**Impact**: Faster iteration cycle, better developer experience

---

## Current Workstreams

The older Phase 1 / Phase 2 / Phase 3 calendar framing is no longer accurate. The project is now organized around active workstreams rather than dated milestone buckets.

### Completed Baseline

- Layer 1 is complete for the current contract set.
- Layer 3 is complete at the current generic proof surface.
- Layer 2 theorem shape is complete for the current supported fragment.
- Ledger sum properties, selector trust reduction, ERC721 baseline support, and large differential/property test suites are already in place.

### Active Work

1. **Layer 2 widening and completeness**
   - Thread helper-aware proof reuse, storage/event/call coverage, and richer observables into the generic whole-contract theorem.
   - Tracking: [#1630](https://github.com/lfglabs-dev/verity/issues/1630), [#1638](https://github.com/lfglabs-dev/verity/issues/1638)

2. **Trust reduction**
   - Continue the EVMYulLean bridge work and reduce remaining axiomatized / trusted boundaries.
   - Tracking: [#1683](https://github.com/lfglabs-dev/verity/issues/1683)

3. **Language and interop completeness**
   - Close the remaining `verity_contract` EDSL gaps needed for production DeFi contracts.
   - Tracking: [#1680](https://github.com/lfglabs-dev/verity/issues/1680), [#586](https://github.com/lfglabs-dev/verity/issues/586)

4. **Documentation and artifact synchronization**
   - Keep generated metrics, trust assumptions, parity profiles, and public docs aligned with the codebase.
   - Tracking: [#1681](https://github.com/lfglabs-dev/verity/issues/1681), [#585](https://github.com/lfglabs-dev/verity/issues/585)

### Longer-Term Expansion

- Add larger verified example contracts such as governance and AMM systems.
- Improve contributor UX with tutorials, proof-pattern guides, and better IDE/documentation integration.
- Expand optimization, parity-pack, and artifact-generation workflows once the current verification/documentation baselines stay stable.

---

## Contributing

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution guidelines and [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md) for current project state.

---

**Last Updated**: 2026-04-18
**Status**: Layer 1 is complete for the current contract set; Layer 2 now has a generic whole-contract theorem for the current supported fragment, with remaining [#1510](https://github.com/lfglabs-dev/verity/issues/1510) work focused on fragment widening and legacy bridge migration; Layer 3 is complete. Trust reduction 1/3 done. Sum properties complete (7/7 proven). CompilationModel now supports real-world contracts (loops, branching, events, multi-mappings, internal call mechanics, verified externs).
