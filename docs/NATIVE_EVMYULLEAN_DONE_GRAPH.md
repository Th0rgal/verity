# Native EVMYulLean Definition-Of-Done Graph

This graph ranks the remaining work for making native EVMYulLean the
authoritative Verity runtime target. The ordering combines dependency pressure
and urgency:

- **P0**: on the critical path to flipping the public theorem target.
- **P1**: required before the transition should be declared complete, but can
  proceed in parallel with the P0 proof path.
- **P2**: cleanup after the native path is authoritative.

The finish line is:

```text
source DSL
-> CompilationModel / generated Yul
-> EVMYulLean native Yul runtime
-> projected observable result
-> public end-to-end theorem
```

The custom Verity Yul interpreter may remain as a regression oracle, but it
must not carry the public theorem claim.

## Critical Path

```text
N0 generated-fragment contract
  -> N1 native state/environment bridge
  -> N2 native result projection
  -> N3 native dispatcher skeleton
  -> N4 body temp/write preservation
  -> N5 generated statement/expression native equivalence
  -> N6 whole runtime native/EVMYulLean agreement
  -> N7 fuel adequacy / theorem-facing fuel story
  -> N8 public Layer 3 theorem flip
  -> N10 CI/docs enforcement
```

Parallel P1 work:

```text
N9 issue-scope semantic closure
  -> N8 public Layer 3 theorem flip
```

Post-flip P2 work:

```text
N8 public Layer 3 theorem flip
  -> N11 interpreter demotion/removal plan
```

## Ranked Nodes

### N0: Generated-Fragment Contract

- **Urgency**: P0
- **Depends on**: none
- **Blocks**: N1, N3, N4, N5, N6
- **Status**: partially implicit in existing lowering/proof modules. Generated
  dispatcher selector lookup now has native-lowering specializations
  `lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function` and
  `lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function`, bridging
  `IRFunction` selector hits and misses to lowered native case lookup facts.
  The actual `buildSwitch` source case list is named by
  `buildSwitchSourceCases`, proved equal to `switchCases` by
  `buildSwitchSourceCases_eq_switchCases`, and consumed directly by
  `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function`
  and `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function`.
  The singleton dispatcher-only runtime lowering boundary now lives in the
  native harness as `lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative`.
  Helper-free emitted runtime lowering is packaged by
  `lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive`,
  with the compiled supported no-mapping wrapper
  `lowerRuntimeContractNative_of_compile_ok_supported_noMapping`. The generated
  mapping-helper lowering is named by `nativeMappingSlotFunctionDefinition` and
  `lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero`, pinning
  the concrete native EVMYulLean function body for `mappingSlot` at scratch
  base zero. Mapping-enabled emitted-runtime lowering is now packaged by
  `lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved`
  and the compiled supported wrapper
  `lowerRuntimeContractNative_of_compile_ok_supported_mapping_reserved`; the
  dispatcher is lowered under the full emitted-runtime reserved-name context so
  native switch temporary allocation remains faithful. Successful full native
  lowering is now peeled back to its concrete dispatcher lowering by
  `lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher`,
  `lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher`,
  `lowerRuntimeContractNative_emitYul_mapping_ok_dispatcher_reserved`, and
  `lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved`.
  EndToEnd also
  names the positive/projected no-mapping dispatcher-statement wrappers
  `nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping`
  and
  `nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping`,
  plus their `_ofIR_environment` and `_ofIR_globalDefaults` variants and the
  corresponding direct
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_*`
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_*`
  wrappers. The same native dispatcher-statement surface now exists for
  mapping-enabled generated runtimes under the `_mapping_reserved` names,
  including `nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_*`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_*`,
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_*`
  `_ofIR_environment` / `_ofIR_globalDefaults` variants. The
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_*`
  wrappers compose successful full runtime lowering with the concrete
  dispatcher-statement surfaces, keeping callers at the emitted-runtime
  boundary while the exact dispatcher lowering is extracted internally. The
  `layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_*`
  wrappers lift that same full-runtime boundary to Layer 3, and
  `layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_*`
  lifts it to the Layers 2+3 composition.
  Generic `.block` lowering shape also lives in the native harness via
  `lowerStmtsNative_single_block_ok_singleton` and
  `lowerStmtsNative_block_stmts_eq`; let/if/switch dispatcher statement peels
  are named by `lowerStmtsNativeWithSwitchIds_let_head_eq`,
  `lowerStmtsNativeWithSwitchIds_if_head_eq`, and
  `lowerStmtsNativeWithSwitchIds_singleton_switch_eq`; default-revert switch
  lowering is pinned by `lowerStmtsNativeWithSwitchIds_revert_zero_zero`,
  `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq`, and
  `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered`.
  The combined no-fallback/no-receive generated dispatcher lowering shape is
  exposed as `buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered`;
  its selector hit/miss lookup companions are
  `buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function`
  and `buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function`.
- **Definition of done**:
  - The compiler-emitted runtime Yul fragment is explicitly characterized.
  - Allowed statements, expressions, builtins, helper functions, dispatcher
    shape, storage layout, temp naming, and freshness guarantees are named.
  - Unsupported native/runtime features are either syntactically excluded or
    fail closed before theorem claims rely on them.
- **Verification**:
  - `python3 scripts/check_native_transition_doc.py`
  - Lean checks for `Compiler/Proofs/YulGeneration/Backends/EvmYulLeanAdapter.lean`
    and `EvmYulLeanNativeHarness.lean`.

### N1: Native State And Environment Bridge

- **Urgency**: P0
- **Depends on**: N0
- **Blocks**: N5, N6, N8
- **Status**: selector/calldata, sender/source/current address, callvalue,
  timestamp, number, storage seeding, and storage projection have bridge
  coverage. `chainid` and `blobbasefee` fail closed unless representable.
  Header-derived builtins without Verity transaction fields now also fail
  closed on selected native runtime paths.
  `validateNativeRuntimeEnvironment_ofIR_representableEnvironment` and
  `validateNativeRuntimeEnvironment_ofIR_globalDefaults` package the common
  `YulTransaction.ofIR` validation cases once unsupported selected-path header
  builtin use has been ruled out. EndToEnd mirrors the global-default case for
  the compiled native positive and projected-result seams.
  `generatedRuntimeNativeFragment_of_compile_ok_supported_safe` and
  `validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safe` close
  the executable generated-runtime fragment validator for supported compiled
  contracts.
- **Definition of done**:
  - Every environment field reachable from generated Yul is bridged, explicitly
    defaulted under a theorem invariant, or rejected fail-closed.
  - Static-call permissions, external call environment, returndata, gas, and
    block-header fields have explicit scope decisions.
  - State bridge lemmas cover the theorem-facing fields used by generated code.
- **Verification**:
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge`
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`
  - `lake env lean Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeSmokeTest.lean`

### N2: Native Result Projection

- **Urgency**: P0
- **Depends on**: N1
- **Blocks**: N6, N8
- **Status**: projection coverage exists for success, stop, return, revert,
  hard native errors, storage rollback, logs, and storage projection. The
  generic
  `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq`
  lemma packages generated selector-miss native `Revert` execution with the
  exact projected rollback result for arbitrary one-word selector tags. The
  generic
  `exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq` lemma
  packages selector-hit native halt/error execution with the selected body's
  projected result at the full lowered-switch boundary; its store-parametric
  companion
  `exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq`
  covers selector switches entered after earlier dispatcher-local bindings.
  The selector-miss companion
  `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq`
  gives the same exact rollback package for store-parametric miss/default
  paths. The block-level
  `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq`
  wrapper lifts that package through the generated dispatcher-local
  `__has_selector` binding shape, while
  `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq`
  packages selector-hit halt/error projection through the same block shape.
  Selector-hit normal-success projection is now packaged by
  `exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq`,
  `exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq`
  and its dispatcher-block companion
  `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq`.
  The final direct dispatcher-match surface also has the endpoint-agnostic
  `nativeDispatcherExecMatchesIRPositive_of_project_eq_match`, which lets a
  generated runtime proof discharge the positive native-vs-IR target from one
  projected native `YulResult` equality plus the observable IR match. The
  corresponding runtime lifts are named by
  `nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_project_eq_match` and
  `nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_project_eq_match`.
  EndToEnd now mirrors this as compiled-contract projected-result and
  environment-closure seams:
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_eq_match`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_environment`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_external_bodies_match`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_external_bodies_match`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_match`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment`,
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults`.
- **Definition of done**:
  - Projection lemmas cover every native halt/error/result used by generated
    runtime execution.
  - Revert/error rollback behavior is theorem-facing, not only tested.
  - Multiword/non-word-aligned return behavior is either fully modeled or
    restricted by generated-fragment invariants.
- **Verification**:
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`
  - `lake env lean Compiler/Proofs/YulGeneration/Backends/EvmYulLeanNativeSmokeTest.lean`

### N3: Native Dispatcher Skeleton

- **Urgency**: P0
- **Depends on**: N0, N1
- **Blocks**: N4, N6
- **Status**: selector temp initialization, matched flag initialization,
  guarded case/default execution, fuel-parametric case chains, lookup-driven
  hit/miss lemmas, and raw lowered switch block bridge lemmas are in progress.
- **Definition of done**:
  - The lowered dispatcher switch executes the same selected/default branch as
    the EVMYulLean fuel wrapper for every generated dispatcher shape.
  - The result is stated at the raw `lowerNativeSwitchBlock` boundary and at the
    higher generated dispatcher boundary.
- **Verification**:
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`
  - `python3 scripts/check_proof_length.py`
  - `lake env lean PrintAxioms.lean`

### N4: Body Temp/Write Preservation

- **Urgency**: P0, highest current bottleneck
- **Depends on**: N0, N3
- **Blocks**: N5, N6
- **Status**: `NativeBlockPreservesWord`, singleton/block-lift/if composition
  including condition evaluations that preserve the tracked word, list-level
  composition from per-statement preservation, selected freshness
  projection lemmas, assignment constructors for literal/hex/identifier/string
  RHS forms, generated `let` constructors for omitted, variable, and literal
  initializers, generated `let` primitive-call constructors when argument
  evaluation and the primitive preserve the tracked word, generated `let` and
  expression-statement user-call wrappers when argument evaluation and the call
  preserve the tracked word, read-only primitive preservation wrappers for
  generated comparison, arithmetic, signed arithmetic, bitwise, shift,
  switch-guard, calldata-size,
  calldata/memory reads, callvalue, address/caller, timestamp/number, and
  `sload` RHS forms, expression/argument-list preservation constructors for variables,
  literals, primitive and user calls, and argument-list cons/nil composition, concrete
  generated expression-statement constructors for `mstore` and `sstore` when
  argument evaluation preserves the tracked word, and empty-store plus store-parametric
  selector-hit freshness switch execution exist; general preservation from
  `nativeStmtsWriteNames` freshness is not complete for all generated statement
  families.
- **Definition of done**:
  - If a generated native body does not write a dispatcher temp, native
    execution preserves that temp.
  - The theorem composes for selected switch bodies and default bodies.
  - The matched flag remains stable after case body execution, so default
    execution is skipped exactly when it should be.
- **Verification**:
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`

### N5: Generated Statement/Expression Native Equivalence

- **Urgency**: P0
- **Depends on**: N0, N1, N2, N4
- **Blocks**: N6
- **Status**: selected expression and lowering equations exist, but full
  generated-fragment statement/block equivalence is incomplete.
- **Definition of done**:
  - Generated `let`, assignment, expression statements, blocks, conditionals,
    switches, loops if emitted, calls, storage operations, memory operations,
    events, return/stop/revert, and ABI snippets agree with the oracle.
  - Generated expression equivalence covers constants, locals, arithmetic,
    comparisons, calldata, memory, storage, keccak/slot computations, selector
    extraction, and supported builtins.
- **Verification**:
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanRetarget`
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapterCorrectness`
  - `lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness`

### N6: Whole Runtime Native/Interpreter Agreement

- **Urgency**: P0
- **Depends on**: N1, N2, N3, N4, N5
- **Blocks**: N7, N8
- **Status**: theorem seams exist; the whole-runtime agreement theorem is not
  complete.
- **Definition of done**:
  - For compiler-generated runtime Yul, native `callDispatcher` execution
    agrees with the current EVMYulLean-backed public semantic path on the
    observable result.
  - The theorem covers selected public function dispatch, default dispatch,
    storage, logs, return/revert/error behavior, and generated helper calls.
- **Verification**:
  - `lake build Compiler.Proofs.EndToEnd`
  - `lake env lean PrintAxioms.lean`

### N7: Fuel Story

- **Urgency**: P0
- **Depends on**: N6
- **Blocks**: N8
- **Status**: several fuel-parametric switch lemmas exist; public theorem fuel
  policy is unresolved.
- **Definition of done**:
  - The public theorem is either fuel-parametric, backed by a generated-code
    fuel lower bound, or uses a total wrapper with a proved sufficient default.
  - Fuel exhaustion cannot masquerade as semantic disagreement.
- **Verification**:
  - `lake build Compiler.Proofs.EndToEnd`

### N8: Public Theorem Flip

- **Urgency**: P0
- **Depends on**: N6, N7, N9
- **Blocks**: N10, N11
- **Status**: not done. The public path still uses
  `interpretYulRuntimeWithBackend .evmYulLean`.
- **Definition of done**:
  - Layer 3 theorem statements and generated proof plumbing target
    `interpretIRRuntimeNative` or an equivalent native `callDispatcher` wrapper.
  - The theorem no longer depends on the custom interpreter for the public
    semantic claim.
- **Verification**:
  - `rg "interpretYulRuntimeWithBackend \\.evmYulLean" Compiler/Proofs/EndToEnd.lean`
  - `lake build Compiler.Proofs.EndToEnd`

### N9: Issue-Scope Semantic Closure

- **Urgency**: P1
- **Depends on**: N0, N1, N5
- **Blocks**: N8 as a release-quality gate
- **Status**: partial progress exists for environment reads, mapping structs,
  packed members, overload identity, typed-IR ambiguity rejection, and direct
  internal calls.
- **Definition of done**:
  - Mapping-struct and packed-member behavior is covered by source, generated
    Yul, native execution, and proof-level preservation.
  - Signature/selector dispatch is fully selector-based where ABI dispatch is
    relevant.
  - External calls, returndata, and static-call behavior are either proved or
    explicitly out of the generated native fragment.
- **Verification**:
  - Existing property/differential tests for storage, overloads, external calls,
    and environment features.
  - `python3 scripts/check_native_transition_doc.py`

### N10: CI And Docs Enforcement

- **Urgency**: P0 after N8
- **Depends on**: N8
- **Blocks**: transition declaration
- **Status**: transition doc guards exist and now pin additional fail-closed
  environment boundary behavior.
- **Definition of done**:
  - CI fails if the public theorem target drifts back to the interpreter.
  - CI keeps transition docs, native smoke tests, axiom report, and generated
    fragment boundary in sync.
  - Axioms report is updated and reviewed after the theorem flip.
- **Verification**:
  - `python3 scripts/check_native_transition_doc.py`
  - `python3 scripts/check_proof_length.py`
  - `lake env lean PrintAxioms.lean`

### N11: Interpreter Demotion

- **Urgency**: P2
- **Depends on**: N8, N10
- **Blocks**: eventual cleanup only
- **Status**: not started.
- **Definition of done**:
  - The custom interpreter is documented and used as a regression/differential
    oracle, not as the authoritative public proof target.
  - Removal or shrinkage is deferred until native coverage is mature.
- **Verification**:
  - Documentation and CI checks name the native path as authoritative.
