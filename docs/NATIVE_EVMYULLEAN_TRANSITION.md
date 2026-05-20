# Native EVMYulLean Runtime Transition

This document tracks the remaining work for issue #1737: make native
EVMYulLean execution the public Layer 3 semantic target for Verity-generated
runtime Yul.

The detailed completion contract and reusable agent prompt live in
[`NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md`](NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md).

## Current State

The deeper generated-Yul preservation path still targets:

```lean
interpretYulRuntimeWithBackend .evmYulLean
```

That path executes Verity's custom fuel-based Yul statement interpreter and
routes bridged builtins through EVMYulLean-backed builtin evaluation. This is a
useful compatibility bridge, but it is not the final architecture requested by
#1722.

The native path now exists beside it:

```lean
Compiler.Proofs.YulGeneration.Backends.Native.interpretRuntimeNative
Compiler.Proofs.YulGeneration.Backends.Native.interpretIRRuntimeNative
```

Those entry points lower Verity runtime Yul into an EVMYulLean `YulContract`,
construct an EVMYulLean `SharedState .Yul`, run
`EvmYul.Yul.callDispatcher`, and project the observable result back to
Verity's `YulResult` shape. The native IR entry point requires callers to pass
the observable storage slot set explicitly, because the state bridge only
materializes pre-state storage for those slots.

## What This PR Establishes

- The native target has an IR-contract entry point:
  `interpretIRRuntimeNative`.
- Native result projection preserves pre-existing event history and appends
  native EVMYulLean logs, matching the observable shape expected by the current
  proof-side `YulResult`.
- The EndToEnd layer now exposes a small native result surface:
  `nativeResultsMatchOn`, `sourceResultMatchesNativeOn`, the source/native
  composition theorem over that result surface,
  `nativeGeneratedCallDispatcherResultOf`,
  `nativeGeneratedCallDispatcherMatchesIROn`, the supported-compiler
  generated direct `EvmYul.Yul.callDispatcher` theorem
  `compile_preserves_native_evmYulLean_callDispatcher_of_generated_callDispatcher_match`, the
  helper-free call-dispatcher lowering wrapper
  `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping`,
  the mapping-helper call-dispatcher lowering wrapper
  `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping`,
  and the concrete SimpleStorage native theorem. The dispatcher-exec
  compatibility predicate and wrappers are file-local helpers; public generated
  correctness exposes native `EvmYul.Yul.callDispatcher` premises and derives
  source/native agreement directly over the projected call-dispatcher result.
  The old generated runtime adapter wrappers have been removed rather than
  being retained as file-local `interpretIRRuntimeNative` compatibility
  theorems. On the
  helper-free and mapping-helper paths, the public wrapper theorems still accept
  the concrete generated-dispatcher lowering result while exposing the direct
  projected `EvmYul.Yul.callDispatcher` result. The concrete SimpleStorage
  native theorem now targets that direct projected call-dispatcher result too.
  The opaque arbitrary-fuel
  identity seams, generated dispatcher-exec lift facts, and fuel-indexed
  `nativeIRRuntimeMatchesIR` targets are file-local, and the older
  proof-interpreter bridge signature has been removed from EndToEnd. The public
  generated target is native `EvmYul.Yul.callDispatcher` through
  `nativeGeneratedCallDispatcherResultOf` and `nativeResultsMatchOn`, comparing
  success, return value, events, and the explicitly observable final-storage
  slots. The backend-parameterized safe-body Yul target is now isolated
  lower-level transition evidence; the generated native fragment still needs
  broader direct match proofs before that transition plumbing can be removed
  completely.
- The same module also keeps file-local transition seams for
  `nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_environment`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_globalDefaults`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_eq_match`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_environment`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults`,
  `layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_external_bodies_match`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_positive_body_closure`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_external_bodies_match`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherExec_project_body_closure`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_external_bodies_match`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_external_bodies_match`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_match`,
  with `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure`
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_environment`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_environment`,
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults`
  as the explicitly named safe-body wrapper aliases.
  The canonical native runtime and selected full-runtime wrapper surfaces set dispatcher fuel to
  `nativeRuntimeDispatcherFuel irContract` and runtime fuel to
  `nativeRuntimeFuel irContract`, avoiding an arbitrary public fuel parameter
  on the recommended direct-match surface. These direct match seams keep the
  remaining proof obligation at concrete native lowering, selected-path
  environment validation, and either raw positive dispatcher-exec matching or
  projected-result matching against IR execution. The compiled supported
  fragment check is now named explicitly by
  `generatedRuntimeNativeFragment_of_compile_ok_supported_safe` and
  `validateGeneratedRuntimeNativeFragment_of_compile_ok_supported_safe`, so the
  executable generated-runtime validator is closed from the same public
  `SupportedSpec`, static-parameter, and safe-body hypotheses as the native
  wrapper seams. Full generated-runtime native lowering success is named by
  `lowerRuntimeContractNative_of_compile_ok_supported_exists`, directly
  packaging `SupportedSpec + compile` into an executable
  `lowerRuntimeContractNative` witness. The helper-free native lowering boundary is also named by
  `lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive`
  in the native harness and by
  `lowerRuntimeContractNative_of_compile_ok_supported_noMapping` for compiled
  supported contracts, reducing no-mapping runtimes to the generated
  `initFreeMemoryPointer; buildSwitch` runtime shell. The public
  `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_noMapping`
  wrapper consumes that concrete init-prefixed dispatcher lowering directly, exposes the
  generated `EvmYul.Yul.callDispatcher` result surface, and keeps the same full
  emitted-runtime lowering equality internal. The mapping-helper side of
  the same boundary is now named by `nativeMappingSlotFunctionDefinition` and
  `lowerFunctionDefinitionNativeWithReserved_mappingSlotFuncAt_zero`, which
  package the concrete native lowering of the generated `mappingSlot` helper at
  scratch base zero. Mapping-enabled emitted runtime lowering is now packaged
  by
  `lowerRuntimeContractNative_emitYul_mapping_noInternals_noFallback_noReceive_reserved`
  in the native harness and by
  `lowerRuntimeContractNative_of_compile_ok_supported_mapping_reserved` for
  compiled supported contracts, with the generated
  `initFreeMemoryPointer; buildSwitch` dispatcher lowered under the full
  emitted-runtime reserved-name context. The public
  `compile_preserves_native_evmYulLean_of_lowered_generated_callDispatcher_mapping`
  wrapper consumes that reserved-context init-prefixed dispatcher lowering directly, keeps the
  reserved-context emitted-runtime lowering internal, and exposes the generated
  `EvmYul.Yul.callDispatcher` premise. Successful full native lowering
  can now also be peeled back to the concrete dispatcher lowering by
  `lowerRuntimeContractNative_emitYul_noMapping_ok_dispatcher`,
  `lowerRuntimeContractNative_of_compile_ok_supported_noMapping_ok_dispatcher`,
  `lowerRuntimeContractNative_emitYul_mapping_ok_dispatcher_reserved`, and
  `lowerRuntimeContractNative_of_compile_ok_supported_mapping_ok_dispatcher_reserved`.
  The no-mapping positive/projected native wrappers
  `nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_positive_body_closure_noMapping`
  and
  `nativeIRRuntimeMatchesIR_of_compiled_generated_dispatcherStmts_project_body_closure_noMapping`
  now consume the narrower dispatcher-statement lowering equality directly. The
  `_ofIR_environment` and `_ofIR_globalDefaults` variants discharge the native
  environment side condition for the same no-mapping dispatcher-statement shell,
  while the matching
  `layer3_contract_preserves_semantics_native_of_compiled_generated_dispatcherStmts_*`
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherStmts_*`
  wrappers expose the direct native-vs-IR result surface. The mapping-enabled equivalents are
  exposed under the
  `_mapping_reserved` suffix for the `nativeIRRuntimeMatchesIR`,
  `layer3_contract_preserves_semantics_native_of_compiled_generated_*`, and
  `layers2_3_ir_matches_native_evmYulLean_of_generated_*` dispatcher-statement
  wrapper families. The `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_runtime_dispatcherStmts_*`
  wrappers now compose successful full runtime lowering with those dispatcher
  statement surfaces, so
  callers can remain at the emitted-runtime lowering boundary while proving
  the exact extracted dispatcher match. The same
  full-runtime boundary is lifted to Layer 3 by the
  `layer3_contract_preserves_semantics_native_of_compiled_generated_lowered_runtime_dispatcherStmts_*`
  wrapper family, and to the Layers 2+3 composition by the
  `layers2_3_ir_matches_native_evmYulLean_of_generated_lowered_runtime_dispatcherStmts_*`
  wrapper family. The public Layers 2+3 full-runtime dispatcher-statement
  wrappers also expose `_ofIR_environment` and `_ofIR_globalDefaults` variants for both no-mapping
  and `_mapping_reserved` paths, matching the narrower dispatcher-statement
  environment-discharge surface while keeping callers at the full
  emitted-runtime lowering boundary.
- The native harness also names the dispatcher-block execution that
  `EvmYul.Yul.callDispatcher` performs after fuel checking and empty call-frame
  setup: `callDispatcherBlockResult`, with
  `callDispatcher_succ_eq_callDispatcherBlockResult` proving the reduction.
  It then rewrites initial-state execution to the lowered contract directly via
  `contractDispatcherBlockResult` and
  `callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult`.
  The wrapper is also peeled to raw native execution through
  `contractDispatcherExecResult` and
  `contractDispatcherBlockResult_eq_execResult`. The next proof no longer has
  to open dispatcher or projection wrappers before attacking `EvmYul.Yul.exec`
  preservation for the lowered contract dispatcher body.
- Native runtime top-level partitioning is now transparent enough for proofs:
  `lowerRuntimeContractNativeAux` is structurally recursive, and the named
  equations `lowerRuntimeContractNativeAux_funcDef_cons`,
  `lowerRuntimeContractNativeAux_stmt_cons`, and
  `lowerRuntimeContractNative_empty` expose the helper-definition/function-map
  split that future dispatcher-agreement proofs need.
- The selected generated-dispatch path has small named hooks:
  `selectorExprMatchesGeneratedDispatcher_selectorExpr`,
  `selectedSwitchBody_hit`, and `selectedSwitchBody_miss`.
- The native harness remains separate from the existing retargeting theorem, so
  the proof tree does not claim a theorem that is not yet proved.
- The current private transition-only
  `yulCodegen_preserves_semantics_evmYulLeanBackend` theorem still composes
  through
  `yulCodegen_preserves_semantics_via_reference_oracle` before rewriting the
  emitted runtime to the private EVMYulLean backend executor wrapper
  `interpretYulRuntimeWithBackend`. The explicit
  `yulCodegen_preserves_semantics_evmYulLeanBackend` theorem gives isolated
  transition evidence for an EVMYulLean-backed Yul target, but it is not yet a
  native source-of-truth
  Layer 3 proof. The older
  `yulCodegen_preserves_semantics_evmYulLeanBackend_via_reference_oracle` name
  remains only as a private compatibility alias; public EndToEnd wrappers no
  longer consume either legacy retarget name.
- The older generic native reference-oracle/fuel-wrapper aliases have been
  removed. The remaining file-local native Layer 3 transition seams consume
  `nativeIRRuntimeMatchesIR` directly, while the public supported EndToEnd
  theorems expose direct `EvmYul.Yul.callDispatcher` results. The generated
  native fragment's direct match proof remains the visible blocker for deleting
  the private runtime transition layer.
- `nativeDispatcherExecMatchesIRPositive_of_project_eq_match` now gives the
  remaining generated-dispatch proof a single projected-result introduction
  form, so endpoint-specific native success/halt/error splits are only needed
  when a proof needs endpoint-specific facts.
- `nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_project_eq_match` and
  `nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_project_eq_match`
  lift that projected-result package through the native runtime harness.
- The EndToEnd module mirrors that projected-result surface for compiled
  supported contracts through
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_eq_match`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_environment`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults`,
  and the `layer3_...project...` / `layers2_3_...project...` wrappers, so
  callers can provide one projected native result equality plus the observable
  match without first building the positive-dispatcher predicate.
  The `_ofIR_environment` variants discharge raw native environment validation
  from representable `tx.chainId`/`tx.blobBaseFee` facts plus the
  selected-path unsupported-header check. The `_ofIR_globalDefaults` variants
  package the current EVMYulLean global-default transaction case behind the
  same selected-path unsupported-header check.

## Clean Target Architecture

The desired end state is:

```text
CompilationModel
  -> IRContract
  -> emitted runtime Yul
  -> EVMYulLean YulContract
  -> EvmYul.Yul.callDispatcher
  -> projected observable result
```

The Verity custom Yul interpreter should then be used only as a regression
oracle, not as the semantic target in the public theorem stack.

## Remaining Work

The following verified user reports should stay explicit in the transition
scope so the native path does not look more complete than it is:

- The public supported generated `callDispatcher` theorem is now composed down
  to native `EvmYul.Yul.callDispatcher`, with selector miss and generated
  selector-hit guard failures discharged internally. The closed generic case
  wrappers are
  `nativeGeneratedCallDispatcherResult_selector_miss_matchesIR_exists_of_compile_ok_supported`,
  `nativeGeneratedCallDispatcherResult_selector_hit_nonpayable_nonzero_revert_matchesIR_exists_of_compile_ok_supported`,
  and
  `nativeGeneratedCallDispatcherResult_selector_hit_args_short_revert_matchesIR_exists_of_compile_ok_supported`.
  The artifact/error continuation path remains named by
  `nativeGeneratedCallDispatcherResult_selector_hit_error_matchesIR_exists_of_compile_ok_supported`.
  Its remaining success-path blocker is the selected user-body result boundary:
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel`. The normal-return side
  still needs a generic native execution proof for
  `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived`, connecting the
  lowered selected `fn.body` at dispatcher fuel to `execIRFunction`; the
  halt-channel side is currently supplied by
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel`. The source-level
  public composition theorem
  `compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
  now rewrites the generated dispatcher result to the canonical
  `interpretIRRuntimeNative` target, packages that result with the source-to-IR
  compiler theorem, and discharges the lowered native runtime witness
  internally. The public IR/native theorem keeps the direct projected result
  target. The public theorem no longer exposes full `DispatchGuardsSafe`;
  `SupportedSpec` carries the selected function calldata-threshold inventory, and
  `generatedFunctionCalldataThreshold_of_compile_ok_supported` transports that
  inventory across `compile` to the generated IR function selected by the
  dispatcher. Legacy premise-taking `compile_preserves_native_evmYulLean_*`
  wrappers are file-local; the public `compile_preserves_native_evmYulLean_*`
  surface is limited to the direct `nativeGeneratedCallDispatcherResultOf`
  composition theorem and the generated `SupportedSpec + compile` composition
  theorem. The private success bridge rebuilds `DispatchGuardsSafe` after
  the generated value and argument guards have selected the success branch.
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_bridgedStraightStmts_mapping`
  packages the mapping-helper straight-body preservation path through
  `NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_bridgedStraightStmts`.
  The no-mapping helper-free straight-body preservation bridge is now split
  out as `NativeMappingFreeBridgedExpr`,
  `NativeExprPreservesWord_lowerExprNative_of_mappingFreeBridgedExpr`,
  `NativeMappingFreePreservableStraightStmt`,
  `NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_mappingFreePreservableStraightStmts`,
  and
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_mappingFreePreservableStraightStmts`.
  Historical `BridgedStraightStmts` no-mapping bodies can now enter that same
  actual-runtime path through `NativeMappingFreeSideConditionForBridgedStraightStmt`,
  `NativeMappingFreePreservableStraightStmts.of_bridgedStraightStmts`, and
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_exec_only_and_bridgedStraightStmts_mappingFree`.
  The dispatcher-level adapter
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_exec_only_and_bridgedStraightStmts_mappingFree`
  composes that result bridge with the supported `compile` theorem stack.
  The compile-to-body handoff is tracked by
  `generatedRuntimeSelectedFunctionBodyBridged_of_compile_ok_supported`,
  `lowerStmtsNativeWithSwitchIds_selectedFunctionBody_exists_of_compile_ok_supported`,
  `selectedFunctionBodyBridgedAndLowered_of_compile_ok_supported`, and
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.selected_body_closure_of_compile_ok_supported`,
  which packages the selected `BridgedStmts` witness, selected native-body
  lowering success, and generated calldata-threshold fact from `SupportedSpec +
  compile` without claiming native execution semantics. The dispatcher
  artifact handoff remains tracked by
  `nativeGeneratedSelectorHitSuccessUserBodyLoweredArtifacts_exists_of_compile_ok_supported`,
  and
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.selected_body_artifacts_of_compile_ok_supported`
  combines those lowered artifacts with the selected-body closure facts for the
  actual dispatcher-selected `fn.body`. When generated switch-case freshness is
  available,
  `selectedUserBodyClosureAndMatchedFresh_of_compile_ok_supported_switchFresh`
  also strips the generated guard prefix and recovers matched-flag freshness
  for the actual lowered user body. That freshness handoff still has to be
  consumed before the selected-body preservation callback loses the current
  `hLowerCases` fact: the later result-bridge callback only sees the selected
  `hBodyLower`/`hUserBodyLower` pair, while switch-case freshness is stated over
  the full lowered `cases'` list. The next adapter should therefore stay at the
  dispatcher artifact boundary, or widen the preservation callback to carry
  `hLowerCases`, instead of trying to reconstruct whole-case freshness from a
  selected body lowering alone. The mapping-helper side now has that
  dispatcher-boundary handoff under
  `nativeGeneratedSelectorHitBodyPreservesMatched_mapping_of_switchFresh` and
  `NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_bridgedStraightStmts_mapping_switchFresh`,
  with
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_exec_only_and_bridgedStraightStmts_mapping_switchFresh`
  carrying it back to the generated dispatcher theorem,
  mirroring the earlier mapping-free `switchFresh` adapter while keeping
  mapping-specific straight-body side conditions private.
  The dispatcher wrappers can now consume the smaller per-case lowering
  freshness premise through
  `nativeGeneratedSwitchTempsFreshForNativeBodies_of_case_body_fresh`,
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_exec_only_and_bridgedStraightStmts_mappingFree_caseFresh`,
  and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_with_selected_user_body_exec_only_and_bridgedStraightStmts_mapping_caseFresh`;
  the remaining freshness work is to derive that per-case premise from the
  generated straight-body shape and reserved-name set.
  A fully closed
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_compile_ok_supported`
  lemma is still missing. The proof cannot be completed from the current
  handoff facts alone: the dispatcher-facing adapters also need the generic
  selected-body execution predicate
  `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived`, straight-body
  preservation inputs (`BridgedStraightStmts` plus the mapping/no-mapping side
  conditions), and a lowered-body freshness proof showing the generated matched
  flag is absent from `nativeStmtsWriteNames bodyNative`. The compile-supported
  handoff currently gives `BridgedStmts fn.body` and successful native
  lowering, but not those stronger execution, straight-fragment, side-condition,
  or matched-temp freshness facts.
  The normal-return execution side now has a sound singleton-`leave` base case:
  `execIRStmts_single_leave_succ_succ`,
  `exec_block_leave_ok_add_ten`, and
  `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_leave_body`.
  This does not close the dispatcher result boundary because native `leave`
  exits through a revivable checkpoint, so the existing matched-flag
  preservation predicate is not the right continuation fact for that shape.
  The halt-channel side now also has a singleton-`stop` base case:
  `execIRFunction_single_stop`, `exec_block_stop_halt_add_ten`, and
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_stop_body`; it
  composes through
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_stop_body` and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_stop_body`.
  The halt-channel scalar-return side now also covers literal external
  returns via `execIRFunction_mstore0_lit_return32`,
  `exec_lowerExprNative_mstore_lit_lit_ok_fuel`,
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_lit_return32`,
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_lit_return32`,
  and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_lit_return32`.
  Single-argument external returns are covered by
  `execIRFunction_mstore0_calldataload4_return32_of_args_cons`,
  `exec_lowerExprNative_mstore_lit_calldataload_lit_ok_fuel`,
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_mstore0_calldataload4_return32`,
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_mstore0_calldataload4_return32`,
  and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_calldataload4_return32`.
  The reusable aligned-calldata return seams are
  `execIRFunction_mstore0_calldataload_aligned_return32`,
  `initialState_calldataload_aligned_arg_word`,
  `exec_lowerExprNative_mstore_lit_calldataload_lit_ok_fuel`, and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_mstore0_calldataload_aligned_return32`
  under the explicit `ByteArray.readBytes` offset condition
  `4 + 32 * idx < 2^64`.
  The remaining normal-return blocker is the generic body-shape discovery path:
  generated selected bodies still need to identify arbitrary scalar return
  bodies and supply the mapping-free straight-body predicate automatically. A
  direct source-shape handoff cannot simply reuse the raw two-statement exact
  return lemmas, because `compileFunctionSpec` prepends `genParamLoads`; even
  zero-parameter functions carry the generated calldata-size guard in
  `fn.body`. The zero-parameter literal-return instance is now closed through
  the guarded generated shape with
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_lit_return32`,
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_lit_return32`,
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_lit_return32`,
  and the source-shape wrapper
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_lit_return32`.
  The matching zero-parameter storage-return shape is closed with
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_zeroParam_mstore0_sload0_return32`,
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_zeroParam_mstore0_sload0_return32`,
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_zeroParam_mstore0_sload0_return32`,
  and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_zeroParam_sload0_return32`.
  The generated one-argument setter shape now also closes through the generated
  parameter-load guard and `value` binding:
  `execIRFunction_oneParam_store0_value_stop`,
  `NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel.of_oneParam_store0_value_stop`,
  `NativeGeneratedSelectedUserBodyResultBridgeAtFuel.of_oneParam_store0_value_stop`,
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_oneParam_store0_value_stop`,
  and
  `nativeGeneratedCallDispatcherMatchesIR_of_compile_ok_supported_source_oneParam_store0_value_stop`,
  with the source/native preservation wrapper
  `compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher_source_oneParam_store0_value_stop`.
- [#1741](https://github.com/lfglabs-dev/verity/issues/1741):
  `blockTimestamp` is bridged through native EVMYulLean execution, and native
  smoke coverage now checks `timestamp()`/`number()` state reads. Native
  `chainid()` and `blobbasefee()` now fail closed on the selected native runtime
  path unless the corresponding `YulTransaction` field is representable by
  EVMYulLean's current environment model. Today that means
  `YulTransaction.chainId` must match the EVMYulLean global `EvmYul.chainId`, and
  `YulTransaction.blobBaseFee` must match the minimum blob gas price
  `EvmYul.MIN_BASE_FEE_PER_BLOB_GAS`. Header-derived native builtins that do
  not yet have Verity `YulTransaction` fields, such as `coinbase`, `difficulty`,
  `prevrandao`, `gaslimit`, `basefee`, and `gasprice`, also fail closed on the
  selected native runtime path instead of reading EVMYulLean's zeroed header
  defaults. The account-balance builtin `selfbalance` also fails closed on the
  selected native runtime path until the bridge carries Verity's `selfBalance`
  into the EVMYulLean account map. The native harness names the remaining
  unbridged boundary with
  `initialState_unbridgedEnvironmentDefaults`, pinning base-fee/blob fields and
  native `chainid` to their current EVMYulLean default/global behavior until
  the follow-up widens the state bridge. The helper theorems
  `validateNativeRuntimeEnvironment_ofIR_representableEnvironment` and
  `validateNativeRuntimeEnvironment_ofIR_globalDefaults` now package the common
  `YulTransaction.ofIR` validation cases once selected-path unsupported header
  builtin use has been ruled out. EndToEnd mirrors the global-default case with
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure_ofIR_globalDefaults`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_project_body_closure_ofIR_globalDefaults`,
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_body_closure_ofIR_globalDefaults`,
  and `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_project_body_closure_ofIR_globalDefaults`.
  The
  `verity_contract` surface now accepts monadic environment reads such as
  `let t <- blockTimestamp`, `let t <- Verity.blockTimestamp`, `blockNumber`,
  `chainid`, `blobbasefee`, `contractAddress`, `msgSender`, and `msgValue`, and the
  executable `.run` helpers read those values from `ContractState` instead of
  placeholder constants.
- [#1738](https://github.com/lfglabs-dev/verity/issues/1738): mapping-struct
  storage now has contract-local executable `.run` helpers for struct member
  reads/writes that use the same abstract Solidity mapping-slot formula as the
  compiler/native storage projection, including packed member masking. Before
  native execution becomes authoritative, this still needs proof-level source
  semantics and preservation coverage for the packed struct-member cases.
- [#1742](https://github.com/lfglabs-dev/verity/issues/1742): overloaded
  source functions now use a signature-based identity model for generated
  declarations, duplicate validation, and direct internal-call lowering while
  preserving the Solidity-facing source name for selectors/ABI dispatch.
  Same-name/same-arity declarations are accepted when their parameter types
  differ. The macro-generated compilation model still gives internal helpers
  unique Yul-level names, and the lower-level `CompilationModel` rejects
  duplicate same-name internal functions because native/Yul function
  definitions are keyed by name. Native EVM dispatch is selector-based; the
  remaining transition work is theorem coverage around the widened frontend
  surface and any future executable `.run` overload-dispatch extensions.
- [#1740](https://github.com/lfglabs-dev/verity/issues/1740): the
  `verity_contract` source surface intentionally models internal delegation with
  ordinary direct function-name calls, not user-written `internalCall`/
  `internalCallAssign`. Statement-position calls lower to
  `Stmt.internalCall`, single-result binds lower to `Expr.internalCall`, and
  tuple-result binds lower to `Stmt.internalCallAssign`; the lower-level
  constructors remain compilation-model IR, not the recommended executable
  contract-body syntax.
- [#1744](https://github.com/lfglabs-dev/verity/issues/1744): near-literal
  manual packed-slot writes now have a first-class `verity_contract` surface:
  construct the packed word with ordinary word operations such as `bitOr` and
  `shl`, then write it with `setPackedStorage root offset word`. This lowers to
  a full-word `sstore(root.slot + offset, word)` via
  `Stmt.setStorageWord`, keeping explicit slot boundaries visible without an
  unsafe raw-Yul block.
- [#1745](https://github.com/lfglabs-dev/verity/issues/1745): dynamic array
  parameters with static tuple elements are now accepted on the tuple
  destructuring/tuple-return `arrayElement` path. Tuple destructuring such as
  `let (xtReserve, liqSquare, offset) := arrayElement cuts idx` lowers to
  checked word reads with the element ABI stride. Plain scalar `arrayElement`
  remains limited to single-word static element arrays until the general
  multi-word element read path lowers through `Expr.arrayElementWord` instead
  of the 32-byte-stride helper. Dynamic element types such as `Array String`
  and `Array Bytes` remain rejected.

1. Prove lowering invariants for the native contract shape.

   Required facts:
   - top-level `funcDef` nodes are partitioned into `YulContract.functions`
     (now exposed by `lowerRuntimeContractNativeAux_funcDef_cons`),
   - dispatcher code contains no function definitions,
   - known runtime builtins lower to native `.inl` primops, now named by
     `lowerExprNative_call_runtimePrimOp`,
   - user/helper calls remain `.inr` function calls, now named by
     `lowerExprNative_call_userFunction`,
   - duplicate helper definitions fail closed.

   Progress: `generatedRuntimeNativeFragment` is the executable native runtime
   shape boundary, and `interpretRuntimeNative`/`interpretIRRuntimeNative` now
   fail closed before lowering when emitted runtime code violates that boundary.
   It currently pins unique top-level helper names, no nested dispatcher
   `funcDef`s, and no nested helper-body `funcDef`s.

   `EvmYul.Yul.callDispatcher` now unfolds through
   `callDispatcher_succ_eq_callDispatcherBlockResult` to the named
   `callDispatcherBlockResult`, then rewrites initial-state execution to
   `contractDispatcherBlockResult`, then peels the block wrapper to
   `contractDispatcherExecResult`. EndToEnd now exposes the direct
   `nativeDispatcherExecMatchesIRPositive` target plus generated-shape lifts to
   `nativeIRRuntimeMatchesIR`, so positive-fuel callers prove raw dispatcher
   execution against IR directly instead of passing through intermediate
   fuel-wrapper agreement predicates.

   Statement-level native lowering through
   `lowerStmtsNativeWithSwitchIds`/`lowerStmtGroupNativeWithSwitchIds` is now
   structurally recursive, and named equations expose list cons, switch-case
   cons, straight-line statement forms, blocks, loops, and the lazy native
   switch block constructor `lowerNativeSwitchBlock`. The theorem
   `lowerNativeSwitchBlock_eq` records the actual guarded-block shape that
   native dispatcher proofs must consume: the discriminator is evaluated once,
   each case is guarded by `iszero(matched) && discr == tag`, and the default
   runs only when no case has marked the switch matched. The top-level partition
   equation and statement-level lowering equations are proved, but full
   dispatcher-block agreement still requires per-statement native execution
   preservation lemmas against IR. EndToEnd provides raw-exec intro forms for
   the direct native-vs-IR concrete outcomes:
   `nativeDispatcherExecMatchesIRPositive_of_exec_ok_match`,
   `nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match`,
   `nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match`,
   and `nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match`.
   These let each generated-statement simulation case finish from a proved
   `contractDispatcherExecResult` equation plus the corresponding observable
   projection match.

   The generated dispatcher selector expression is also pinned for the
   EVMYulLean-backed EVMYulLean fuel wrapper:
   the private `bridgedExpr_selectorExpr` lemma shows that `selectorExpr` is in
   the bridged expression fragment, and the private
   `evalYulExprWithBackend_evmYulLean_selectorExpr_semantics` lemma proves that
   it evaluates to `state.selector % selectorModulus`. This discharges the
   isolated interpreter-oracle side of the first selector branch condition. The native
   side now exposes `lowerExprNative_selectorExpr`,
   `step_calldataload_ok`, `step_shr_ok`,
   `primCall_calldataload_ok`, `primCall_shr_ok`, and
   `eval_lowerExprNative_selectorExpr_ok`, so native evaluation of the lowered
   selector expression reduces to EVMYulLean `calldataload(0)` followed by
   `shr(224, ...)`. The byte bridge also names
   `readBytes_zero_get?_of_lt_source` plus
   `initialState_calldataReadWord_selectorByte0` through
   `initialState_calldataReadWord_selectorByte3`, proving that the native
   word read sees the bridged selector bytes before any opaque zero-padding.
   The arithmetic recomposition side is named by `selectorBytesAsNat`,
   `initialState_calldataReadWord_selectorPrefix` exposes the corresponding
   little-endian `fromBytes'` prefix, `uint256_shiftRight_224_ofNat_toNat`
   exposes the native `UInt256.shiftRight` arithmetic at selector shift, and
   `readBytes_zero_32_size` proves the EVMYulLean `readBytes` length fact now
   that `ffi.ByteArray.zeroes` has a kernel-visible Lean body in the pinned
   EVMYulLean revision. The named
   `initialState_selectorExpr_native_value` and
   `eval_lowerExprNative_selectorExpr_initialState_ok` theorems therefore prove
   that native evaluation of the lowered selector expression over the bridged
   initial state returns `tx.functionSelector % selectorModulus`.
   `exec_let_lowerExprNative_selectorExpr_initialState_ok`, `exec_let_lit_ok`,
   and `exec_nativeSwitchPrefix_selector_initialState_ok` then package the
   first two statements emitted by the generated native switch block:
   discriminator-temp initialization from the normalized selector followed by
   matched-flag initialization to zero. The named
   `step_eq_ok`, `step_iszero_ok`, `step_and_ok`, `primCall_eq_ok`,
   `primCall_iszero_ok`, `primCall_and_ok`, `exec_block_cons_ok`,
   `exec_if_eval_zero`, `exec_if_eval_nonzero`, and
   `eval_nativeSwitchGuardedMatch_ok` theorems expose the next native
   guarded-switch reduction layer for the lazy switch block emitted by
   `lowerNativeSwitchBlock`; `eval_nativeSwitchGuardedMatch_hit_ok`,
   `exec_if_nativeSwitchGuardedMatch_hit`, `exec_lowerAssignNative_lit_ok`,
   and `exec_if_nativeSwitchGuardedMatch_hit_marked` package the selected-case
   guard hit, matched-flag assignment, and native `if` execution step, while
   `eval_nativeSwitchGuardedMatch_miss_ok` and
   `exec_if_nativeSwitchGuardedMatch_miss` package the non-selected-case skip
   while no previous case has matched, and
   `eval_nativeSwitchGuardedMatch_matched_ok` and
   `exec_if_nativeSwitchGuardedMatch_matched` package the later-case skip
   once the matched flag is set. `eval_nativeSwitchDefaultGuard_ok`,
   `eval_nativeSwitchDefaultGuard_unmatched_ok`,
   `eval_nativeSwitchDefaultGuard_matched_ok`,
   `exec_if_nativeSwitchDefaultGuard_unmatched`, and
   `exec_if_nativeSwitchDefaultGuard_matched` package the generated default
   guard for both no-case-matched and case-already-matched paths. The matching
   `_fuel` variants remove the fixed-fuel limitation that blocked recursive
   whole-case-chain execution over the generated block tail. The native harness
   now also exposes `exec_nativeSwitchCaseIfs_all_miss_fuel`,
   `exec_nativeSwitchCaseIfs_matched_fuel`, and
   `exec_nativeSwitchCaseIfs_prefix_hit_fuel`, packaging whole guarded
   case-chain execution for default misses, suffix skips after a match, and the
   selected-case prefix-hit shape. `exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel`
   and `exec_nativeSwitchDefaultIf_matched_fuel` then package the optional
   default statement emitted by the lazy lowering. The selector lookup bridge
   now exposes `nativeSwitch_find_hit_split`,
   `nativeSwitch_find_none_all_miss`,
   `exec_nativeSwitchCaseIfs_find_hit_fuel`, and
   `exec_nativeSwitchCaseIfs_find_none_fuel`, so generated dispatcher proofs can
   consume a concrete `find?` hit or miss instead of manually supplying the
  prefix/selected/suffix split. The hit side now has the preservation adapter
  `NativeBlockPreservesWord` plus
  `exec_nativeSwitchCaseIfs_find_hit_preserved_fuel`, which turns selected-body
  preservation of the matched flag into the whole generated case-chain
  postcondition. The native harness also exposes `exec_block_append_ok`,
  `exec_nativeSwitchCaseIfs_with_default_matched_fuel`,
  `exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel`,
  `exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel`, and
  `exec_nativeSwitchCaseIfs_find_none_without_default_fuel`, composing selector
  lookup with the optional default arm emitted by `lowerNativeSwitchBlock`. The
  adapter now also exposes
  `lowerSwitchCasesNativeWithSwitchIds_find?_some` and
  `lowerSwitchCasesNativeWithSwitchIds_find?_none`, proving that native case
  lowering preserves the source switch selector lookup result while exposing
  the switch-temp counter interval for the selected lowered body. The native
  harness lifts those generic lookup facts to generated dispatcher function
  lookup with `lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function`
  and `lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function`, so an
  `IRFunction` selector hit or miss now produces the corresponding lowered
  native case lookup fact directly. It also exposes `buildSwitchSourceCases`
  and `buildSwitchSourceCases_eq_switchCases`, plus the actual-`buildSwitch`
  wrappers `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function`
  and `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function`,
  so generated dispatcher proofs can consume the source case list emitted by
  `Compiler.CodegenCommon.buildSwitch` without first rewriting manually to
  `switchCases`. The native harness also owns
  `lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative`, the generic
  singleton non-`funcDef` runtime lowering boundary for dispatcher-only runtime
  code. Helper-free emitted runtime lowering is packaged by
  `lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive`.
  It also owns the generic
  block-lowering shape lemmas `lowerStmtsNative_single_block_ok_singleton` and
  `lowerStmtsNative_block_stmts_eq`, plus the generated-dispatcher peel facts
  `lowerStmtsNativeWithSwitchIds_let_head_eq`,
  `lowerStmtsNativeWithSwitchIds_if_head_eq`, and
  `lowerStmtsNativeWithSwitchIds_singleton_switch_eq`. That leaves the
  concrete default-revert switch lowering facts
  `lowerStmtsNativeWithSwitchIds_revert_zero_zero`,
  `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq`, and
  `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered`
  in the native harness as well. The harness now also packages those peels for
  the actual no-fallback/no-receive generated dispatcher in
  `buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered`, with
  `buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function`
  and `buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function`
  further combining that generated shape with function-selector lookup facts.
  This leaves the EndToEnd SimpleStorage dispatcher reduction as aliases over
  native-harness facts. The
  remaining native dispatcher proof starts after that complete lazy-switch
  bridge, at proving `NativeBlockPreservesWord` for selected/default lowered
  bodies and threading the initialized prefix state plus the lowering lookup
  facts into the raw lowered switch block. The harness now exposes that raw
  switch shape as `lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts`
  and packages the raw block execution bridge with
  `exec_lowerNativeSwitchBlock_selector_find_hit_preserved_fuel`,
  `exec_nativeSwitchTail_find_hit_fresh_fuel`,
  `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel`,
  `exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel`,
  `exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel`,
  `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel`,
  `exec_lowerNativeSwitchBlock_selector_find_none_with_default_nonempty_fuel`,
  and `exec_lowerNativeSwitchBlock_selector_find_none_without_default_fuel`.
  The body preservation algebra now includes `state_lookup_insert_of_ne`,
  `nativeSwitchPrefixFinalState_matched`,
  `nativeSwitchPrefixFinalState_discr`,
  `nativeSwitchPrefixFinalState_marked`, `NativeBlockPreservesWord_nil`,
  `NativeBlockPreservesWord_cons`,
  `NativeBlockPreservesWord_singleton`,
  `NativeBlockPreservesWord_of_forall_stmt`,
  `NativeBlockPreservesWord_of_forall_stmt_write_not_mem`,
  `NativeStmtPreservesWord_block`,
  `NativeStmtPreservesWord_if_of_eval_self`,
  `NativeStmtPreservesWord_if_of_eval_preserves`,
  `NativeStmtPreservesWord_if_of_cond_preserves`,
  `nativeSwitchBranchFold_ok_preserves_word`,
  `execSwitchCases_ok_branch_preserves_word`,
  `NativeStmtPreservesWord_switch_of_eval_preserves`,
  `NativeStmtPreservesWord_switch_of_cond_preserves`,
  `NativeStmtPreservesWord_switch_of_cond_preserves_and_nativeStmtsWriteNames_not_mem`,
  `NativeStmtPreservesWord_switch_of_eval_preserves_and_nativeStmtsWriteNames_not_mem`,
  `NativeStmtPreservesWord_lowerAssignNative_lit_of_ne`,
  `NativeStmtPreservesWord_lowerAssignNative_hex_of_ne`,
  `NativeStmtPreservesWord_lowerAssignNative_ident_of_ne`,
  `NativeStmtPreservesWord_lowerAssignNative_str_of_ne`,
  `NativeStmtPreservesWord_let_none_of_not_mem`,
  `NativeStmtPreservesWord_let_var_of_not_mem`,
  `NativeStmtPreservesWord_let_lit_of_not_mem`,
  `NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem`,
  `NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem`,
  `NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem`,
  `NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem`,
  `NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_let_prim_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_let_user_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_nativeEvalArgs_call_preserves`,
  `NativePrimCallPreservesWord_calldatasize`,
  `NativePrimCallPreservesWord_callvalue`,
  `NativePrimCallPreservesWord_address`,
  `NativePrimCallPreservesWord_balance`,
  `NativePrimCallPreservesWord_origin`,
  `NativePrimCallPreservesWord_caller`,
  `NativePrimCallPreservesWord_timestamp`,
  `NativePrimCallPreservesWord_number`,
  `NativePrimCallPreservesWord_chainid`,
  `NativePrimCallPreservesWord_blobbasefee`,
  `NativePrimCallPreservesWord_gasprice`,
  `NativePrimCallPreservesWord_coinbase`,
  `NativePrimCallPreservesWord_gaslimit`,
  `NativePrimCallPreservesWord_selfbalance`,
  `NativePrimCallPreservesWord_unary_same_state`,
  `NativePrimCallPreservesWord_binary_same_state`,
  `NativePrimCallPreservesWord_ternary_same_state`,
  `NativePrimCallPreservesWord_iszero`,
  `NativePrimCallPreservesWord_shr`,
  `NativePrimCallPreservesWord_add`,
  `NativePrimCallPreservesWord_sub`,
  `NativePrimCallPreservesWord_mul`,
  `NativePrimCallPreservesWord_div`,
  `NativePrimCallPreservesWord_mod`,
  `NativePrimCallPreservesWord_sdiv`,
  `NativePrimCallPreservesWord_smod`,
  `NativePrimCallPreservesWord_addmod`,
  `NativePrimCallPreservesWord_mulmod`,
  `NativePrimCallPreservesWord_exp`,
  `NativePrimCallPreservesWord_signextend`,
  `NativePrimCallPreservesWord_eq`,
  `NativePrimCallPreservesWord_lt`,
  `NativePrimCallPreservesWord_gt`,
  `NativePrimCallPreservesWord_slt`,
  `NativePrimCallPreservesWord_sgt`,
  `NativePrimCallPreservesWord_and`,
  `NativePrimCallPreservesWord_or`,
  `NativePrimCallPreservesWord_xor`,
  `NativePrimCallPreservesWord_not`,
  `NativePrimCallPreservesWord_shl`,
  `NativePrimCallPreservesWord_byte`,
  `NativePrimCallPreservesWord_sar`,
  `NativePrimCallPreservesWord_sload`,
  `NativePrimCallPreservesWord_calldataload`,
  `NativePrimCallPreservesWord_mload`,
  `NativePrimCallPreservesWord_mstore`,
  `NativePrimCallPreservesWord_mstore8`,
  `NativePrimCallPreservesWord_tload`,
  `NativePrimCallPreservesWord_tstore`,
  `NativePrimCallPreservesWord_sstore`,
  `NativePrimCallPreservesWord_stop`,
  `NativePrimCallPreservesWord_return`,
  `NativePrimCallPreservesWord_revert`,
  `NativePrimCallPreservesWord_msize`,
  `NativePrimCallPreservesWord_gas`,
  `NativePrimCallPreservesWord_returndatasize`,
  `NativePrimCallPreservesWord_calldatacopy`,
  `NativePrimCallPreservesWord_returndatacopy`,
  `NativePrimCallPreservesWord_pop`,
  `NativePrimCallPreservesWord_keccak256`,
  `NativePrimCallPreservesWord_log0`,
  `NativePrimCallPreservesWord_log1`,
  `NativePrimCallPreservesWord_log2`,
  `NativePrimCallPreservesWord_log3`,
  `NativePrimCallPreservesWord_log4`,
  `NativeExprPreservesWord`,
  `NativeEvalArgsPreservesWord`,
  `NativeExprPreservesWord_var`,
  `NativeExprPreservesWord_lit`,
  `NativeEvalArgsPreservesWord_nil`,
  `NativeEvalArgsPreservesWord_cons`,
  `NativeEvalArgsPreservesWord_map_lowerExprNative`,
  `NativeEvalArgsPreservesWord_map_lowerExprNative_reverse`,
  `NativeExprPreservesWord_lowerExprNative_lit`,
  `NativeExprPreservesWord_lowerExprNative_hex`,
  `NativeExprPreservesWord_lowerExprNative_str`,
  `NativeExprPreservesWord_lowerExprNative_ident`,
  `NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves`,
  `NativeExprPreservesWord_call_prim_of_nativeEvalArgs_primCall_preserves`,
  `NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves`,
  `NativeExprPreservesWord_call_user_of_evalArgs_call_preserves`,
  `NativeExprPreservesWord_call_user_of_nativeEvalArgs_call_preserves`,
  `NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeExprPreservesWord_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_prim_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_user_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_return_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_nativeEvalArgs_and_evalArgs_shape_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_stop`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop`,
  `nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem`,
  `collectNativeStmtWriteNames_append`,
  `nativeStmtsWriteNames_append`,
  `nativeStmtsWriteNames_cons`,
  `nativeStmtsWriteNames_cons_not_mem_iff`,
  `nativeStmtsWriteNames_head_not_mem_of_cons_not_mem`,
  `nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem`,
  `nativeStmtsWriteNames_left_not_mem_of_append_not_mem`,
  `nativeStmtsWriteNames_right_not_mem_of_append_not_mem`,
  `nativeStmtsWriteNames_append_not_mem_iff`,
  `NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem`,
  `NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem`,
  `NativeBlockPreservesWord_append_of_forall_stmt`,
  `NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem`,
  `NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_append_not_mem`,
  `NativeStmtPreservesWord_block_of_nativeStmtsWriteNames_not_mem`,
  `NativeStmtPreservesWord_if_of_eval_preserves_and_nativeStmtsWriteNames_not_mem`,
  `NativeStmtPreservesWord_if_of_cond_preserves_and_nativeStmtsWriteNames_not_mem`,
  `NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched`,
  `NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_discr`,
  `NativeBlockPreservesWord_of_nativeSwitchFresh_default_matched`,
  `NativeBlockPreservesWord_of_nativeSwitchFresh_default_discr`,
  `nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem`,
  `nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem`,
  `nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem`,
  `nativeSwitchTempsFreshForNativeBodies_find_hit_matched_not_mem`, and
  `nativeSwitchTempsFreshForNativeBodies_default_matched_not_mem`. The selected
  switch-tail and lowered-switch hit paths consume generated
  `nativeSwitchTempsFreshForNativeBodies` freshness through reusable native
  block preservation wrappers and the execution lemmas
  `exec_nativeSwitchTail_find_hit_fresh_fuel` and
  `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel`; the
  store-parametric lowered-switch success path uses
  `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel` to carry the
  same freshness reasoning through states that already contain generated
  dispatcher bindings such as `__has_selector`. The adapter now names
   the needed freshness surface with `yulStmtWriteNames`,
   `yulStmtsWriteNames`,
   `nativeStmtWriteNames`, `nativeStmtsWriteNames`,
   `nativeSwitchTempsFreshForWrites`,
   `nativeSwitchTempsFreshForSourceBodies`, and
   `nativeSwitchTempsFreshForNativeBodies`; the key precondition to discharge
   is that fresh native switch temporaries are not reassigned by lowered
   case/default bodies while the selected body runs.

2. Prove native state bridge lemmas.

   Required fields:
   - selector and calldata byte layout,
   - caller/source and current address,
   - callvalue,
   - block timestamp, block number, chain id, and blob base fee,
   - storage lookup and storage write projection,
   - transient storage where generated Yul uses `tload`/`tstore`,
   - memory and returndata for ABI return/revert/log paths.

3. Prove native result projection lemmas.

   Required cases:
   - normal expression values returned by `callDispatcher`,
   - `stop`,
   - 32-byte `return`,
   - `revert` with rollback,
   - log projection with topics followed by word-aligned data,
   - hard native errors mapping to conservative failure.

4. Add wider executable coverage for the native path.

   The native theorem seam now compares native execution and the interpreter
   oracle under the same explicit fuel, but the existing Layer 3 preservation
   theorem is still only composed at the default runtime fuel. Before the
   public target can accept arbitrary native fuel, either prove the Layer 3
   preservation theorem fuel-parametrically or keep the public native wrapper
   total by choosing that default fuel internally.

   Current smoke coverage exercises primop lowering, including critical
   halt/log builtins, helper function maps, duplicate-helper failure, emitted
   dispatcher lowering shape and selector expression, lazy native dispatcher
   guards used instead of native `Switch` so matched selectors do not execute
   reverting default branches, block-scoped discriminator bindings for those
   lazy dispatcher guards, threaded native switch-discriminator ids across
   dispatcher statement lowering, per-switch matched flags that prevent
   non-halting duplicate case bodies from falling through, native assignment
   lowering through the named
   `lowerAssignNative` helper plus executable rebinding smoke coverage,
   dispatcher/helper
   partitioning that keeps helper definitions in the function map while
   dispatcher calls remain native user-function calls, fail-closed rejection
   of nested native function definitions in dispatcher/helper bodies, exact
   generated-fragment gate failures at the native runtime and IR-runtime
   entrypoints, the named
   `lowerExprNative_call_runtimePrimOp` and
   `lowerExprNative_call_userFunction` lemmas for native expression-call
   lowering,
   selector cases with their lowered storage-write and memory-return bodies,
   selector/calldata byte layout, ABI argument-word decoding, storage writes, `sload` through explicit
   observable pre-state slots, omitted-slot default reads, IR storage-read
   dispatcher lowering to native `SLOAD`, `interpretIRRuntimeNative` storage
   forwarding with explicit observable slots and prior events, the named
   `interpretIRRuntimeNative_eq_interpretRuntimeNative` lemma for that
   forwarding contract, `tstore`/`tload`
   execution through copied observable storage, initial native state contract
   installation, the named `initialState_installsExecutionContract` lemma for
   installed dispatcher code and mutable execution permission, the named
   `initialState_installsCurrentAccountContract` lemma for account-map runtime
   code installation at the current contract address, observable
   storage seeding, the named `initialState_observableStorageSlot` lemma for
   explicit observable pre-state slots, the named
   `initialState_omittedStorageSlot` lemma for omitted pre-state slot defaults,
   the named `projectStorageFromState_accountStorageSlot` and
   `projectStorageFromState_missingAccountStorageSlot` lemmas for final native
   account storage projection, the named
   `projectStorageFromState_missingAccount` lemma for absent-account default
   projection,
   and direct transaction-environment seeding for sender/source, value, current
   address, calldata selector/argument bytes, timestamp, and block number, the
   named `initialState_transactionEnvironment` lemma for those initial
   environment fields, the named `initialState_source`,
   `initialState_sender`, `initialState_codeOwner`, `initialState_weiValue`,
   `initialState_blockTimestamp`, `initialState_blockNumber`, and
   `initialState_calldata` lemmas for direct downstream rewriting of those
   native state bridge fields, the named `initialState_calldataSize` lemma for the native
   selector-plus-ABI-word calldata length, the named
   `calldataToByteArray_selectorByte0`,
   `calldataToByteArray_selectorByte1`,
   `calldataToByteArray_selectorByte2`, and
   `calldataToByteArray_selectorByte3` lemmas pinning the native calldata
   selector byte layout needed by dispatcher-selection proofs, the named
   `readBytes_zero_get?_of_lt_source`,
   `initialState_calldataReadWord_selectorByte0`,
   `initialState_calldataReadWord_selectorByte1`,
   `initialState_calldataReadWord_selectorByte2`, and
   `initialState_calldataReadWord_selectorByte3` lemmas showing that native
   `calldataload(0)` reads those selector bytes in its first ABI word. It also
   includes the named `initialState_calldataReadWord_selectorPrefix`,
   `uint256_shiftRight_224_ofNat_toNat`, `readBytes_zero_32_size`,
   `initialState_selectorExpr_native_value`, and
   `eval_lowerExprNative_selectorExpr_initialState_ok` lemmas proving native
   selector-value agreement for the bridged initial state, the named
   `exec_let_lowerExprNative_selectorExpr_initialState_ok`, `exec_let_lit_ok`,
   and `exec_nativeSwitchPrefix_selector_initialState_ok` lemmas for the
   generated native switch discriminator/matched-prefix initialization, the named
   `eval_nativeSwitchGuardedMatch_ok`, `eval_nativeSwitchGuardedMatch_hit_ok`,
   `exec_if_nativeSwitchGuardedMatch_hit`, `exec_lowerAssignNative_lit_ok`,
   `exec_if_nativeSwitchGuardedMatch_hit_marked`,
   `eval_nativeSwitchGuardedMatch_miss_ok`,
   `exec_if_nativeSwitchGuardedMatch_miss`,
   `eval_nativeSwitchGuardedMatch_matched_ok`,
   `exec_if_nativeSwitchGuardedMatch_matched`,
   `eval_nativeSwitchDefaultGuard_ok`,
   `eval_nativeSwitchDefaultGuard_unmatched_ok`,
   `eval_nativeSwitchDefaultGuard_matched_ok`,
   `exec_if_nativeSwitchDefaultGuard_unmatched`,
   `exec_if_nativeSwitchDefaultGuard_matched`, the fuel-parametric
   `_fuel` variants for generated case/default guards,
   `exec_nativeSwitchCaseIfs_all_miss_fuel`,
   `exec_nativeSwitchCaseIfs_matched_fuel`, and
   `exec_nativeSwitchCaseIfs_prefix_hit_fuel` for whole generated case chains,
   `nativeSwitch_find_hit_split`, `nativeSwitch_find_none_all_miss`,
   `exec_nativeSwitchCaseIfs_find_hit_fuel`, and
   `exec_nativeSwitchCaseIfs_find_none_fuel` for selector-lookup-driven case
   chain execution,
   `lowerSwitchCasesNativeWithSwitchIds_find?_some_of_find_function` and
   `lowerSwitchCasesNativeWithSwitchIds_find?_none_of_find_function` for
   generated dispatcher function-lookup facts lifted through native case
   lowering,
   `buildSwitchSourceCases_eq_switchCases`,
   `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_some_of_find_function`,
   and `lowerSwitchCasesNativeWithSwitchIds_buildSwitch_find?_none_of_find_function`
   for the actual `buildSwitch` source case list,
   `lowerRuntimeContractNative_single_stmt_eq_lowerStmtsNative` for singleton
   dispatcher-only runtime lowering,
   `lowerRuntimeContractNative_emitYul_noMapping_noInternals_noFallback_noReceive`
   for helper-free emitted runtime lowering,
   `lowerStmtsNative_single_block_ok_singleton` and
   `lowerStmtsNative_block_stmts_eq` for generic `.block` lowering shape,
   `lowerStmtsNativeWithSwitchIds_let_head_eq`,
   `lowerStmtsNativeWithSwitchIds_if_head_eq`, and
   `lowerStmtsNativeWithSwitchIds_singleton_switch_eq` for generic dispatcher
   statement peels,
   `lowerStmtsNativeWithSwitchIds_revert_zero_zero`,
   `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq`, and
   `lowerStmtsNativeWithSwitchIds_singleton_switch_revert_default_eq_sourceLowered`
   for generated selector-miss default-revert lowering,
   `buildSwitch_noFallback_noReceive_lowered_inner_sourceLowered` for the
   combined no-fallback/no-receive generated dispatcher lowering shape,
   `buildSwitch_noFallback_noReceive_lowered_inner_find?_some_of_find_function`
   and `buildSwitch_noFallback_noReceive_lowered_inner_find?_none_of_find_function`
   for generated dispatcher shape plus selector lookup,
   `exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel` and
   `exec_nativeSwitchDefaultIf_matched_fuel` for optional generated defaults,
   `exec_block_append_ok`,
   `exec_nativeSwitchCaseIfs_with_default_matched_fuel`,
   `exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel`,
   `exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel`, and
   `exec_nativeSwitchCaseIfs_find_none_without_default_fuel` for complete
   generated case-chain plus optional-default execution,
   `exec_lowerNativeSwitchBlock_selector_find_hit_preserved_fuel`,
   `exec_nativeSwitchTail_find_hit_fresh_fuel`,
   `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel`,
   `exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel`,
   `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_fresh`,
   `exec_lowerNativeSwitchBlock_selector_find_none_with_default_nonempty_fuel`,
   and `exec_lowerNativeSwitchBlock_selector_find_none_without_default_fuel`
   for raw lowered switch-block execution from the native initial state,
   and companion native `exec`/primitive reduction lemmas for the lazy guarded switch case/default gates,
   the native-switch write-target collectors and freshness predicates
   `yulStmtsWriteNames`, `nativeStmtsWriteNames`,
   `nativeSwitchTempsFreshForSourceBodies`, and
   `nativeSwitchTempsFreshForNativeBodies`, plus freshness projection lemmas
   for selected native bodies and optional defaults,
   plus the named
   private `bridgedExpr_selectorExpr` and
   `evalYulExprWithBackend_evmYulLean_selectorExpr_semantics` lemmas for the
   generated dispatcher selector expression on the isolated interpreter-oracle side, the named
   `initialState_unbridgedEnvironmentDefaults` lemma for
   base-fee/blob-field defaults and native-global `chainid` behavior, callvalue,
   caller/address, calldatasize, timestamp/number, a native-vs-reference-oracle
   runtime comparison for those bridged environment fields, selected-path
   fail-closed `chainid`/`blobbasefee` validation for non-representable
   `YulTransaction.chainId`/`YulTransaction.blobBaseFee`, executable `stop` halt
   projection, the named `projectHaltReturn_stop` and `projectResult_stop`
   lemmas for `stop`/zero-halt return projection, native log projection from
   topics plus word-aligned data with the named
   `projectLogEntry_topicsAndWordData` and `projectLogsFromState_logSeries`
   lemmas, successful native value result projection with committed
   storage/logs and matching `finalMappings`, the named
   `projectResult_ok` and `projectResult_ok_events` lemmas for successful
   native value results and event-history append behavior, native return
   halt projection with committed storage/logs and matching `finalMappings`,
   the named `projectResult_ok_success`, `projectResult_ok_returnValue`, and
   `projectResult_ok_finalMappings` lemmas for successful value-result
   projection, the named
   `projectHaltReturn_32ByteReturn`, `projectResult_yulHalt`,
   `projectResult_yulHalt_success`, `projectResult_yulHalt_returnValue`,
   `projectResult_yulHalt_finalMappings`, and `projectResult_yulHalt_events`
   lemmas for halt success, return-value, final-mapping, and event-history
   append behavior, and the named `projectResult_32ByteReturn` lemma for
   32-byte `return` halt projection, the named
   `projectHaltReturn_non32ByteReturn` and `projectResult_non32ByteReturn`
   lemmas pinning the current conservative non-word-sized return-buffer
   fallback until wider returndata support lands, log projection for `log0`
   through `log4` topic arities, conservative rollback projection for native errors,
   explicit hard-error rollback for `OutOfFuel`, explicit `Revert` rollback
   projection with no return value, the named `projectResult_revert` rollback,
   `projectResult_revert_success`, `projectResult_revert_returnValue`, and
   `projectResult_revert_finalMappings` final-mapping rollback and
   `projectResult_revert_events` event-history preservation lemmas, the named
   `projectResult_hardError_success` and `projectResult_hardError_returnValue`
   lemmas for hard native failure observables, the named
   `projectResult_ok_finalStorageSlot` and
   `projectResult_yulHalt_finalStorageSlot` lemmas for committed final-storage
   slot projection, the named `projectResult_ok_missingFinalStorageSlot` and
   `projectResult_yulHalt_missingFinalStorageSlot` lemmas for present-account
   missing-slot default projection, the named
   `projectResult_ok_missingFinalStorageAccountSlot` and
   `projectResult_yulHalt_missingFinalStorageAccountSlot` lemmas for
   absent-account final-storage default projection, the named
   `projectResult_revert_finalStorageSlot` and
   `projectResult_hardError_finalStorageSlot` lemmas for rollback final-storage
   slot projection,
   conservative `finalMappings` rollback on native errors with the named
   `projectResult_hardError_finalMappings` lemma, the named
   `projectResult_hardError` and `projectResult_hardError_events` lemmas for
   every non-halt native error, the named `projectResult_finalMappings` lemma
   showing every native projection keeps `finalMappings` synchronized with
   `finalStorage`, named `interpretRuntimeNative_loweringError` and
   `interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative`
   lemmas for fail-closed lowering and the successful lower/build/call/project
   native execution pipeline, `interpretIRRuntimeNative`
   forwarding/fail-closed lowering behavior, executable native-vs-reference
   oracle coverage for actual `Compiler.emitYul` dispatcher selection with
   explicit expected success/return/storage outcomes,
   ABI argument-word decoding, observable storage reads, generated
   `mappingSlot` helper execution for singleton mapping writes, singleton
   mapping reads, nested mapping writes, and `CompilationModel`-compiled
   packed mapping-struct member reads/writes plus singleton and nested
   multi-word mapping-struct member reads/writes, 32-byte return halt projection,
   multi-word memory-return fallback projection, and memory-backed revert rollback, and named
   `interpretIRRuntimeNative_loweringError` and
   `interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative`
   lemmas pinning the same fail-closed and exact native call-dispatcher
   pipeline at the IR entry point. Next coverage should include:
   - returndata and external-call outcomes,
   - static-call permission behavior,
   - proof-level preservation for the covered mapping member oracle cases.

5. Introduce the public generated native preservation theorem.

   The EndToEnd module keeps the arbitrary-fuel identity seam private. The
   file-local generated native theorem chain starts at:

   ```lean
   layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match
   ```

   It replaces the opaque bridge hypothesis with successful
   `lowerRuntimeContractNative`, successful
   `validateNativeRuntimeEnvironment`, and
   `nativeDispatcherExecMatchesIRPositive` for the lowered native contract, plus
   generated-code shape facts that discharge the executable generated-fragment
   check.
   The compiled supported path has a direct source-body-closure wrapper:
   `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure`.
   This variant derives the external no-`funcDef` generated-fragment witness
   from source-level static-scalar parameter witnesses plus compiled statement-list
   no-`funcDef` closure, leaving the native dispatcher match itself as the
   remaining proof obligation.
   The concrete `simpleStorage_endToEnd_native_evmYulLean` theorem now targets
   the direct projected `EvmYul.Yul.callDispatcher` result through
   `nativeGeneratedCallDispatcherResultOf`, after its retrieve-hit, store-hit,
   and selector-miss cases prove the lowered native dispatcher result matches
   `interpretIR` directly. The older `interpretIRRuntimeNative` SimpleStorage
   wrapper is file-local compatibility evidence. The generic selector-miss
   boundary is now
   packaged by
   `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq`,
   which exposes the native `Revert` execution and exact projected rollback
   result for arbitrary generated selector tables whose tags fit in one EVM
   word. The same miss package is also lifted to the public raw dispatcher
   boundary by
   `contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq`.
   Selector-hit native halt/error projection now has the analogous
   generic boundary
   `exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq`,
   with
   `contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq`
   lifting that package to the public raw dispatcher boundary,
   consumed by the SimpleStorage store-hit and retrieve-hit wrappers before
   their contract-specific IR comparisons. The store-parametric
   `exec_lowerNativeSwitchBlock_selector_find_hit_error_store_projectResult_eq`
   variant carries the same projection package through selector switches
   entered after earlier dispatcher-local bindings. The store-parametric
   selector-miss companion
   `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq`
   carries the exact revert rollback package through the same pre-bound local
   store shape, and
   `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq`
   lifts it through the generated dispatcher block shape after
   `__has_selector` is installed. Selector-hit halt/error projection has the
   matching block-level package
   `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq`.
   Selector-hit normal-success projection is carried by
   `exec_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq`,
   `exec_lowerNativeSwitchBlock_selector_find_hit_ok_store_projectResult_eq`
   and
   `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq`.

   This closes the SimpleStorage public theorem against the native
   lowered-dispatcher source of truth. The remaining generic work is to remove
   the private compatibility fuel-wrapper/reference-oracle theorem family that
   still exists for contracts without direct native dispatcher match proofs.

   A clean intermediate theorem is:

   ```lean
   interpretYulRuntimeWithBackend .evmYulLean emittedRuntime
     =
   interpretRuntimeNative fuel emittedRuntime ...
   ```

   for the safe generated fragment. Once that bridge is proved, retarget the
   Layer 3 and EndToEnd statements directly to the native execution target.

6. Flip the trust boundary only after the theorem target moves.

   Documentation should say EVMYulLean is the authoritative public semantic
   target, while making clear that retargeting evidence remains isolated in
   `EvmYulLeanRetarget.lean` and still routes through the private
   `execYulFuelWithBackend` transition executor until the generic native proof
   stack replaces it.

   The direct native target is now named `nativeIRRuntimeMatchesIR`: it compares
   `Native.interpretIRRuntimeNative` against `interpretIR` on the observable
   result surface. Remaining generated-fragment work can target a successful
   native run plus `nativeResultsMatchOn` against IR directly. The Layer 3 and
   Layers 2-3 native theorem spellings now consume `nativeIRRuntimeMatchesIR`;
   the older `_via_reference_oracle` native wrapper variants have been removed.
   At the raw lowered-dispatcher boundary,
   `nativeDispatcherExecMatchesIRPositive` and
   `nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match` expose the
   same direct native-vs-IR target for positive-fuel generated dispatcher
   proofs from the native harness. Concrete case proofs can now package normal,
   projected halt, and projected error runs with
   `nativeDispatcherExecMatchesIRPositive_of_exec_ok_match`,
   `nativeDispatcherExecMatchesIRPositive_of_exec_ok_project_eq_match`,
   `nativeDispatcherExecMatchesIRPositive_of_exec_yulHalt_project_eq_match`, and
   `nativeDispatcherExecMatchesIRPositive_of_exec_error_project_eq_match`.
   Generated-code shape facts lift this target through
   `nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match`,
   and compiled supported contracts can use
   `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure`
   or the Layer 3 / Layers 2-3 wrappers
   `layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match`
   and
   `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match`.
   Normal selector-hit execution has the matching raw dispatcher lift
   `contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_hit_ok_projectResult_eq`.
   SimpleStorage now keeps only the direct per-case splitter
   `simpleStorageNativeCallDispatcherMatchBridge_of_per_case` in this bridge
   path. The public `simpleStorage_endToEnd_native_evmYulLean` theorem consumes
   the direct projected `EvmYul.Yul.callDispatcher` result and discharges its
   native match with this direct splitter. The
   selector-miss revert arm is discharged by
   `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq`
   and its contract-dispatcher boundary lift
   `contractDispatcherExecResult_block_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult_eq`
   (with
   `exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_projectResult_eq`
   and
   `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_projectResult_eq`
   available for pre-bound dispatcher-local stores)
   before the SimpleStorage-specific selector table specialization reaches
   `simpleStorageNativeSelectorMissMatchBridge_proved`, and the retrieve-hit
   and store-hit selector wrappers consume
   `exec_lowerNativeSwitchBlock_selector_find_hit_error_projectResult_eq`
   (with
   `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error_projectResult_eq`
   and
   `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_projectResult_eq`
   available at the generated dispatcher block boundary)
   before their direct native-vs-IR proofs. The retrieve-hit arm has the proof
   `simpleStorageNativeRetrieveHitMatchBridge_proved`. The store-hit arm is
   closed by `simpleStorageNativeStoreHitMatchBridge_proved`, which covers both
   the short-calldata revert and argument-present storage update paths.

## Cleanup After the Flip (DoD-5 — completed)

- ~~Keep the legacy fuel-based executor and the private
  `execYulFuelWithBackend` wrapper in reference-oracle or isolated
  lower-level transition status~~ → **removed** (the legacy reference-oracle
  stack and the proof-interpreter retargeting layer were deleted in the
  EVMYulLean transition).
- Bridge-only docs that described the custom interpreter as the active
  semantic target have been updated to describe the native EvmYulLean
  dispatcher as the sole runtime authority.
- Upstream any EVMYulLean fork changes needed for memory, returndata, logs, or
  external-call semantics.

## PR 1822 — Achievement Summary

PR 1822 (`native-evmyullean-public-correctness`) lands the public-surface
retarget plus the first five leaf `ExecOnlyBridgeAtFuelRevived` constructors.
The Revived family now covers the observational-no-op body shapes a real
dispatcher will emit for label-only user bodies. The deeper "straight prefix
ending in `leave`/fall-through" cases are scoped out to a follow-up PR.

### Shipped in this PR

- **Public-surface retarget** — `interpretYulRuntimeEvmYulLean` and
  `interpretYulRuntimeEvmYulLeanFuel`; Layer 3 and SimpleStorage EndToEnd
  theorems retargeted to EVMYulLean conclusions; legacy reference-oracle
  paths renamed to `..._via_reference_oracle`; `defaultBuiltinBackend := .evmYulLean`.
  (The legacy `legacyBuiltinBackend`/`legacyEvalBuiltinCallWithContext`/legacy
  fuel executor opt-ins were later removed in DoD-5.)
- **Native EndToEnd surface** — `nativeResultsMatchOn`, the supported-compiler
  generated direct `EvmYul.Yul.callDispatcher` theorem and its helper-free /
  mapping-helper lowering wrappers, concrete SimpleStorage native theorem,
  case freshness dispatcher adapters, mapping switch freshness wrappers.
- **G1 increments S1–S4 (leaf Revived constructors)** —
  `.of_block_empty`, `.of_block_leave`, `.of_singleton_comment` shipped on
  `NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived`, plus the
  pre-existing `.of_empty_body` and `.of_leave_body`. `.of_comment_cons` is
  intentionally deferred to the success-bridge wiring layer (rationale below).
  Together these five constructors cover every body of shape `[]`, `[.leave]`,
  `[.block []]`, `[.block [.leave]]`, `[.comment text]` — the full
  observational-no-op family.
- **Supporting harness lemmas** — `exec_block_block_nil_ok_add_ten`,
  `exec_block_block_leave_ok_add_ten`, `exec_block_noop_block_head_eq`,
  `lowerStmtsNativeWithSwitchIds_comment_head_eq`, and the source-side
  `nativeResultsMatchOn_execIRFunction_*_body_markedPrefix` family.
- **Invariants preserved** — zero `sorry`, zero new axioms; `lake build
  Compiler.Proofs.EndToEnd` green; `make check` validators (axioms,
  capability boundary, builtin boundary, doc check) pass.

### Remaining for a follow-up PR

The composite `<straight-stmts>` and `<straight-stmts>; leave` body shapes,
and the final wiring + premise drop, are deferred. They share heavy proof
infrastructure (whole-block per-slot preservation, IR `execIRStmts`
falling-through induction) that does not fit a single landable increment in
the current branch's budget. See the
[G1 Incremental Plan](#g1-incremental-plan-generic-execonlybridgeatfuelrevived)
below for the exact constructor signatures, harness lemmas, and proof
sketches that the follow-up PR needs to land:

- **G1-S5** `.of_nativePreservableStraightStmts_leave` plus companion
  `execIRStmts_continue_of_nativePreservableStraightStmts_pre_leave` lemma.
- **G1-S6** `.of_bridgedStraightStmts_falling_through` (the deepest case;
  requires aligning `execIRFunction`'s fall-through extraction with the
  dispatcher's outer block exit).
- **G1-S7** Wire all five shipped leaves plus the two new constructors
  through `NativeGeneratedSelectorHitSuccessBridge` adapters, including
  per-leaf `_with_label_prefix` variants that strip a leading
  `.comment "label"` head via `exec_block_noop_block_head_eq`. This step
  also subsumes the deferred `.of_comment_cons` shape.
- **G1-S8** Drop `hUserBodyHalt` from
  `compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
  once S5–S7 are in.

## G1 Incremental Plan: Generic `ExecOnlyBridgeAtFuelRevived`

The remaining success-side blocker is a generic constructor for
`NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived` that does not
enumerate every concrete `fn.body` shape. The Revived predicate covers
**non-halting** bodies; halting bodies (`stop`/`return`/`revert`) are owned by
`NativeGeneratedSelectedUserBodyHaltExecBridgeAtFuel`, which already has a full
shape family.

Today only two Revived constructors exist:
`NativeGeneratedSelectedUserBodyExecOnlyBridgeAtFuelRevived.of_empty_body`
(`fn.body = []`) and `.of_leave_body` (`fn.body = [.leave]`). The remaining
Revived family is planned as a pyramid of independently-pushable
constructors, each of which compiles green on its own and is independently
useful to downstream adapters:

1. **`.of_block_empty`** — `fn.body = [.block []]`. Lowers to
   `[.Block []]`; closed by `exec_block_noop_block_head_eq` and
   `exec_block_nil_ok`. Source-side `execIRFunction` collapses the inner empty
   block to `.continue stateWithParams`, mirroring `.of_empty_body`. Needs a
   companion `nativeResultsMatchOn_execIRFunction_block_empty_markedPrefix`
   lemma.
2. **`.of_block_leave`** — `fn.body = [.block [.leave]]`. Lowers to
   `[.Block [.Leave]]`; closed by `exec_block_leave_ok_add_ten` after a
   `Block`-head peel. Mirrors `.of_leave_body`.
3. **`.of_singleton_comment`** — `fn.body = [.comment text]`. Lowers to
   `[.Block []]` via `lowerStmtsNativeWithSwitchIds_comment_head_eq`. Source
   side is `.continue state` (comment is a no-op at positive fuel).
4. **`.of_comment_cons`** — recursive adapter: if the tail satisfies the
   Revived predicate then so does `.comment text :: rest`. Discharges the
   no-op head with `exec_block_noop_block_head_eq` and matches the source-side
   `.continue` step.
   *Deferred to S8 wiring.* A direct Revived-level recursion is structurally
   awkward because the Revived predicate's `nativeGeneratedSelectorHitUserBodyFuel`
   computation depends on the contract's full `fn.body` size; recursing into
   `rest` would require either a predicate-level refactor that parameterizes
   over an explicit body shape, or full duplication of the predicate's logic
   inline. Instead, the runtime dispatcher's `.comment "label" :: <real body>`
   shape is handled at the `NativeGeneratedSelectorHitSuccessBridge` wiring
   layer (step 7): each leaf Revived constructor pairs with a one-shot
   comment-prefix adapter that strips the no-op label head, leaving the
   `<real body>` to match an existing leaf constructor.
5. **`.of_nativePreservableStraightStmts_leave`** — bodies of shape
   `<straight-stmts>; leave`. Composes `NativePreservableStraightStmts`
   preservation
   (`NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts`)
   with the `leave` checkpoint, yielding a `final.reviveJump` whose observable
   slots equal the source-side post-state. Requires an
   `execIRStmts_continue_of_nativePreservableStraightStmts_pre_leave` companion
   lemma in `IRInterpreter.lean` proving the source side falls through with the
   same observable storage.
6. **`.of_bridgedStraightStmts_falling_through`** — bodies of shape
   `<straight-stmts>` (no terminator). The hardest piece: requires the source
   side's `execIRStmts` falling through to `.continue` with native-side
   `NativeBlockPreservesWord` preservation, combined with the function-end
   fall-through convention shared between `execIRFunction` and `EvmYul.Yul.exec`.
7. **Wire into `NativeGeneratedSelectorHitSuccessBridge`** — extend
   `NativeGeneratedSelectorHitSuccessBridge.of_selected_user_body_exec_only_and_*`
   adapters so the new Revived constructors feed the existing
   `BridgedStraightStmts` and `mappingFree` result-bridge composition stacks.
8. **Drop the `hUserBodyHalt` premise from the supported-generated
   call-dispatcher composition theorem** — once the Revived family covers the
   same source-level scope as the Halt family, the public theorem premise
   collapses.

Each step lands as its own commit on `native-evmyullean-public-correctness`
and keeps `lake build Compiler.Proofs.EndToEnd` green. The pyramid is designed
so that partial completion (e.g., stopping after step 4) already removes
specific `hUserBodyHalt` demand for trivially-non-halting bodies, even before
the deep generic case at step 6 lands.

### Status of G1 increments

- **Step 1 (`.of_block_empty`)** — **shipped in PR 1822**
  (commit `fa980235`+rebase `8b46a6e7`). Pairs with new harness lemma
  `exec_block_block_nil_ok_add_ten` and source helper
  `nativeResultsMatchOn_execIRFunction_block_empty_body_markedPrefix`.
- **Step 2 (`.of_block_leave`)** — **shipped in PR 1822** (`a5d2e0d3`).
  Harness: `exec_block_block_leave_ok_add_ten`. Source helper:
  `nativeResultsMatchOn_execIRFunction_block_leave_body_markedPrefix`.
- **Step 3 (`.of_singleton_comment`)** — **shipped in PR 1822**
  (`f69044a1`+rebase `06723c83`). Reuses `exec_block_block_nil_ok_add_ten`;
  existential text extraction in the hypothesis. Source helper:
  `nativeResultsMatchOn_execIRFunction_singleton_comment_body_markedPrefix`.
- **Step 4 (`.of_comment_cons`)** — **intentionally deferred to step 7
  wiring** (`8e31e756`). Rationale: structural mismatch between the
  predicate's `nativeGeneratedSelectorHitUserBodyFuel`-on-full-`fn.body`
  and a tail-body recursion. Handled at the success-bridge layer via
  per-leaf comment-prefix adapters (S7), not as a standalone Revived
  constructor.
- **Step 5 (`.of_nativePreservableStraightStmts_leave`)** — **deferred to
  follow-up PR**.
  Companion lemma sketch:
  ```
  theorem execIRStmts_continue_of_nativePreservableStraightStmts_pre_leave
      (fuel : Nat) (state : IRState) (preStmts : List YulStmt)
      (hStmts : NativePreservableStraightStmts preStmts)
      (hFuel : sizeOf preStmts < fuel) :
      ∃ state',
        execIRStmts fuel state preStmts = .continue state' ∧
        ∀ slot, state'.storage.getD slot 0 = state.storage.getD slot 0 ∧
        state'.events = state.events
  ```
  Proof by induction on `preStmts` (or on the `NativePreservableStraightStmts`
  predicate) using the per-constructor cases in
  `EvmYulLeanNativeHarness.lean` lines ~18395–18410.
  Constructor sketch: the lowered native body is
  `lower(preStmts) ++ [.Leave]`; dispatcher-wrapped as
  `.Block (lower(preStmts) ++ [.Leave])`. Use
  `exec_block_append_eq_of_continue` (or similar splice lemma) to split exec
  across the append, derive `NativeBlockPreservesWord` for each observable
  slot via `NativeBlockPreservesWord_lowerStmtsNativeWithSwitchIds_of_nativePreservableStraightStmts`,
  then peel the trailing `.Leave` with `exec_block_leave_ok_add_ten` after
  one cons step.
- **Step 6 (`.of_bridgedStraightStmts_falling_through`)** — **deferred to
  follow-up PR**. Hardest piece. Same machinery as step 5 minus the trailing leave: the
  function-end fall-through convention must align `execIRFunction`'s
  post-`execIRStmts` extraction with the dispatcher's outer block exit. Key
  delta: source side returns `.continue state'` with no explicit terminator;
  must show this projects observationally identical to native's
  `.Block lower(preStmts)` `.ok` exit. Likely also needs an
  `execIRFunction_continue_extract_eq` lemma showing the IR function's return
  extraction at no-return-vars fn is a no-op.
- **Step 7 (success-bridge wiring + `.of_comment_cons` collapse)** —
  **deferred to follow-up PR**. Extend
  `NativeGeneratedSelectorHitSuccessBridge.of_selected_*` adapters to take
  per-leaf Revived constructors and inject the `.comment "label"`-head strip
  via `exec_block_noop_block_head_eq`. Each leaf gets a `_with_label_prefix`
  variant.
- **Step 8 (drop `hUserBodyHalt`)** — **deferred to follow-up PR**. Final
  theorem-level
  collapse: after the Revived family covers all source-side non-halting
  bodies the dispatcher can emit, the
  `compile_preserves_native_evmYulLean_of_compile_ok_supported_generated_callDispatcher`
  signature drops its `hUserBodyHalt` premise.

The PR-1822 shipped constructors (Step 1–3, plus the pre-existing
`.of_empty_body` and `.of_leave_body`) are independently useful: they
directly discharge the Revived premise for contracts whose selected
`fn.body` is one of `[]`, `[.leave]`, `[.block []]`, `[.block [.leave]]`, or
`[.comment text]`. This is the observational-no-op family — concrete
contracts whose user body is a label-only stub now have a direct Revived
bridge without going through the halt path.

Steps 5–8 remain the path to dropping `hUserBodyHalt` for non-trivial user
bodies. A future PR should pick up `execIRStmts_continue_of_nativePreservableStraightStmts_pre_leave`
first (purely IR-side, no harness coupling) before tackling the full
constructor proofs.
