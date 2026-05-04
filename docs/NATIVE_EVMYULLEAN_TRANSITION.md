# Native EVMYulLean Runtime Transition

This document tracks the remaining work for issue #1737: make native
EVMYulLean execution the public Layer 3 semantic target for Verity-generated
runtime Yul.

The detailed completion contract and reusable agent prompt live in
[`NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md`](NATIVE_EVMYULLEAN_FULL_TRANSITION_DONE.md).

## Current State

The current public proof path still targets:

```lean
interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel
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
- The EndToEnd layer now exposes the native-facing theorem seam
  `layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge`.
  Its conclusion targets `Native.interpretIRRuntimeNative` through
  `nativeResultsMatchOn`, comparing success, return value, events, and the
  explicitly observable final-storage slots, and it now consumes the direct
  `nativeIRRuntimeMatchesIR` target instead of the older
  reference-oracle/fuel-wrapper wrapper alias. This is still not a completed
  public flip: the safe-body public Yul target remains the EVMYulLean fuel
  wrapper, and the generated native fragment still needs the direct match proof
  to become the public source-of-truth theorem.
- The same module also exposes
  `nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper`,
  `nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper`,
  `nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper_of_exec_agree`,
  `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper`,
  `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive`,
  `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_positive`,
  `nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper_of_dispatcherBlock_agree`,
  `nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_lowered_callDispatcher_agree`,
  `nativeIRRuntimeMatchesIR_of_generated_lowered_dispatcherExec_positive_match`,
  `nativeIRRuntimeMatchesIR_of_compiled_generated_lowered_dispatcherExec_positive_body_closure`,
  `layer3_contract_preserves_semantics_native_of_generated_dispatcherExec_positive_match`, and
  `layers2_3_ir_matches_native_evmYulLean_of_generated_dispatcherExec_positive_match`.
  These direct match seams keep the remaining proof obligation at concrete
  native lowering, selected-path environment validation, and raw positive
  dispatcher-exec matching against IR execution.
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
- The current
  `yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle`
  theorem still composes through
  `yulCodegen_preserves_semantics_via_reference_oracle` before rewriting the
  emitted runtime to the EVMYulLean backend executor. The explicit
  `yulCodegen_preserves_semantics_evmYulLeanFuelWrapperDefaultFuel_via_reference_oracle` theorem
  gives an EVMYulLean-backed Yul target, but it is not yet a native
  source-of-truth Layer 3 proof.
- The older generic native reference-oracle/fuel-wrapper aliases have been
  removed. The remaining native Layer 3 and supported EndToEnd seams consume
  `nativeIRRuntimeMatchesIR` directly, making the generated native fragment's
  direct match proof the visible blocker.

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
  defaults. The native harness names the remaining unbridged boundary with
  `initialState_unbridgedEnvironmentDefaults`, pinning base-fee/blob fields and
  native `chainid` to their current EVMYulLean default/global behavior until
  the follow-up widens the state bridge. The
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
   `contractDispatcherExecResult`. EndToEnd exposes
   `nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper`,
   `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper`,
   positive-fuel `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapperPositive`,
   `nativeDispatcherBlockAgreesWithEvmYulLeanFuelWrapper_of_exec_agree`,
   `nativeCallDispatcherAgreesWithEvmYulLeanFuelWrapper_of_dispatcherBlock_agree`.
   Positive-fuel callers that already prove raw dispatcher execution can now
   bypass those intermediate lifts via
   `nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_lowered_dispatcherExec_positive_agree`
   and the generated-shape
   `nativeIRRuntimeAgreesWithEvmYulLeanFuelWrapper_of_generated_lowered_dispatcherExec_positive_agree`.
   The remaining bridge is therefore direct native `EvmYul.Yul.exec` execution
   of the lowered contract dispatcher block against the EVMYulLean fuel wrapper.

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
   preservation lemmas against `execYulFuelWithBackend .evmYulLean`.
   EndToEnd now provides raw-exec intro forms for the three concrete native
   outcomes:
   `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_ok_agree`,
   `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_yulHalt_agree`, and
   `nativeDispatcherExecAgreesWithEvmYulLeanFuelWrapper_of_exec_error_agree`. These let
   each generated-statement simulation case finish from a proved
   `contractDispatcherExecResult` equation plus the corresponding observable
   projection agreement.

   The generated dispatcher selector expression is also pinned for the
   EVMYulLean-backed EVMYulLean fuel wrapper:
   `bridgedExpr_selectorExpr` shows that `selectorExpr` is in the bridged
   expression fragment, and
   `evalYulExprWithBackend_evmYulLean_selectorExpr_semantics` proves that it
   evaluates to `state.selector % selectorModulus`. This discharges the
   interpreter-oracle side of the first selector branch condition. The native
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
  the switch-temp counter interval for the selected lowered body. The
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
  `NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeExprPreservesWord_call_user_of_evalArgs_call_preserves`,
  `NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves`,
  `NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves`,
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
   `bridgedExpr_selectorExpr` and
   `evalYulExprWithBackend_evmYulLean_selectorExpr_semantics` lemmas for the
   generated dispatcher selector expression on the interpreter-oracle side, the named
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

5. Introduce the public native preservation theorem.

   The EndToEnd module now has a named native theorem seam:

   ```lean
   layers2_3_ir_matches_native_evmYulLean_of_evmYulLean_bridge
   ```

   It targets `Native.interpretIRRuntimeNative` directly, but only under:

   ```lean
   nativeIRRuntimeMatchesIR fuel irContract tx initialState
     observableSlots
   ```

   The next theorem in that chain is:

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
   The concrete `simpleStorage_endToEnd_native_evmYulLean` theorem now uses the
   direct positive dispatcher-exec match wrapper, after its retrieve-hit,
   store-hit, and selector-miss cases prove the lowered native dispatcher result
   matches `interpretIR` directly.

   This closes the SimpleStorage public theorem against the native
   lowered-dispatcher source of truth. The remaining generic work is to remove
   the compatibility fuel-wrapper/reference-oracle theorem family that still
   exists for contracts without direct native dispatcher match proofs.

   A clean intermediate theorem is:

   ```lean
   interpretYulRuntimeEvmYulLeanFuelWrapperDefaultFuel emittedRuntime
     =
   interpretRuntimeNative fuel emittedRuntime ...
   ```

   for the safe generated fragment. Once that bridge is proved, retarget the
   Layer 3 and EndToEnd statements directly to the native execution target.

6. Flip the trust boundary only after the theorem target moves.

   Documentation should say EVMYulLean is the authoritative semantic target
   only after the public theorem no longer routes through
   `execYulFuelWithBackend`. Until then, the accurate status is:
   EVMYulLean-backed builtin bridge proven, native runtime harness executable,
   native public theorem pending.

   The direct native target is now named `nativeIRRuntimeMatchesIR`: it compares
   `Native.interpretIRRuntimeNative` against `interpretIR` on the observable
   result surface. Remaining generated-fragment work can target a successful
   native run plus `nativeResultsMatchOn` against IR directly, while the current
   fuel-wrapper theorem remains explicitly named as the oracle side of the
   bridge. The
   non-`via_reference_oracle` Layer 3 and Layers 2-3 native theorem spellings
   now consume `nativeIRRuntimeMatchesIR`; the explicit `_via_reference_oracle`
   variants remain as compatibility wrappers for the older fuel-wrapper route.
   At the raw lowered-dispatcher boundary,
   `nativeDispatcherExecMatchesIRPositive` and
   `nativeIRRuntimeMatchesIR_of_lowered_dispatcherExec_positive_match` expose the
   same direct native-vs-IR target for positive-fuel generated dispatcher
   proofs. Concrete case proofs can now package normal, projected halt, and
   projected error runs with
   `nativeDispatcherExecMatchesIRPositive_of_exec_ok_match`,
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
   SimpleStorage also exposes the direct positive-dispatcher seam
   `simpleStorage_endToEnd_native_evmYulLean_of_positive_dispatcherExec_match`
   and a direct per-case splitter
   `simpleStorageNativeCallDispatcherMatchBridge_of_per_case`. The public
   `simpleStorage_endToEnd_native_evmYulLean` theorem now consumes this direct
   splitter. The selector-miss revert arm is discharged by
   `simpleStorageNativeSelectorMissMatchBridge_proved`, and the retrieve-hit
   arm has the direct native-vs-IR proof
   `simpleStorageNativeRetrieveHitMatchBridge_proved`. The store-hit arm is
   closed by `simpleStorageNativeStoreHitMatchBridge_proved`, which covers both
   the short-calldata revert and argument-present storage update paths.

## Cleanup After the Flip

- Move `legacyExecYulFuel` and `execYulFuelWithBackend` to reference-oracle status.
- Remove bridge-only docs that describe the custom interpreter as the active
  semantic target.
- Keep cross-check tests between the old oracle and native EVMYulLean for one
  release cycle.
- Upstream any EVMYulLean fork changes needed for memory, returndata, logs, or
  external-call semantics.
