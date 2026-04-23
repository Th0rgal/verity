# Native EVMYulLean Runtime Transition

This document tracks the remaining work for issue #1737: make native
EVMYulLean execution the public Layer 3 semantic target for Verity-generated
runtime Yul.

## Current State

The current public proof path still targets:

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
- The EndToEnd layer now exposes the native-facing theorem seam
  `layers2_3_ir_matches_native_evmYulLean_of_interpreter_bridge`. Its
  conclusion targets `Native.interpretIRRuntimeNative` through
  `nativeResultsMatchOn`, comparing success, return value, events, and the
  explicitly observable final-storage slots, but it still requires the explicit
  `nativeIRRuntimeAgreesWithInterpreter` obligation for the generated runtime.
  That obligation is observable-slot and fuel-aligned with the native run through
  `interpretYulRuntimeWithBackendFuel`, and the theorem seam currently requires
  that fuel to equal the interpreter proof stack's default runtime fuel
  `sizeOf (Compiler.emitYul contract).runtimeCode + 1`. This is the exact
  remaining native-vs-interpreter equivalence theorem plus a named
  full-storage-projection and fuel-parametric-preservation gap, not a completed
  public flip.
- The same module also exposes
  `nativeCallDispatcherAgreesWithInterpreter`,
  `nativeDispatcherBlockAgreesWithInterpreter`,
  `nativeCallDispatcherAgreesWithInterpreter_of_dispatcherBlock_agree`,
  `nativeIRRuntimeAgreesWithInterpreter_of_lowered_callDispatcher_agree`,
  `layer3_contract_preserves_semantics_native_of_lowered_callDispatcher_bridge`,
  and
  `layers2_3_ir_matches_native_evmYulLean_of_lowered_callDispatcher_bridge`.
  These move the remaining proof obligation down to concrete native lowering,
  selected-path environment validation, and projected native dispatcher-block
  execution agreement with the fuel-aligned interpreter oracle.
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
  `EvmYul.MIN_BASE_FEE_PER_BLOB_GAS`. The native harness names the remaining
  unbridged boundary with
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

   Progress: `EvmYul.Yul.callDispatcher` now unfolds through
   `callDispatcher_succ_eq_callDispatcherBlockResult` to the named
   `callDispatcherBlockResult`, then rewrites initial-state execution to
   `contractDispatcherBlockResult`, then peels the block wrapper to
   `contractDispatcherExecResult`. EndToEnd exposes
   `nativeDispatcherBlockAgreesWithInterpreter` plus
   `nativeDispatcherExecAgreesWithInterpreter`,
   `nativeDispatcherBlockAgreesWithInterpreter_of_exec_agree`, and
   `nativeCallDispatcherAgreesWithInterpreter_of_dispatcherBlock_agree`. The
   remaining bridge is therefore direct native `EvmYul.Yul.exec` execution of
   the lowered contract dispatcher block against the interpreter oracle.

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
   `nativeDispatcherExecAgreesWithInterpreter_of_exec_ok_agree`,
   `nativeDispatcherExecAgreesWithInterpreter_of_exec_yulHalt_agree`, and
   `nativeDispatcherExecAgreesWithInterpreter_of_exec_error_agree`. These let
   each generated-statement simulation case finish from a proved
   `contractDispatcherExecResult` equation plus the corresponding observable
   projection agreement.

   The generated dispatcher selector expression is also pinned for the
   EVMYulLean-backed interpreter oracle:
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
   The arithmetic recomposition side is named by `selectorBytesAsNat`, and
   `fromBytes'_selectorPrefix_shift` now proves the list-decoding side once the
   32-byte big-endian read word has the four ABI selector bytes at the high
   end. The remaining native selector proof is the EVMYulLean ByteArray/UInt256
   bridge that connects `State.calldataload`/`UInt256.shiftRight` over
   `ByteArray.readBytes` and `uInt256OfByteArray` to that 32-byte list shape.

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
   of nested native function definitions in dispatcher/helper bodies, the named
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
   `calldataload(0)` reads those selector bytes in its first ABI word, the named
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
   layers2_3_ir_matches_native_evmYulLean_of_interpreter_bridge
   ```

   It targets `Native.interpretIRRuntimeNative` directly, but only under:

   ```lean
   nativeIRRuntimeAgreesWithInterpreter fuel irContract tx initialState
     observableSlots
   ```

   The next theorem in that chain is:

   ```lean
   layers2_3_ir_matches_native_evmYulLean_of_lowered_callDispatcher_bridge
   ```

   It replaces the opaque bridge hypothesis with successful
   `lowerRuntimeContractNative`, successful
   `validateNativeRuntimeEnvironment`, and
   `nativeCallDispatcherAgreesWithInterpreter` for the lowered native contract.
   That obligation can now be discharged from
   `nativeDispatcherBlockAgreesWithInterpreter`, which compares projected
   `contractDispatcherBlockResult` execution with the interpreter oracle.
   The block obligation can in turn be discharged from
   `nativeDispatcherExecAgreesWithInterpreter`, which targets raw
   `contractDispatcherExecResult`.

   This makes the remaining proof obligation concrete: for the supported
   generated fragment, native `lowerRuntimeContractNative` plus
   `EvmYul.Yul.exec` of the lowered contract dispatcher block must produce the
   same projected `YulResult` as the current
   `interpretYulRuntimeWithBackend .evmYulLean` interpreter oracle. The
   successor theorem should discharge that bridge, or target a total native
   wrapper once the remaining closed-failure cases are ruled out by syntactic
   invariants.

   A clean intermediate theorem is:

   ```lean
   interpretYulRuntimeWithBackend .evmYulLean emittedRuntime
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

## Cleanup After the Flip

- Move `execYulFuel` and `execYulFuelWithBackend` to reference-oracle status.
- Remove bridge-only docs that describe the custom interpreter as the active
  semantic target.
- Keep cross-check tests between the old oracle and native EVMYulLean for one
  release cycle.
- Upstream any EVMYulLean fork changes needed for memory, returndata, logs, or
  external-call semantics.
