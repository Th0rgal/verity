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
Verity's `YulResult` shape.

## What This PR Establishes

- The native target has an IR-contract entry point:
  `interpretIRRuntimeNative`.
- Native result projection preserves pre-existing event history and appends
  native EVMYulLean logs, matching the observable shape expected by the current
  proof-side `YulResult`.
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

1. Prove lowering invariants for the native contract shape.

   Required facts:
   - top-level `funcDef` nodes are partitioned into `YulContract.functions`,
   - dispatcher code contains no function definitions,
   - known runtime builtins lower to native `.inl` primops,
   - user/helper calls remain `.inr` function calls,
   - duplicate helper definitions fail closed.

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

   Current smoke coverage exercises primop lowering, helper function maps,
   storage writes, callvalue, return projection, and log projection. Next
   coverage should include:
   - dispatcher selector selection from emitted runtime code,
   - memory-heavy `return` and `revert`,
   - `log0` through `log4`,
   - returndata and external-call outcomes,
   - static-call permission behavior,
   - mapping helper lowering or replacement with native keccak/memory code.

5. Introduce the public native preservation theorem.

   The successor theorem should target `interpretIRRuntimeNative`, or a
   total wrapper around it once the remaining closed-failure cases are ruled
   out by syntactic invariants.

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
