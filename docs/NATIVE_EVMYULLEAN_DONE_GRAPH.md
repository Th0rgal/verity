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
  -> N6 whole runtime native/interpreter agreement
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
- **Status**: partially implicit in existing lowering/proof modules.
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
  hard native errors, storage rollback, logs, and storage projection.
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
    the interpreter oracle for every generated dispatcher shape.
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
- **Status**: `NativeBlockPreservesWord`, singleton/block-lift/if composition,
  list-level composition from per-statement preservation, selected freshness
  projection lemmas, and assignment constructors for literal/hex/identifier
  RHS forms exist; general preservation from `nativeStmtsWriteNames`
  freshness is not complete.
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
    agrees with the current interpreter-backed public semantic path on the
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
