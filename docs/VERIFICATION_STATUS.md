# Verification Status

For the full documentation, see [verity.thomas.md/verification](https://verity.thomas.md/verification).

## Architecture

Verity implements a **three-layer verification stack** proving smart contracts correct from specification to Yul bytecode:

```
EDSL contracts (Lean)
    ↓ Layer 1: EDSL ≡ CompilationModel [PROVEN FOR CURRENT CONTRACTS; GENERIC CORE, CONTRACT BRIDGES]
CompilationModel (declarative compiler-facing model)
    ↓ Layer 2: CompilationModel → IR [GENERIC WHOLE-CONTRACT THEOREM]
Intermediate Representation (IR)
    ↓ Layer 3: IR → Yul [GENERIC SURFACE, EXPLICIT BRIDGE HYPOTHESIS]
Yul (EVM Assembly)
    ↓ (Trusted: solc compiler)
EVM Bytecode
```

## Layer 1: EDSL ≡ CompilationModel, PROVEN FOR CURRENT CONTRACTS

**What it proves today**: The EDSL `Contract` monad execution is equivalent to `CompilationModel` interpretation for the current supported contract set. This is the frontend semantic bridge. The proof stack has a generic typed-IR core, but the active bridge theorems are still instantiated per contract. Separate per-contract proofs under `Contracts/<Name>/Proofs/` then show these contracts satisfy their human-readable specifications; those specification theorems are downstream contract proofs, not the definition of Layer 1 itself.

### Verified Contracts

| Contract | Properties | Status | Location |
|----------|------------|--------|----------|
| SimpleStorage | 20 | Complete | `Contracts/SimpleStorage/Proofs/` |
| Counter | 28 | Complete | `Contracts/Counter/Proofs/` |
| SafeCounter | 25 | Complete | `Contracts/SafeCounter/Proofs/` |
| Owned | 23 | Complete | `Contracts/Owned/Proofs/` |
| OwnedCounter | 48 | Complete | `Contracts/OwnedCounter/Proofs/` |
| Ledger | 33 | Complete | `Contracts/Ledger/Proofs/` |
| LocalObligationMacroSmoke | 4 | Baseline | `Contracts/LocalObligationMacroSmoke/Proofs/` |
| SimpleToken | 61 | Complete | `Contracts/SimpleToken/Proofs/` |
| ERC20 | 19 | Baseline | `Contracts/ERC20/Proofs/` |
| ERC721 | 11 | Baseline | `Contracts/ERC721/Proofs/` |
| ReentrancyExample | 5 | Complete | `Contracts/ReentrancyExample/Contract.lean` |
| CryptoHash | 0 | No specs | `Contracts/CryptoHash/Contract.lean` |
| **Total** | **277** | **✅ 100%** | — |

> **Note**: Stdlib (0 internal proof-automation properties) is excluded from the contract-spec theorem table above but included in overall coverage statistics (277 total properties).

Layer 1 uses macro-generated EDSL-to-`CompilationModel` bridge theorems backed by a generic typed-IR compilation-correctness theorem ([`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)). Tuple/bytes/fixed-array/dynamic-array/string parameters now stay inside that proof path when they are carried as ABI head words/offsets. Advanced constructs beyond that typed-IR head-word surface (linked libraries, ECMs, fully custom ABI behavior) are still expressed directly in `CompilationModel` and trusted at that boundary.

Internal helper calls are supported operationally in `CompilationModel` and the fuel-based interpreter path, but helper-level compositional proof reuse across callers is not yet a first-class verified interface. Current EDSL-to-`CompilationModel` bridge instantiations remain contract-specific; the remaining proof-level helper boundary is tracked in the Layer 2 completeness roadmap under [#1630](https://github.com/Th0rgal/verity/issues/1630), with the current interface/boundary refactor in [#1633](https://github.com/Th0rgal/verity/pull/1633).

## Layer 2: CompilationModel → IR — GENERIC WHOLE-CONTRACT THEOREM

Tracking:
- Theorem-shape milestone: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- Follow-on widening/completeness work: [#1630](https://github.com/Th0rgal/verity/issues/1630)
- Axiom-elimination work completed in: [#1618](https://github.com/Th0rgal/verity/issues/1618)
- Proof decomposition plan: [GENERIC_LAYER2_PLAN.md](./GENERIC_LAYER2_PLAN.md)

**What is generic today**:
- a structural theorem for raw statement lists inside the explicit `SupportedStmtList` fragment witness in [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean), re-exported for the compiler-proof layer in [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- a whole-contract theorem surface, [`compile_preserves_semantics`](../Compiler/Proofs/IRGeneration/Contract.lean), quantified over arbitrary supported `CompilationModel`s, selectors, a `SupportedSpec` witness, and successful `CompilationModel.compile` output; the source side is already expressed in the helper-aware semantics family using the canonical `SupportedSpec.helperFuel` bound

**What is not yet covered**:
- the supported whole-contract fragment is still intentionally narrower than the full `CompilationModel` surface; unsupported features remain documented at the boundary instead of being claimed as proved
- the body-level supported-fragment witness is now decomposed into feature-local interfaces (`core`, `state`, `calls`, `effects`) in [`SupportedSpec.lean`](../Compiler/Proofs/IRGeneration/SupportedSpec.lean), and the `calls` interface is further split into `helpers`, `foreign`, and `lowLevel`; `calls.helpers` now inventories direct helper callees through positive summary witnesses carrying an `InternalHelperSummaryContract` plus a strictly decreasing helper-rank measure, and expression-position helper callees are tracked separately with an explicit world-preservation-on-success obligation because the current helper-aware expression semantics returns only values. [`SourceSemantics.lean`](../Compiler/Proofs/IRGeneration/SourceSemantics.lean) exposes the helper-aware source execution target those future contracts will quantify over and now defines `InternalHelperSummarySound` / `SupportedBodyHelperSummariesSound` plus direct-call consumption lemmas for helper summaries. The feature-local `state` / `calls` / `effects` scans recurse through nested `ite` / `forEach` bodies, so these boundary witnesses are control-flow complete, but helper reuse, low-level calls, and richer observables are still outside the proved generic theorem until those interfaces are threaded through the body/IR composition lemmas
- the helper-aware source semantics is now proved to be a conservative extension of the current helper-free source semantics on the existing `SupportedSpec` fragment, and the public theorem surface is already anchored to that helper-aware semantics via `SupportedSpec.helperFuel`, so future helper-summary composition can target the same source-level semantics family without another theorem-shape rewrite or trusted-boundary change; `SourceSemantics.lean` now also defines the helper-free collapse goal `ExecStmtListWithHelpersConservativeExtensionGoal` together with a reusable global helper-summary proof catalog (`SupportedHelperSummaryProofCatalog`) that feeds `SupportedSpecHelperProofs`. `SupportedSpec.lean` now separates the coarse current helper exclusion (`stmtTouchesUnsupportedHelperSurface`) from the narrower exact-seam predicate `stmtTouchesInternalHelperSurface`, further cuts that genuine-helper surface into direct statement-position heads, expression-position heads, and structural recursive heads, and introduces the compiled-side glue `SupportedCompiledInternalHelperWitness` / `SupportedRuntimeHelperTableInterface`; `Contract.lean` proves `compile_ok_yields_supportedRuntimeHelperTableInterface`, so future exact helper-step proofs can assume a generic source-helper-to-runtime-helper-table mapping instead of re-deriving it ad hoc from `CompilationModel.compile`. `GenericInduction.lean` now exposes the helper-aware induction interfaces `CompiledStmtStepWithHelpers` / `StmtListGenericWithHelpers`, the lifting lemmas `CompiledStmtStep.withHelpers_of_helperSurfaceClosed` / `stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed`, the induction-level theorem `supported_function_body_correct_from_exact_state_generic_helper_steps`, the exact helper-aware compiled induction seam `CompiledStmtStepWithHelpersAndHelperIR` / `StmtListGenericWithHelpersAndHelperIR`, the strong helper-free compiled compatibility witness `StmtListCompiledLegacyCompatible`, the weaker future-proof exact-seam witnesses `StmtListHelperFreeCompiledLegacyCompatible` and `StmtListHelperFreeStepInterface`, the split exact helper-step interfaces `StmtListInternalHelperSurfaceStepInterface` / `StmtListResidualHelperSurfaceStepInterface`, the finer genuine-helper interfaces `StmtListDirectInternalHelperCallStepInterface` / `StmtListDirectInternalHelperAssignStepInterface` / `StmtListDirectInternalHelperStepInterface` / `StmtListExprInternalHelperStepInterface` / `StmtListStructuralInternalHelperStepInterface`, the exact-seam lifting lemmas `CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible` / `stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible`, the split bridges `stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible` / `stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible` plus coarser compatibility wrappers over `StmtListDirectInternalHelperStepInterface`, the body-level finer split bridge `supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir`, the compatibility wrapper `supported_function_body_correct_from_exact_state_generic_split_internal_helper_surface_steps_and_helper_ir`, the derivation lemmas `stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface` / `SupportedBodyInterface.compiledHelperFreeLegacyCompatible` / `stmtListHelperFreeStepInterface_of_core`, the exact induction-level body theorem `supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir`, the direct current-fragment exact-body wrapper `supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir`, the transitional legacy-compiled-body target `SupportedFunctionBodyWithHelpersIRPreservationGoal`, and the exact future helper-aware compiled-body target `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`; `Function.lean` exposes the matching function-level wrapper `supported_function_correct_with_helper_proofs_body_goal`, and the older goal wrappers (`supported_function_body_correct_from_exact_state_generic_with_helpers_goal`, `supported_function_correct_with_helper_proofs_goal`) are therefore now abstract helper-free discharge paths into the transitional target rather than the eventual helper-rich theorem target
- the machine-readable boundary catalog now makes that blocker exact rather than implicit: callers still reach the body theorem through the helper-free `SupportedStmtList` witness, and that helper exclusion is now derived directly in Lean as `SupportedStmtList.helperSurfaceClosed`; the helper-aware body theorem does not yet consume helper-summary soundness/rank evidence end to end. More precisely, that evidence is not yet consumed through the exact helper-aware compiled induction seam `CompiledStmtStepWithHelpersAndHelperIR` / `StmtListGenericWithHelpersAndHelperIR` and then into a direct proof of `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal` for the genuinely new internal-helper cases, even though `IRInterpreter.lean` now defines helper-aware compiled-side targets (`execIRFunctionWithInternals`, `interpretIRWithInternals`) that can resolve `IRContract.internalFunctions` and `Function.lean` / `Dispatch.lean` / `Contract.lean` now expose wrapper theorems that already target those helper-aware compiled semantics. `GenericInduction.lean` now also makes the interim compiled-side boundary explicit by proving that the older legacy-compiled-body goal `SupportedFunctionBodyWithHelpersIRPreservationGoal` lifts into `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal` on `LegacyCompatibleExternalStmtList` bodies when `IRContract.internalFunctions = []`, and it now also splits the exact helper-rich reuse boundary on both sides: the compiled side is reduced to `StmtListHelperFreeCompiledLegacyCompatible`, the residual non-helper side is isolated in `StmtListResidualHelperSurfaceStepInterface`, and the genuine internal-helper side is further reduced to `StmtListDirectInternalHelperCallStepInterface`, `StmtListDirectInternalHelperAssignStepInterface`, `StmtListExprInternalHelperStepInterface`, and `StmtListStructuralInternalHelperStepInterface`, with `StmtListDirectInternalHelperStepInterface` retained only as a compatibility wrapper over the two direct statement-position proof shapes, while the source side is reduced to `StmtListHelperFreeStepInterface`, combined by `stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible` and the body-level bridge `supported_function_body_correct_from_exact_state_generic_finer_split_internal_helper_surface_steps_and_helper_ir`. On today's fragment those weaker witnesses are now derived directly from the supported-body surface and the existing helper-free generic library, and `supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir` already reaches the exact helper-aware compiled body goal without a caller-supplied compiled-side premise and without requiring future helper-rich bodies to satisfy `StmtListGenericCore` wholesale. The intended legacy-compatible external-body Yul subset is now formalized directly in `IRInterpreter.lean` as `LegacyCompatibleExternalStmtList`, the weaker external-body witness is split out as `LegacyCompatibleExternalBodies`, the helper-free runtime-contract shape is now packaged as `LegacyCompatibleRuntimeContract`, and the exact first retarget theorem is now encoded as `InterpretIRWithInternalsZeroConservativeExtensionGoal`; `IRInterpreter.lean` now also decomposes that theorem into the explicit expr / stmt / stmt-list / function proof surface `InterpretIRWithInternalsZeroConservativeExtensionInterfaces`, factors shared transaction setup through `applyIRTransactionContext`, and still exposes the selected-function cut `InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal` with the bridge theorem `interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal` over `LegacyCompatibleRuntimeDispatch`. The helper-free conservative-extension goal is now closed on that subset, culminating in `interpretIRWithInternalsZeroConservativeExtensionGoal_closed`; the supporting closed surfaces include `InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals`, `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`, and the dedicated expr-statement builtin classifier `exprStmtUsesDedicatedBuiltinSemantics`, with direct helper-free lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`. `Dispatch.runtimeContractOfFunctions` now also has a `runtimeContractOfFunctions_legacyCompatible` bridge, and `Contract.lean` exposes the helper-aware `_goal` / `_closed` wrappers `compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal` and `compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`. It now also proves that successful `CompilationModel.compile` on the current `SupportedSpec` fragment yields the full `LegacyCompatibleRuntimeContract` witness, exposing a directly consumable helper-aware whole-contract theorem `compile_preserves_semantics_with_helper_proofs_and_helper_ir_supported` with no extra caller-supplied compiled-side premise. The helper-aware compiled target remains available as total fuel-indexed helper-aware IR semantics. The remaining blocker on today's theorem domain is therefore helper-summary soundness/rank consumption in the genuinely new internal-helper cases of the exact helper-aware compiled induction seam, now cut along the same direct-helper-call / direct-helper-assign / expression-helper / structural-recursion lines as the source-side helper lemmas, and then in a direct proof of `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal` while widening or replacing the helper-excluding statement fragment and proving the exact helper step interface at those heads. A later widening step still needs a weaker retarget boundary that can tolerate helper tables once helper-rich features move inside the theorem domain; that later compiled-side blocker remains tracked in [#1638](https://github.com/Th0rgal/verity/issues/1638)

**Intended end-state claim**:
- "whole EDSL" means the proof-complete macro-lowered image of `verity_contract`, not all arbitrary Lean-produced `CompilationModel` terms
- the widening target is to prove the generic theorem for that frontend image, or for a `CompilationModel` subset that the frontend lowering is proved to land inside
- the machine-readable companion for that claim and the current proof boundary is [`artifacts/layer2_boundary_catalog.json`](../artifacts/layer2_boundary_catalog.json)

### What is not fully migrated yet

- The generic theorem surface is in place, but the supported whole-contract fragment is still narrower than the full `CompilationModel` / EDSL surface.
- The contract/body support witness is no longer one undifferentiated exclusion bit, and helper calls now have an explicit summary inventory boundary, a reusable semantic summary contract slot, a global proof catalog for reusing helper-summary soundness across callers, and a dedicated source-semantics target, but the remaining excluded surfaces are still real proof gaps until the corresponding feature-local interfaces are consumed by positive theorem interfaces. In particular, helper reuse is still held behind the explicit helper-excluding `SupportedBodyInterface.stmtList` gate recorded in `artifacts/layer2_boundary_catalog.json`.
- Contracts and features outside `SupportedSpec` still rely on explicit trust-surface documentation, targeted testing, or future fragment-widening work rather than a claim of full generic compile-preservation.

**Current boundary**:
- Generic: supported statement-list compilation and the whole-contract theorem itself
- Proved generically: initial-state normalization between `withTransactionContext` and `initialIRStateForTx`, under explicit transaction-context normalization hypotheses
- No Lean axioms remain in Layer 2; 0 `sorry` placeholders remain. The `storageLookup_projectStorage` proof (previously a sorry) is now complete, using `Batteries.RBMap.find?_insert` lemmas with an injectivity argument over in-range storage slots.
- 6 stateful environment-reading builtins now have bridge proofs connecting Verity's `evalBuiltinCallWithContext` to the EVMYulLean state constructed by `toSharedState`: `callvalue`, `timestamp`, `number`, `caller` (requires valid address hypothesis), `address` (requires valid address hypothesis), and `calldatasize` (now reduced into UInt256 word semantics, so no extra size bound is needed)
- Additional explicit precondition: the generic theorem surface now requires the observed transaction-context fields (`sender`, `thisAddress`, `msgValue`, `blockTimestamp`, `blockNumber`, `chainId`) to already fit the bounded source-side `Address`/`Uint256` domains
- Outside the current generic theorem or current proof model: events/logs, proxy/delegatecall upgradeability, linked externals, local unsafe obligations, and other trust-surfaced features not captured by the current supported whole-contract fragment

Key files:
- [`TypedIRCompilerCorrectness.lean`](../Compiler/TypedIRCompilerCorrectness.lean)
- [`SupportedFragment.lean`](../Compiler/Proofs/IRGeneration/SupportedFragment.lean)
- [`Function.lean`](../Compiler/Proofs/IRGeneration/Function.lean)
- [`Contract.lean`](../Compiler/Proofs/IRGeneration/Contract.lean)
- [`EndToEnd.lean`](../Compiler/Proofs/EndToEnd.lean)

## Layer 3: IR → Yul, GENERIC, WITH EXPLICIT AXIOM BOUNDARY

**What it proves today**: Yul code generation preserves IR semantics through a generic statement/function equivalence stack, but the current full dispatch-preservation path still depends on 1 documented bridge hypothesis in [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean). The checked contract-level theorem surface now explicitly requires dispatch-guard safety for each selected function case: word-level zero `msg.value` on non-payable paths.

All 8 Yul statement types proven equivalent to IR counterparts. Universal dispatcher theorem:

```lean
theorem all_stmts_equiv : ∀ selector fuel stmt irState yulState,
    statesAligned selector irState yulState →
    execResultsAligned selector
      (execIRStmt irState stmt)
      (execYulStmtFuel fuel yulState stmt)
```

Key files: [`StatementEquivalence.lean`](../Compiler/Proofs/YulGeneration/StatementEquivalence.lean), [`Preservation.lean`](../Compiler/Proofs/YulGeneration/Preservation.lean), [`AXIOMS.md`](../AXIOMS.md)

### Phase 4: EVMYulLean Semantic Retargeting (sorry-dependent recursive statement-target fragment + conditional EndToEnd target)

The retargeting module [`EvmYulLeanRetarget.lean`](../Compiler/Proofs/YulGeneration/Backends/EvmYulLeanRetarget.lean) proves the following retargeting theorems:
- `backends_agree_on_bridged_builtins`: the `.verity` and `.evmYulLean` backends produce identical results at the `evalBuiltinCallWithBackendContext` level for all 36 bridged builtins (dispatch proof is sorry-free; delegates to the 36 per-builtin context-lifted bridge lemmas in `EvmYulLeanBridgeLemmas.lean`, 2 of which rest on sorry-backed core equivalences for smod/sar)
- `evalYulExpr_evmYulLean_eq_on_bridged`: `evalYulExpr` agrees with the `.evmYulLean` backend-parameterized evaluator for every `BridgedExpr` expression, including nested calls to bridged builtins and backend-independent `tload`/`mload`; this theorem transitively depends on the two sorry-backed smod/sar core equivalences
- `execYulFuelWithBackend_verity_eq`: the backend-parameterized statement executor recovers existing `execYulFuel` semantics at `.verity`, giving the next induction a verified executor surface
- `execYulFuelWithBackend_eq_on_bridged_straight_stmts`: `.verity` and `.evmYulLean` statement execution agree for straight-line statement lists satisfying `BridgedStraightStmts`, covering value bindings, `letMany`'s shared revert behavior, and dedicated statement-call semantics for mapping-slot, literal-slot, and identifier-slot `sstore`, `mstore`, `tstore`, `stop`, `return`, and `revert`; this theorem also transitively depends on the two sorry-backed smod/sar core equivalences through expression evaluation
- `execYulFuelWithBackend_block_eq_on_bridged_straight_stmts`: `.block` wrappers around those straight-line lists preserve the same backend equivalence
- `execYulFuelWithBackend_if_eq_on_bridged_body`: `.if_` statements with bridged conditions and straight-line bodies preserve the same backend equivalence
- `execYulFuelWithBackend_switch_eq_on_bridged_cases`: `.switch` statements with bridged scrutinees and straight-line selected case/default bodies preserve the same backend equivalence
- `execYulFuelWithBackend_for_eq_on_bridged_parts`: `.for_` statements with straight-line init/body/post lists and a bridged condition preserve the same backend equivalence
- `execYulFuelWithBackend_eq_on_bridged_target`: recursive `.verity = .evmYulLean` backend equivalence for `BridgedTarget` executions whose nested statements satisfy `BridgedStmt`
- `emitYul_runtimeCode_bridged`: the emitted runtime dispatch wrapper satisfies `BridgedTarget` when the IR function bodies, fallback/receive bodies, and internal helper statements it embeds satisfy `BridgedStmt`
- `emitYul_runtimeCode_evmYulLean_eq_on_bridged_bodies`: emitted runtime-code execution through Verity `execYulFuel` equals the EVMYulLean backend executor when those embedded function/entrypoint/internal bodies satisfy `BridgedStmts`
- `yulCodegen_preserves_semantics_evmYulLean`: the existing Layer-3 IR→Yul preservation theorem composed with the EVMYulLean backend runtime target, conditional on the same embedded-body `BridgedStmts` witnesses
- `layers2_3_ir_matches_yul_evmYulLean`: the public EndToEnd composition over the EVMYulLean backend runtime target, conditional on the same embedded-body `BridgedStmts` witnesses and existing entry-state hypotheses
- `genParamLoads_scalar_bridged`: scalar calldata parameter-loading prologues emitted by `genParamLoads` satisfy `BridgedStmts`
- `genStaticTypeLoads_calldataload_bridged`: static scalar leaf-load helpers for fixed arrays/tuples satisfy `BridgedStmts`
- `genParamLoads_static_scalar_bridged`: full calldata parameter-loading prologues for static scalar fixed arrays/tuples satisfy `BridgedStmts`
- `compileExpr_bridgedSource`: pure arithmetic/comparison/bit-operation source expressions in the `BridgedSourceExpr` fragment compile to `BridgedExpr`
- `compileStmtList_binding_leaf_bridged`: scalar-leaf `letVar`/`assignVar` source statement lists compile to `BridgedStmts`
- `compileStmtList_pure_binding_bridged`: pure arithmetic/comparison/bit-operation `letVar`/`assignVar` source statement lists compile to `BridgedStmts`
- `compileStmtList_storage_fragment_bridged`: pure binding plus unpacked single-slot `setStorage` source statement lists compile to `BridgedStmts`
- `compileStmtList_terminator_external_bridged`: external `stop`/`return` source statement lists compile to `BridgedStmts`
- `compileStmtList_internal_return_bridged`: internal `return` source statement lists compile to assignment-plus-`leave` `BridgedStmts`
- `compileStmtList_require_bridged`: plain `Stmt.require` source statement lists whose failure conditions compile to `BridgedExpr` compile to `BridgedStmts` (the emitted Yul is `if failCond revertWithMessage(msg)`; `revertWithMessage` is proven hypothesis-free to satisfy `BridgedStmts`)
- `compileStmtList_external_body_fragment_bridged`: mixed external source-body fragments made from pure bindings, unpacked single-slot `setStorage`, plain `require`, and external `stop`/`return` compile to `BridgedStmts`
- `compileStmtList_internal_body_fragment_bridged`: mixed internal source-body fragments made from pure bindings, unpacked single-slot `setStorage`, plain `require`, internal `return`, and `stop` compile to `BridgedStmts`
- `compileStmtList_external_structured_body_fragment_bridged`: mixed external source-body fragments plus one `Stmt.ite` layer around mixed-fragment branches compile to `BridgedStmts`
- `compileStmtList_internal_structured_body_fragment_bridged`: mixed internal source-body fragments plus one `Stmt.ite` layer around mixed-fragment branches compile to `BridgedStmts`
- `compileStmtList_external_nested_body_fragment_bridged`: mixed external source-body fragments plus two `Stmt.ite` layers around mixed/structured branches compile to `BridgedStmts`
- `compileStmtList_internal_nested_body_fragment_bridged`: mixed internal source-body fragments plus two `Stmt.ite` layers around mixed/structured branches compile to `BridgedStmts`
- `compileStmtList_external_recursive_body_fragment_bridged`: mixed external source-body fragments closed recursively under `Stmt.ite` compile to `BridgedStmts`
- `compileStmtList_internal_recursive_body_fragment_bridged`: mixed internal source-body fragments closed recursively under `Stmt.ite` compile to `BridgedStmts`

The backend-parameterized executor now has a proved `.verity = .evmYulLean` theorem for recursive statement targets constrained by `BridgedTarget`, the generated runtime wrapper is proved to preserve that predicate and to execute equivalently under explicit body-closure hypotheses, Layer 3 now has a contract-level theorem whose Yul side is `interpretYulRuntimeWithBackend .evmYulLean`, and the public EndToEnd module exposes conditional wrappers over that target. Body closure now covers scalar calldata parameter prologues, static scalar fixed-array/tuple parameter prologues, pure source-expression fragments, scalar/pure-expression let/assign statement-list bodies, pure-binding plus unpacked single-slot `setStorage` statement lists, external `stop`/`return` terminators, internal `return` assignment-plus-`leave` terminators, `Stmt.require` statements with bridged failure conditions, mixed external/internal body fragments composed from those pieces, and recursive `Stmt.ite` wrappers around those mixed fragments; full compiler-produced IR bodies are still pending.

Trust boundary (recursive statement-target fragment with conditional EndToEnd target): `BridgedExpr` expressions, `BridgedStraightStmts` statement lists, recursively nested `BridgedTarget` executions, emitted runtime wrappers whose embedded bodies are bridged, and public EndToEnd wrappers carrying those body hypotheses now inherit EVMYulLean semantics when their builtin dependencies are fully proven — "EVMYulLean's execution model matches the EVM" (backed by upstream Ethereum conformance tests) — rather than "Verity's custom builtin implementations are correct." Expressions or statements using smod/sar remain sorry-dependent until those core equivalences are discharged.

Not yet proven in this module:
- compiler-produced IR function/entrypoint body closure beyond scalar/static-scalar calldata parameter prologues and recursive pure-binding/single-slot `setStorage`/`require`/terminator/`Stmt.ite` fragments

Remaining gaps for whole-program retargeting:
- 2 sorry-backed core equivalences (smod, sar — complex sign/bit semantics)
- extend compiler-produced IR function/entrypoint body closure beyond scalar/static-scalar calldata parameter prologues and recursive pure-binding/single-slot `setStorage`/`require`/terminator/`Stmt.ite` fragments
- discharge the conditional EndToEnd EVMYulLean theorem's `BridgedStmts` hypotheses for full compiler-produced contracts

## Example Contract Compilation Coverage

The repository contains several different kinds of contract examples. Their current compile-preservation status is not uniform.

### Contracts covered by the generic Layer 2 theorem

All contracts within the `SupportedSpec` fragment are covered by the generic whole-contract theorem in `Compiler/Proofs/IRGeneration/Contract.lean`. No manual per-contract bridge proofs are needed.

### Spec proofs exist, contract-level compile-preservation is generic

All current contracts with spec proofs benefit from the generic Layer 2 theorem if they fall within the supported fragment. Contracts outside the fragment (e.g., those using linked externals or unsupported features) rely on testing for compile-preservation confidence.

### Semantic example, not a current `verity_contract` compilation example

- `ReentrancyExample`

`ReentrancyExample` is proved as a semantic case study in Lean, but it is not a current `verity_contract` macro contract with a contract-level compilation-preservation theorem surface in this repo.

### Intentionally outside the current proof-complete compilation subset

- `CryptoHash`: linked external Yul libraries / external call oracle surface
- `RawLogTrustSurface`: raw event emission trust surface
- `LocalObligationTrustSurface`: explicit local unsafe/refinement obligation surface
- `ProxyUpgradeabilityMacroSmoke`, `ProxyUpgradeabilityLayoutCompatibleSmoke`, `ProxyUpgradeabilityLayoutIncompatibleSmoke`: proxy / `delegatecall` / upgradeability semantics are outside the current proof model
- `StringSmoke`, `StringEventSmoke`, `StringErrorSmoke`: smoke examples for string, error, and event surfaces rather than current end-to-end proof-complete examples

Also note that the macro-generated `*_semantic_preservation` theorems are not contract-to-Yul semantic-preservation theorems. They are body-alignment equalities between generated `CompilationModel` bodies and macro-generated body fixtures, not full execution-preservation proofs for compiled IR/Yul.

## Property Test Coverage

| Contract | Coverage | Exclusions |
|----------|----------|------------|
| ERC20 | 100% (19/19) | 0 |
| ERC721 | 100% (11/11) | 0 |
| SafeCounter | 100% (25/25) | 0 |
| ReentrancyExample | 100% (5/5) | 0 |
| Ledger | 100% (33/33) | 0 |
| LocalObligationMacroSmoke | 100% (4/4) | 0 |
| SimpleStorage | 95% (19/20) | 1 proof-only |
| OwnedCounter | 92% (44/48) | 4 proof-only |
| Owned | 87% (20/23) | 3 proof-only |
| SimpleToken | 85% (52/61) | 9 proof-only |
| Counter | 82% (23/28) | 5 proof-only |
| Stdlib | 0% (0/0) | 0 proof-only |

**Status**: 92% coverage (255/277), 22 remaining exclusions all proof-only

- **Total Properties**: 277
- **Covered**: 255
- **Excluded**: 22 (all proof-only)

**Proof-Only Properties (22 exclusions)**: Internal proof machinery that cannot be tested in Foundry.

2 `sorry` remaining across `Compiler/**/*.lean` and `Verity/**/*.lean` proof modules.
2302 theorems/lemmas (1513 public, 789 private) verified by `lake build PrintAxioms`.

0 documented Lean axioms remain. The former mapping-slot range axiom has been eliminated via the kernel-computable Keccak engine. Selector computation is kernel-computable, the Layer 2 body-simulation axiom has been eliminated, and the Layer 3 dispatch bridge is tracked as an explicit theorem hypothesis rather than a Lean axiom.

## Differential Testing

**Status**: CI runs large sharded randomized differential suites against the current contract set, comparing EDSL interpreter output against Solidity-compiled EVM execution.

## Solidity Interop Support Matrix (Issue #586)

This matrix tracks migration-critical Solidity interoperability features and current implementation status.

Status legend:
- `supported`: usable end-to-end
- `partial`: implemented with functional limits or incomplete proof/test coverage
- `unsupported`: not implemented as a first-class feature

| Feature | Spec support | Codegen support | Proof status | Test status | Current status |
|---|---|---|---|---|---|
| Custom errors + typed revert payloads | partial | partial | n/a | partial | partial |
| Low-level calls (`call` / `staticcall` / `delegatecall`) with returndata | partial | partial | n/a | partial | partial |
| `fallback` / `receive` / payable entrypoint modeling | partial | partial | n/a | partial | partial |
| Event ABI parity for indexed dynamic/tuple payloads | supported | supported | supported | supported | supported |
| Storage layout controls (packing + explicit slots) | partial | partial | partial | partial | partial |
| ABI JSON artifact generation | partial | partial | n/a | partial | partial |

Diagnostics policy for unsupported constructs:
1. Report the exact unsupported construct at compile time.
2. Suggest the nearest supported migration pattern.
3. Link to the owning tracking issue.
4. When low-level mechanics, raw `rawLog` event emission, axiomatized primitives (for example `keccak256`), local unsafe/refinement obligations, or external assumptions are in play, emit a machine-readable trust report via `verity-compiler --trust-report <path>`. The report groups foreign trust surfaces into explicit `proofStatus.proved`, `proofStatus.assumed`, and `proofStatus.unchecked` buckets, localizes them to constructor/function `usageSites`, surfaces localized `localObligations`, and now separately lists `notModeledEventEmission`, `notModeledProxyUpgradeability`, `partiallyModeledLinearMemoryMechanics`, and `partiallyModeledRuntimeIntrospection` so the current event, proxy/upgradeability, memory/ABI, and runtime-context proof gaps are explicit in both contract-level and per-site audit output. In human-readable mode, `--verbose` now emits matching usage-site and contract-level summaries. For fail-closed verification runs, add `--deny-unchecked-dependencies`, which now reports the exact usage site that introduced each unchecked dependency. For proof-strict runs that reject any unproved foreign surface, use `--deny-assumed-dependencies`, which fails on both `assumed` and `unchecked` linked externals / ECM modules and reports the exact usage site. For primitive-proof-strict runs, add `--deny-axiomatized-primitives`, which fails on any remaining axiomatized primitive and reports the exact usage site. For local-obligation-proof-strict runs, add `--deny-local-obligations`, which fails on any remaining `assumed` or `unchecked` localized unsafe/refinement obligation and reports the exact usage site. For memory-proof-strict runs, add `--deny-linear-memory-mechanics`, which fails on any remaining partially modeled linear-memory mechanic and reports the exact usage site. For event-proof-strict runs, add `--deny-event-emission`, which fails on any remaining raw `rawLog` event emission and reports the exact usage site. For low-level-proof-strict runs, add `--deny-low-level-mechanics`, which fails on any remaining first-class low-level call / returndata mechanic and reports the exact usage site. For proxy-proof-strict runs, add `--deny-proxy-upgradeability`, which fails on any remaining `delegatecall`-based proxy / upgradeability mechanic and reports the exact usage site; the dedicated proxy semantics gap is tracked under issue `#1420`. For runtime-proof-strict runs, add `--deny-runtime-introspection`, which fails on any remaining partially modeled runtime-introspection primitive and reports the exact usage site.

## Trust Assumptions

See [`TRUST_ASSUMPTIONS.md`](../TRUST_ASSUMPTIONS.md) for the full trust model and [`AXIOMS.md`](../AXIOMS.md) for axiom documentation.

---

**Last Updated**: 2026-04-11
