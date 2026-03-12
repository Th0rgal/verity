# Compiler Verification Proofs

Formal verification proofs for the Verity compiler across the active pipeline
`EDSL -> CompilationModel -> IR -> Yul`.

See `TRUST_ASSUMPTIONS.md` for the full trust boundary.

## Verification Layers

- **Layer 1: EDSL ≡ CompilationModel**. This is the frontend semantic bridge.
  Contract-specific specification proofs live separately in
  `Contracts/<Name>/Proofs/`, while generic typed-IR compilation correctness
  lives in `Compiler/TypedIRCompilerCorrectness.lean`. The generic core is
  real, but the active bridge theorems are still instantiated per contract.
- **Layer 2: CompilationModel -> IR**. A generic supported-statement-fragment
  theorem lives in `Compiler/TypedIRCompilerCorrectness.lean` and
  `Compiler/Proofs/IRGeneration/SupportedFragment.lean`, and the compiler-proof
  layer now closes a generic whole-contract theorem in
  `Compiler/Proofs/IRGeneration/Contract.lean`. The initial-state normalization
  step is proved under an explicit transaction-context normalization hypothesis.
  Layer 2 no longer depends on a Lean axiom.
- **Layer 3: IR -> Yul**. Yul semantics, equivalence, and preservation proofs
  live in `Compiler/Proofs/YulGeneration/`. The proof surface is generic, but the
  current full dispatch-preservation path still uses 1 documented bridge hypothesis.

## Key Modules

- `Compiler/Proofs/EndToEnd.lean`: composed Layers 2 and 3 theorem spine,
  showing compiled IR execution matches Yul execution.
- `Compiler/Proofs/IRGeneration/Expr.lean` and
  `Compiler/Proofs/IRGeneration/IRInterpreter.lean`: Layer 2 semantics and
  interpreter lemmas for the compilation-model path.
- `Compiler/Proofs/IRGeneration/SupportedFragment.lean`: exposes the current
  generic Layer 2 theorem for the explicit `SupportedStmtList` fragment.
- `Compiler/Proofs/YulGeneration/`: Layer 3 semantics, statement equivalence,
  codegen preservation, builtin modeling, and patch-rule proofs.
- `Compiler/Proofs/MappingSlot.lean` and
  `Compiler/Proofs/ArithmeticProfile.lean`: focused proof support for storage
  layout invariants and arithmetic/backend alignment.

The current compiler path consumes `CompilationModel` values directly. There is
no separate verified EDSL-lowering boundary module in the active pipeline.
This branch now includes the generic compiler-level theorem
`Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics`, rooted at
successful `CompilationModel.compile` for an explicit supported whole-contract
fragment. The former exact-state body-simulation axiom in
`Compiler.Proofs.IRGeneration.Function` has now been eliminated.

Tracking:
- theorem shape: [#1510](https://github.com/Th0rgal/verity/issues/1510)
- axiom elimination: [#1618](https://github.com/Th0rgal/verity/issues/1618)
- completeness/generalization: [#1630](https://github.com/Th0rgal/verity/issues/1630)
- plan: [`docs/GENERIC_LAYER2_PLAN.md`](../../docs/GENERIC_LAYER2_PLAN.md)
- machine-readable boundary catalog: [`artifacts/layer2_boundary_catalog.json`](../../artifacts/layer2_boundary_catalog.json)

## Current Layer 2 Boundary

What exists today:
- A structural theorem for raw statement lists admitted by the explicit
  `SupportedStmtList` witness:
  `Compiler.compile_supported_stmt_list_direct_semantics`
- A generic whole-contract theorem for successful `CompilationModel.compile` on
  the current explicit supported fragment:
  `Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics`
- Generic Layer 3 preservation from IR to Yul

What does not exist yet:
- Broader supported-fragment coverage for features still intentionally outside
  the current whole-contract theorem

Target claim:
- "whole EDSL" should be read as coverage of the macro-lowered `verity_contract`
  image, not arbitrary Lean terms that can construct `CompilationModel` values

Current supported-fragment scope for the generic theorem:
- Included: the explicit whole-contract supported fragment captured by
  `SupportedSpec`, including the generic dispatch/function/body closure proved
  under that witness
- Outside the current generic theorem: constructors, events/logs, linked
  externals, and other features intentionally excluded from the current
  supported fragment

The `SupportedSpec` split is now explicit and auditable in the machine-readable
catalog: global invariants, temporary surface exclusions, feature-local body
interfaces, and the current `calls.helpers` helper boundary all appear in
`artifacts/layer2_boundary_catalog.json`.

Negative boundary example:
- A contract whose proof depends on linked external assumptions is outside the
  current supported fragment and still needs an explicit trust argument today.

Internal helper calls are part of the supported `CompilationModel` execution
surface, but the proof library does not yet provide a first-class
helper-spec/helper-theorem reuse boundary across callers. The compositional
internal-call proof gap now sits inside the `calls.helpers` body-support
sub-interface in
`Compiler/Proofs/IRGeneration/SupportedSpec.lean`, and its follow-on widening
work is now split into:
- a positive direct-callee summary inventory already attached to `calls.helpers`
- a spec-aware helper source semantics target in `Compiler/Proofs/IRGeneration/SourceSemantics.lean`
- a reusable helper-summary contract API attached directly to those witnesses
- a reusable global helper-summary proof catalog
  (`SupportedHelperSummaryProofCatalog`) plus the theorem-level wrapper
  `SupportedSpecHelperProofs`, so each internal helper summary can be proved
  once and reused across every caller that references it
- helper-aware generic statement-induction interfaces
  `CompiledStmtStepWithHelpers` / `StmtListGenericWithHelpers` plus the
  induction-level body theorem
  `supported_function_body_correct_from_exact_state_generic_helper_steps`, so
  future helper-summary/rank proofs have an explicit induction target instead of
  only a body/function wrapper seam
- an exact helper-aware compiled induction seam
  `CompiledStmtStepWithHelpersAndHelperIR` /
  `StmtListGenericWithHelpersAndHelperIR` plus the induction-level body theorem
  `supported_function_body_correct_from_exact_state_generic_helper_steps_and_helper_ir`,
  so future helper-rich proofs can target `execIRStmtsWithInternals` directly
  instead of trying to consume helper-call cases through legacy `execIRStmts`
- a compiled-side fail-closed lifting witness/interface
  `StmtListCompiledLegacyCompatible` plus the exact-seam lifting lemmas
  `CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible` /
  `stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible`,
  so already-proved helper-free cases can also be reused inside the exact
  helper-aware compiled seam on legacy-compatible compiled bodies
- a weaker exact-seam compiled compatibility witness
  `StmtListHelperFreeCompiledLegacyCompatible` plus the split exact step
  interfaces `StmtListInternalHelperSurfaceStepInterface` and
  `StmtListResidualHelperSurfaceStepInterface`, where the genuine-helper side is
  now further split into
  `StmtListDirectInternalHelperCallStepInterface`,
  `StmtListDirectInternalHelperAssignStepInterface`,
  `StmtListDirectInternalHelperStepInterface`,
  `StmtListExprInternalHelperStepInterface`, and
  `StmtListStructuralInternalHelperStepInterface`, assembled through
  `stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface`,
  then bridged through
  `stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface`
  and
  `stmtListGenericWithHelpersAndHelperIR_of_core_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible`,
  so future helper-rich bodies only need genuinely new helper proofs at
  internal-helper heads while residual non-helper coarse-surface cases are kept
  separate from helper-summary work, and the genuine-helper proof work itself is
  now cut along direct-helper-call, direct-helper-assign, expression-helper,
  and structural-recursion lines
- a matching weaker source-side reuse witness
  `StmtListHelperFreeStepInterface` plus the direct split bridges
  `stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible`
  and
  `supported_function_body_correct_from_exact_state_generic_internal_helper_surface_steps_and_helper_ir`,
  so helper-rich bodies no longer need the whole list to satisfy
  `StmtListGenericCore` before they can target the exact helper-aware compiled
  body theorem
- a derivation of that compiled-side witness from the existing supported-body
  surface via
  `stmtListCompiledLegacyCompatible_of_supportedContractSurface` and
  `SupportedBodyInterface.compiledLegacyCompatible`; the weaker exact-seam
  witness is also derived directly via
  `stmtListHelperFreeCompiledLegacyCompatible_of_supportedContractSurface` and
  `SupportedBodyInterface.compiledHelperFreeLegacyCompatible`, plus the
  current-fragment exact body wrapper
  `supported_function_body_correct_from_exact_state_generic_with_helpers_and_helper_ir`,
  so today's supported fragment no longer needs a caller-supplied
  compiled-side witness just to reach the exact helper-aware compiled body goal
- matching helper-proof-carrying theorem variants in `Function.lean`,
  `Dispatch.lean`, and `Contract.lean`, so the public Layer 2 theorem family
  already exposes that input without changing the current trusted boundary
- helper-aware compiled-target wrapper theorems in `Contract.lean` and
  `Dispatch.lean` that already target `execIRFunctionWithInternals` /
  `interpretIRWithInternals` once the compiled-side conservative-extension
  equalities are supplied; those modules now also expose `_goal` variants that
  consume the named conservative-extension target
  `InterpretIRWithInternalsZeroConservativeExtensionGoal` plus an explicit
  legacy-compatibility witness instead of a raw equality, including
  `compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal`
- an interface-builder theorem
  `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtCompatibility`
  in `IRInterpreter.lean`, which assembles the full helper-free conservative-
  extension interface object from the already-proved expr / expr-list lemmas
  plus one stmt theorem
- a named remaining stmt-subgoal interface
  `InterpretIRWithInternalsZeroConservativeExtensionStmtSubgoals` in
  `IRInterpreter.lean`, together with
  `execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals` and
  `interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`,
  so the open compiled-side seam is now a compositional Lean object rather than
  only a prose checklist
- a dedicated world-preservation hook for expression-position helper callees
- a strictly decreasing helper-rank interface for direct callees, so future
  helper composition can target a well-founded measure instead of raw fuel
- feature-local `state` / `calls` / `effects` scans that recurse through nested
  `ite` / `forEach` bodies, so the interface inventory is whole-body rather than
  top-level only
- a temporary legacy fail-closed check that keeps the current theorem boundary unchanged

The exact blocker for removing that temporary helper gate is now machine-readable
in `artifacts/layer2_boundary_catalog.json`: callers still derive body closure
through the helper-free `SupportedStmtList`, summary-soundness evidence still is
not threaded through the exact helper-aware compiled body/IR preservation proof, and the
current public theorem stack still runs through the helper-free runtime
constructor `Dispatch.runtimeContractOfFunctions`, which now has an explicit
`internalFunctions = []` lemma. The intended compiled-side compatibility subset
is now explicit in `IRInterpreter.lean` as the legacy-compatible external-body
Yul subset `LegacyCompatibleExternalStmtList` together with the weaker contract-
level witness `LegacyCompatibleExternalBodies`, and the exact first compiled-side
retarget theorem is now encoded there as
`InterpretIRWithInternalsZeroConservativeExtensionGoal`.
That theorem still packages the stronger helper-free runtime-contract shape
`LegacyCompatibleRuntimeContract`, so the next whole-contract helper retarget is
not merely "derive one witness from `CompilationModel.compile`". On today's
fragment the external-body witness is now already derivable from the supported
body interface; the stronger
`internalFunctions = []` side of `LegacyCompatibleRuntimeContract` is not.
`IRInterpreter.lean` now also packages the expected proof decomposition as
`InterpretIRWithInternalsZeroConservativeExtensionInterfaces`, which splits that
goal into expr / stmt / stmt-list / function compatibility lemmas before they
are recomposed at the contract level. The expr / expr-list slice of that
interface is now already discharged in `IRInterpreter.lean` via
`evalIRExprWithInternals_eq_evalIRExpr_of_no_internal`,
`evalIRExprsWithInternals_eq_evalIRExprs_of_no_internal`, and the wrapper
theorem `InterpretIRWithInternalsZeroConservativeExtensionExprInterfaces`. The
helper-free conservative-extension goal is now closed rather than merely
decomposed:
`IRInterpreter.lean` now also factors the shared transaction setup through
`applyIRTransactionContext` and encodes the selected-function cut as
`InterpretIRWithInternalsZeroConservativeExtensionDispatchGoal` over
`LegacyCompatibleRuntimeDispatch`, and now also proves
`interpretIRWithInternalsZeroConservativeExtensionGoal_of_dispatchGoal` so that
the contract-level lift is no longer part of the open blocker. It also proves
`execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals`,
`execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility`,
`execIRFunctionWithInternals_eq_execIRFunction_of_stmtCompatibility`,
`interpretIRWithInternalsZeroConservativeExtensionDispatchGoal_of_stmtCompatibility`,
`interpretIRWithInternalsZeroConservativeExtensionGoal_of_stmtCompatibility`, and
`interpretIRWithInternalsZeroConservativeExtensionInterfaces_of_stmtSubgoals`,
plus the closed corollaries
`interpretIRWithInternalsZeroConservativeExtensionGoal_closed` and
`interpretIRWithInternalsZeroConservativeExtensionInterfaces_closed`, so
stmt-list compatibility, function compatibility, the dispatch-local theorem,
and the contract-level theorem no longer remain open on the helper-free subset.
`IRInterpreter.lean` now also proves
`execIRStmtsWithInternals_eq_execIRStmts_of_exprCompatibility` and
`execIRStmtWithInternals_eq_execIRStmt_of_exprCompatibility`, so the structural
`if` / `block` transport is already discharged and the named stmt-subgoal
interface is itself discharged for `runtimeContractOfFunctions`-style contracts
over the subset. `IRInterpreter.lean` now classifies dedicated expr-statement
builtin cases through
`exprStmtUsesDedicatedBuiltinSemantics` and already exposes direct helper-free
lemmas for `stop`, `mstore`, `revert`, `return`, and mapping-slot `sstore`, so
the broader theorem stack can instantiate the already-defined helper-aware
wrapper theorems rather than requiring another theorem-interface refactor.
`Contract.lean` now also exposes the direct closed helper-aware wrapper
`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`, and on
the current `SupportedSpec` fragment it now also exposes
`compile_preserves_semantics_with_helper_proofs_and_helper_ir_supported`, which
discharges the required `LegacyCompatibleRuntimeContract` witness directly from
successful `CompilationModel.compile`. The helper-aware compiled target remains
available as total fuel-indexed helper-aware IR semantics throughout the later
fragment-widening retargeting work. The remaining blocker is therefore no
longer a helper-free compiled-side witness on today’s theorem domain, but
  end-to-end consumption of helper-summary soundness/rank evidence through the
  genuinely new internal-helper cases in the exact helper-aware compiled
  seam, now cut into
  `StmtListDirectInternalHelperCallStepInterface`,
  `StmtListDirectInternalHelperAssignStepInterface`,
  `StmtListDirectInternalHelperStepInterface`,
  `StmtListExprInternalHelperStepInterface`, and
  `StmtListStructuralInternalHelperStepInterface`, past the transitional
  legacy-compiled-body goal `SupportedFunctionBodyWithHelpersIRPreservationGoal`,
  and then through the exact helper-rich body target
  `SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal`; the current
 function wrapper still feeds through
`supported_function_correct_with_helper_proofs_body_goal`, while widening or
replacing the helper-excluding `SupportedStmtList` fragment whose current
closure is now recorded as `SupportedStmtList.helperSurfaceClosed`. The older
source-side conservative-extension goal
`SourceSemantics.ExecStmtListWithHelpersConservativeExtensionGoal` remains only
as the current helper-free discharge path into
`supported_function_body_correct_from_exact_state_generic_with_helpers_goal`
and `supported_function_correct_with_helper_proofs_goal`, while the concrete
helper-free wrapper now already lifts legacy `CompiledStmtStep` /
`StmtListGenericCore` proofs into that helper-aware induction seam via
`CompiledStmtStep.withHelpers_of_helperSurfaceClosed` and
`stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed`; for later
widening beyond the current fragment, the weaker compiled-side boundary
tracked in [#1638](https://github.com/Th0rgal/verity/issues/1638) still
remains.

The remaining work tracked in
[#1630](https://github.com/Th0rgal/verity/issues/1630).

## Build

```bash
lake build                                      # Build everything
lake build Contracts.SimpleStorage.Proofs    # Build one contract's proofs
```

The proof tree currently has 0 `sorry`, but it still has the documented axioms
listed in `AXIOMS.md`.

## Infrastructure

### Core Semantics ([Verity/Core.lean](../../Verity/Core.lean), [Semantics.lean](../../Verity/Core/Semantics.lean))

The old `SpecInterpreter` module has been removed. EDSL execution now lives in
the `Contract` monad and `ContractState` defined in `Verity/Core.lean`, with
environment wrappers in `Verity/Core/Semantics.lean`.

**Key Types**: `Contract`, `ContractState`, `ContractResult`, `Env`, `World`.

**Key Functions**: `Contract.run`, `Contract.runState`, `Contract.runValue`,
`Env.ofWorld`, `World.withEnv`.

### Automation Library ([Automation.lean](../../Verity/Proofs/Stdlib/Automation.lean))

Proven helper lemmas for common proof patterns:

- **Safe arithmetic**: `safeAdd_some_iff_le`, `safeSub_some_iff_ge`, etc.
- **Storage operations**: `getStorage_runState`, `setStorage_runState`
- **Contract results**: `@[simp]` lemmas for `isSuccess`

## Proof Patterns

### 1. Simple Getters

```lean
theorem getter_correct (state : ContractState) (sender : Address) :
    let edslValue := (getValue.runValue { state with sender := sender }).val
    let result := Contract.run getValue { state with sender := sender }
    match result with
    | .success value _ => value = edslValue
    | .revert _ _ => False := by
  unfold getValue Contract.runValue Contract.run
  simp [getStorage]
```

### 2. Storage Updates

```lean
theorem setter_correct (state : ContractState) (value : Uint256) (sender : Address) :
    let finalState := (setValue value).runState { state with sender := sender }
    finalState.storage slot = value := by
  unfold setValue Contract.runState Contract.run
  simp [setStorage]
```

### 3. Boundary Conditions with Safe Arithmetic

```lean
theorem safe_op_succeeds (state : ContractState) (sender : Address)
    (h : condition) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation Contract.run
  have h_safe : (safeOp a b).isSome := by
    rw [safeOp_some_iff_condition]; exact h
  simp [h_safe]
```

### 4. Access Control

```lean
theorem authorized_operation (state : ContractState) (sender : Address)
    (h : state.storageAddr ownerSlot = sender) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation onlyOwner
  simp [h, msgSender, require]
```

## Common Tactics

| Tactic | Use case |
|--------|----------|
| `omega` | Linear arithmetic on naturals/integers |
| `simp [lemmas]` | Automatic simplification (prefer `simp only` for complex goals) |
| `unfold f` | Unfold definitions incrementally |
| `cases h : expr` | Case analysis on conditions or datatypes |
| `by_cases h : p` | Split proof on a Boolean condition |

## Resources

- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Tactics](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
