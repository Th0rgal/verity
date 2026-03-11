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

Negative boundary example:
- A contract whose proof depends on linked external assumptions is outside the
  current supported fragment and still needs an explicit trust argument today.

Internal helper calls are part of the supported `CompilationModel` execution
surface, but the proof library does not yet provide a first-class
helper-spec/helper-theorem reuse boundary across callers. The compositional
internal-call proof gap now sits inside the `calls` body-support interface in
`Compiler/Proofs/IRGeneration/SupportedSpec.lean`, and its follow-on widening
work is tracked in
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
