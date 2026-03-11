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
- **Layer 2: CompilationModel -> IR**. The current proof surface is split:
  a generic supported-statement-fragment theorem lives in
  `Compiler/TypedIRCompilerCorrectness.lean` and
  `Compiler/Proofs/IRGeneration/SupportedFragment.lean`. A generic whole-contract
  theorem surface now also exists in `Compiler/Proofs/IRGeneration/Contract.lean`,
  but its function-level closure still depends on 1 narrower documented Layer-2
  axiom in `Compiler.Proofs.IRGeneration.Function`. The initial-state
  normalization step is now proved under an explicit transaction-context
  normalization hypothesis. Active end-to-end examples still rely on
  contract-specific theorems in `Contracts/Proofs/SemanticBridge.lean`.
- **Layer 3: IR -> Yul**. Yul semantics, equivalence, and preservation proofs
  live in `Compiler/Proofs/YulGeneration/`. The proof surface is generic, but the
  current full dispatch-preservation path still uses 1 documented bridge hypothesis.

## Key Modules

- `Contracts/Proofs/SemanticBridge.lean`: contract-level bridge theorems that
  connect EDSL executions to compiled IR/Yul executions for supported
  contracts. This is still the active full-contract Layer 2 bridge surface.
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

The compiler path consumes `CompilationModel` values directly; there is no
separate EDSL-lowering boundary module in the active pipeline.

## Layer 2 Status

The generic whole-contract theorem
`Compiler.Proofs.IRGeneration.Contract.compile_preserves_semantics` is proved
for arbitrary supported `CompilationModel`s, covering dispatch, parameter
loading, and initial-state normalization. The proof chain is complete (zero
sorry) but transitively depends on 1 documented axiom for non-core body
simulation (`supported_function_body_correct_from_exact_state` in
`Compiler/Proofs/IRGeneration/Function.lean`; see [AXIOMS.md](../../AXIOMS.md)).

**What is generic today:**
- Whole-contract theorem shape, dispatch, parameter loading
- Supported statement-list compilation (`SupportedFragment.lean`)
- Initial-state normalization (`withTransactionContext` ↔ `initialIRStateForTx`)

**What still needs per-contract work:**
- End-to-end examples still use manual bridge theorems in
  `Contracts/Proofs/SemanticBridge.lean`
- Internal helper calls work operationally but compositional proof reuse across
  callers is not yet a first-class interface ([#1335](https://github.com/Th0rgal/verity/issues/1335))

Tracking: [#1510](https://github.com/Th0rgal/verity/issues/1510) ·
[#1564](https://github.com/Th0rgal/verity/issues/1564) ·
[GENERIC_LAYER2_PLAN.md](../../docs/GENERIC_LAYER2_PLAN.md)

## Build

```bash
lake build                                      # Build everything
lake build Contracts.SimpleStorage.Proofs    # Build one contract's proofs
```

The proof tree currently has 0 `sorry`, but it still has the documented axioms
listed in `AXIOMS.md`.

## Infrastructure

### Core Semantics ([Verity/Core.lean](../../Verity/Core.lean), [Semantics.lean](../../Verity/Core/Semantics.lean))

EDSL execution lives in the `Contract` monad and `ContractState` defined in
`Verity/Core.lean`, with environment wrappers in `Verity/Core/Semantics.lean`.

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
