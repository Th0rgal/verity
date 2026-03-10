# Compiler Verification Proofs

Formal verification proofs for the Verity compiler across the active pipeline
`EDSL -> CompilationModel -> IR -> Yul`.

See `TRUST_ASSUMPTIONS.md` for the full trust boundary.

## Verification Layers

- **Layer 1: EDSL ≡ CompilationModel**. This is the frontend semantic bridge.
  Contract-specific specification proofs live separately in
  `Contracts/<Name>/Proofs/`, while generic typed-IR compilation correctness
  lives in `Compiler/TypedIRCompilerCorrectness.lean`.
- **Layer 2: CompilationModel -> IR**. The current proof surface is split:
  a generic supported-statement-fragment theorem lives in
  `Compiler/TypedIRCompilerCorrectness.lean` and
  `Compiler/Proofs/IRGeneration/SupportedFragment.lean`, while full-contract
  EDSL/CompilationModel-to-IR bridges still rely on contract-specific theorems
  in `Contracts/Proofs/SemanticBridge.lean`.
- **Layer 3: IR -> Yul**. Yul semantics, equivalence, and preservation proofs
  live in `Compiler/Proofs/YulGeneration/`.

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

The current compiler path consumes `CompilationModel` values directly. There is
no separate verified EDSL-lowering boundary module in the active pipeline, and
there is not yet a single generic theorem saying `CompilationModel.compile`
preserves semantics for every supported full contract.

## Current Layer 2 Boundary

What exists today:
- A structural theorem for raw statement lists admitted by the explicit
  `SupportedStmtList` witness:
  `Compiler.compile_supported_stmt_list_direct_semantics`
- Contract-specific bridge theorems in
  `Contracts/Proofs/SemanticBridge.lean` that instantiate the current
  compiler/interpreter machinery for specific contracts
- Generic Layer 3 preservation from IR to Yul

What does not exist yet:
- A compiler-level theorem quantified over an arbitrary supported
  `CompilationModel` and the successful result of `CompilationModel.compile`
- A generic dispatch/function-body/whole-contract Layer 2 preservation proof
  that removes the contract-specific `hpost` premise used by
  `spec_to_ir_preserves_semantics`

Current supported-fragment scope for the generic theorem:
- Included: statement lists that can be witnessed by `SupportedStmtList`
- Outside the current generic theorem: full contract dispatch, constructor
  lowering, mappings as contract-wide compilation targets, events/logs,
  external or linked functionality, and other features that still require
  contract-specific bridge work

Negative boundary example:
- A contract whose proof depends on entrypoint selection plus linked external
  assumptions is outside `SupportedStmtList` and still needs a contract-level
  bridge theorem today. `Contracts/Proofs/SemanticBridge.lean` remains the
  place where those full-contract bridges are instantiated.

Internal helper calls are part of the supported `CompilationModel` execution
surface, but the proof library does not yet provide a first-class
helper-spec/helper-theorem reuse boundary across callers. Existing bridge
theorems remain contract-specific; the compositional internal-call proof gap is
tracked in [#1335](https://github.com/Th0rgal/verity/issues/1335).

## Build

```bash
lake build                                      # Build everything
lake build Contracts.SimpleStorage.Proofs    # Build one contract's proofs
```

All proofs complete — no `sorry` warnings expected.

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
