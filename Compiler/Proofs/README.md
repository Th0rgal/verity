# Compiler Verification Proofs

Formal verification proofs for the Verity compiler across the active pipeline
`EDSL -> CompilationModel -> IR -> Yul`.

See `TRUST_ASSUMPTIONS.md` for the full trust boundary.

## Verification Layers

- **Layer 1: EDSL ≡ CompilationModel**. Contract-specific proofs live in
  `Contracts/<Name>/Proofs/`, with generic typed-IR compilation correctness in
  `Compiler/TypedIRCompilerCorrectness.lean`.
- **Layer 2: CompilationModel -> IR**. The IR generation proof surface lives in
  `Compiler/Proofs/IRGeneration/`.
- **Layer 3: IR -> Yul**. Yul semantics, equivalence, and preservation proofs
  live in `Compiler/Proofs/YulGeneration/`.

## Key Modules

- `Compiler/Proofs/SemanticBridge.lean`: contract-level bridge theorems that
  connect EDSL executions to compiled IR/Yul executions for supported
  contracts.
- `Compiler/Proofs/EndToEnd.lean`: composed Layers 2 and 3 theorem spine,
  showing compiled IR execution matches Yul execution.
- `Compiler/Proofs/IRGeneration/Expr.lean` and
  `Compiler/Proofs/IRGeneration/IRInterpreter.lean`: Layer 2 semantics and
  interpreter lemmas for the compilation-model path.
- `Compiler/Proofs/YulGeneration/`: Layer 3 semantics, statement equivalence,
  codegen preservation, builtin modeling, and patch-rule proofs.
- `Compiler/Proofs/MappingSlot.lean` and
  `Compiler/Proofs/ArithmeticProfile.lean`: focused proof support for storage
  layout invariants and arithmetic/backend alignment.

The current compiler path consumes `CompilationModel` values directly. There is
no separate verified EDSL-lowering boundary module in the active pipeline.

## Build

```bash
lake build                                      # Build everything
lake build Contracts.SimpleStorage.Proofs    # Build one contract's proofs
```

All proofs complete — no `sorry` warnings expected.

## Infrastructure

### SpecInterpreter ([SpecInterpreter.lean](../../Verity/Proofs/Stdlib/SpecInterpreter.lean))

Execution semantics for the compilation-model language (`CompilationModel` today).

**Key Types**: `EvalContext` (execution environment), `SpecStorage` (abstract storage), `ExecState` (execution state with storage, return value, and halt flag).

**Key Functions**: `evalExpr` (expression evaluation), `execStmt` (statement execution), `interpretSpec` (top-level interpreter).

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
    let specResult := interpretSpec spec (edslToSpecStorage state) tx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  unfold getValue Contract.runValue spec interpretSpec
  simp [getStorage, execFunction, execStmt, evalExpr]
```

### 2. Storage Updates

```lean
theorem setter_correct (state : ContractState) (value : Uint256) (sender : Address) :
    let finalState := (setValue value).runState { state with sender := sender }
    finalState.storage slot = value := by
  unfold setValue Contract.runState
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
