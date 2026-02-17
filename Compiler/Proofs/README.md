# Compiler Verification Proofs

Formal verification proofs for the Verity compiler, proving correctness across three layers.

## Verification Layers

- **Layer 1: EDSL ≡ ContractSpec** — User contracts satisfy their specs.
- **Layer 2: ContractSpec → IR** — IR generation preserves spec semantics.
- **Layer 3: IR → Yul** — All statement equivalence proofs proven (PR #42).

Key entry points:

- Spec semantics: `Verity/Proofs/Stdlib/SpecInterpreter.lean`
- IR generation and proofs: `Compiler/Proofs/IRGeneration/`
- Yul semantics and preservation: `Compiler/Proofs/YulGeneration/`

Layer 1 proofs live alongside each contract spec in `Verity/Specs/<Name>/Proofs.lean`.

## Build

```bash
lake build                                      # Build everything
lake build Verity.Specs.SimpleStorage.Proofs    # Build one contract's proofs
```

Expected warnings: `sorry` from `Verity.Specs.Ledger.SumProofs` (6 sum property proofs, Issue #65). `Verity.Specs.Common.Sum` is fully proven.

## Infrastructure

### SpecInterpreter ([SpecInterpreter.lean](../../Verity/Proofs/Stdlib/SpecInterpreter.lean))

Execution semantics for the ContractSpec language.

**Key Types**: `EvalContext` (execution environment), `SpecStorage` (abstract storage), `ExecutionResult` (success or revert with final state).

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
