# Compiler Verification Proofs

This directory contains formal verification proofs for the DumbContracts compiler, proving correctness across three layers of compilation.

## Verification Layers

- **Layer 1: EDSL ≡ ContractSpec** — Spec correctness for the user-facing contracts.
- **Layer 2: ContractSpec → IR** — IR generation preserves spec semantics.
- **Layer 3: IR → Yul** — Yul codegen preservation is in progress (semantics + scaffolding exist; full equivalence theorems pending).

Key entry points:

- Spec semantics: `DumbContracts/Proofs/Stdlib/SpecInterpreter.lean`
- IR generation and proofs: `Compiler/Proofs/IRGeneration/`
- Yul semantics and preservation: `Compiler/Proofs/YulGeneration/`

## Proof Layout

Layer 1 proofs live alongside each contract spec in `DumbContracts/Specs/<Name>/Proofs.lean` to match the user-facing workflow (Spec → Impl → Proofs).

## Quick Start

```bash
# Build all Layer 1 proofs
lake build DumbContracts.Specs.SimpleStorage.Proofs
lake build DumbContracts.Specs.Counter.Proofs
lake build DumbContracts.Specs.SafeCounter.Proofs
lake build DumbContracts.Specs.Owned.Proofs
lake build DumbContracts.Specs.OwnedCounter.Proofs
lake build DumbContracts.Specs.Ledger.Proofs
lake build DumbContracts.Specs.SimpleToken.Proofs

# Build infrastructure
lake build DumbContracts.Proofs.Stdlib.Automation
lake build DumbContracts.Proofs.Stdlib.SpecInterpreter
```

## Infrastructure Components

### SpecInterpreter ([SpecInterpreter.lean](../../DumbContracts/Proofs/Stdlib/SpecInterpreter.lean))

Defines the execution semantics for ContractSpec language.

**Key Types:**
- `EvalContext`: Execution environment (sender, params, local variables)
- `SpecStorage`: Abstract storage representation with slots and mappings
- `ExecutionResult`: Success or revert with final state

**Key Functions:**
- `evalExpr`: Expression evaluation with modular arithmetic
- `execStmt`: Statement execution (letVar, require, setStorage, etc.)
- `interpretSpec`: Top-level interpreter for ContractSpec

**Usage Example:**
```lean
let tx : Transaction := { sender := alice, functionName := "increment", args := [] }
let storage : SpecStorage := { slots := [(0, 42)], mappings := [] }
let result := interpretSpec counterSpec storage tx
-- result.success = true
-- result.finalStorage.getSlot 0 = 43
```

### Automation Library ([Automation.lean](../../DumbContracts/Proofs/Stdlib/Automation.lean))

Provides proven helper lemmas for common proof patterns.

#### Safe Arithmetic Lemmas

Complete automation for `safeAdd` and `safeSub` from `DumbContracts.Stdlib.Math`:

**safeAdd Lemmas:**
```lean
theorem safeAdd_some_iff_le (a b : Uint256) :
    (safeAdd a b).isSome ↔ (a : Nat) + (b : Nat) ≤ MAX_UINT256

theorem safeAdd_none_iff_gt (a b : Uint256) :
    (safeAdd a b).isNone ↔ (a : Nat) + (b : Nat) > MAX_UINT256

theorem safeAdd_some_val (a b : Uint256) (h : (a : Nat) + (b : Nat) ≤ MAX_UINT256) :
    safeAdd a b = some (a + b)
```

**safeSub Lemmas:**
```lean
theorem safeSub_some_iff_ge (a b : Uint256) :
    (safeSub a b).isSome ↔ (a : Nat) ≥ (b : Nat)

theorem safeSub_none_iff_lt (a b : Uint256) :
    (safeSub a b).isNone ↔ (a : Nat) < (b : Nat)

theorem safeSub_some_val (a b : Uint256) (h : (a : Nat) ≥ (b : Nat)) :
    safeSub a b = some (a - b)
```

**Usage in Proofs:**
```lean
-- Proving SafeCounter boundary conditions
have h : (state.storage 0).val ≥ 1 := ...
have h_safe : (safeSub (state.storage 0) 1).isSome := by
  rw [safeSub_some_iff_ge]
  exact h
```

#### Storage Operation Lemmas

```lean
-- getStorage preserves state
theorem getStorage_runState (slot : StorageSlot Uint256) (state : ContractState) :
    (getStorage slot).runState state = state

-- setStorage updates the state
theorem setStorage_runState (slot : StorageSlot Uint256) (value : Uint256) (state : ContractState) :
    (setStorage slot value).runState state =
      { state with storage := fun s => if s == slot.slot then value else state.storage s }
```

#### Contract Result Lemmas

Automatic simplification with `@[simp]` attribute:

```lean
@[simp]
theorem isSuccess_success (a : α) (s : ContractState) :
    (ContractResult.success a s).isSuccess = true

@[simp]
theorem isSuccess_revert (msg : String) (s : ContractState) :
    (ContractResult.revert msg s : ContractResult α).isSuccess = false
```

## Proof Patterns

### Pattern 1: Simple Getters

For read-only functions that just return storage values:

```lean
theorem getter_correct (state : ContractState) (sender : Address) :
    let edslValue := (getValue.runValue { state with sender := sender }).val
    let specResult := interpretSpec spec (edslToSpecStorage state) tx
    specResult.success = true ∧
    specResult.returnValue = some edslValue := by
  unfold getValue Contract.runValue spec interpretSpec
  simp [getStorage, execFunction, execStmt, evalExpr]
```

**Examples**: SimpleStorage.retrieve_correct, Counter.getCount_correct

### Pattern 2: Storage Updates

For functions that modify storage:

```lean
theorem setter_correct (state : ContractState) (value : Uint256) (sender : Address) :
    let finalState := (setValue value).runState { state with sender := sender }
    finalState.storage slot = value := by
  unfold setValue Contract.runState
  simp [setStorage]
```

**Examples**: SimpleStorage.store_correct

### Pattern 3: Boundary Conditions with Safe Arithmetic

For functions using `safeAdd`/`safeSub`:

```lean
theorem safe_op_succeeds (state : ContractState) (sender : Address)
    (h : condition) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation Contract.run
  have h_safe : (safeOp a b).isSome := by
    rw [safeOp_some_iff_condition]
    exact h
  simp [h_safe]
```

**Examples**: SafeCounter.safeIncrement_succeeds_below_max

### Pattern 4: Structural Induction

For proofs about repeated operations:

```lean
-- 1. Extract recursive function
private def applyN : Nat → State → State
  | 0, s => s
  | k+1, s => applyN k (f s)

-- 2. Prove property by induction
theorem property : ∀ n, P (applyN n s)
  | 0 => base_case
  | k+1 => by
      simp [applyN]
      -- Use IH: property k
      inductive_step
```

**Example**: Counter.multiple_increments

### Pattern 5: Authorization and Access Control

For functions with ownership checks:

```lean
theorem authorized_operation (state : ContractState) (sender : Address)
    (h : state.storageAddr ownerSlot = sender) :
    let result := operation.run { state with sender := sender }
    result.isSuccess = true := by
  unfold operation onlyOwner
  simp [h, msgSender, require]
```

**Example**: Owned.transferOwnership_correct_as_owner

## Common Tactics

### omega
Linear arithmetic solver for natural numbers and integers:
```lean
have h : a + b ≥ b := by omega
have h : a < MAX → a + 1 ≤ MAX := by omega
```

### simp
Automatic simplification using simp lemmas:
```lean
simp [getStorage, Contract.runValue]
simp only [Option.bind, List.lookup]
```

### unfold
Unfold definitions to see structure:
```lean
unfold Contract.run Contract.runState
unfold interpretSpec execFunction
```

### split / cases
Case analysis on conditions or datatypes:
```lean
cases h : safeAdd a b
case none => -- handle None case
case some val => -- handle Some val case
```

### by_cases
Split proof on Boolean condition:
```lean
by_cases h : a ≥ b
case pos => -- proof when h is true
case neg => -- proof when h is false
```

## Testing and Validation

### Build Commands

```bash
# Build specific contract proofs
lake build DumbContracts.Specs.SimpleStorage.Proofs
lake build DumbContracts.Specs.Counter.Proofs
lake build DumbContracts.Specs.SafeCounter.Proofs
lake build DumbContracts.Specs.Owned.Proofs
lake build DumbContracts.Specs.OwnedCounter.Proofs
lake build DumbContracts.Specs.Ledger.Proofs
lake build DumbContracts.Specs.SimpleToken.Proofs

# Build infrastructure
lake build DumbContracts.Proofs.Stdlib.Automation
lake build DumbContracts.Proofs.Stdlib.SpecInterpreter

# Build everything
lake build
```

### Expected Warnings

None.

## Documentation

- Progress tracking lives in `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`.
- **[SpecInterpreter.lean](../../DumbContracts/Proofs/Stdlib/SpecInterpreter.lean)** - Spec execution semantics implementation
- **[Automation.lean](../../DumbContracts/Proofs/Stdlib/Automation.lean)** - Proof helper lemmas and automation

## Contributing

### Adding New Proofs

1. **Start with theorem statement** - Get types right
2. **Unfold definitions** - See the structure
3. **Use automation lemmas** - Import Automation module
4. **Keep proofs small** - Introduce helper lemmas when needed
5. **Test incrementally** - Build after each change

### Code Style

- Use descriptive variable names: `h_success`, `h_overflow`, `h_ge`
- Add comments for non-obvious steps
- Group related lemmas together
- Use `@[simp]` for automatic simplification lemmas
- Keep proofs under 20 lines when possible

### Common Pitfalls

❌ **Don't**: Use `simp` without restrictions when goal is complex
✅ **Do**: Use `simp only [specific, lemmas]` or `simp [h]`

❌ **Don't**: Unfold everything at once
✅ **Do**: Unfold incrementally to maintain clarity

❌ **Don't**: Force omega on non-linear arithmetic
✅ **Do**: Add intermediate `have` statements to help omega

## Resources

- [Lean 4 Documentation](https://lean-lang.org/documentation/)
- [Lean 4 Theorem Proving](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib Tactics](https://leanprover-community.github.io/mathlib4_docs/tactics.html)
- [DumbContracts Core](../DumbContracts/Core.lean)
- Roadmap and progress updates: `docs-site/content/research.mdx` and `docs-site/content/research/iterations.mdx`
