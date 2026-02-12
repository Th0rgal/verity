# Compiler Verification Proofs

This directory contains formal verification proofs for the DumbContracts compiler, proving correctness across three layers of compilation.

## Three-Layer Verification Strategy

### Layer 1: EDSL ≡ ContractSpec (Specification Correctness) ✅ 100% Complete

**Goal**: Prove that manually written ContractSpec specifications accurately represent the verified EDSL contracts.

**Status**: 27/27 theorems proven across 7 contracts

#### Completed Contracts

##### SimpleStorage (100% ✅)
- 4/4 theorems proven
- Demonstrates basic storage operations
- Pattern: unfold + simp for direct computation
- **Proofs**: [SpecCorrectness/SimpleStorage.lean](SpecCorrectness/SimpleStorage.lean)

##### Counter (100% ✅)
- 7/7 theorems proven
- Includes modular arithmetic with wraparound
- Features structural induction proof for multiple increments
- **Proofs**: [SpecCorrectness/Counter.lean](SpecCorrectness/Counter.lean)

##### SafeCounter (100% ✅)
- 8/8 theorems proven
- Demonstrates overflow/underflow protection with safe arithmetic
- **Proofs**: [SpecCorrectness/SafeCounter.lean](SpecCorrectness/SafeCounter.lean)

##### Owned (100% ✅)
- 8/8 theorems proven
- Demonstrates ownership and access control patterns
- **Proofs**: [SpecCorrectness/Owned.lean](SpecCorrectness/Owned.lean)

##### OwnedCounter (100% ✅)
- 4/4 theorems proven
- Combines ownership checks with counter semantics
- **Proofs**: [SpecCorrectness/OwnedCounter.lean](SpecCorrectness/OwnedCounter.lean)

##### Ledger (100% ✅)
- 2/2 theorems proven
- Mapping-based balance operations
- **Proofs**: [SpecCorrectness/Ledger.lean](SpecCorrectness/Ledger.lean)

##### SimpleToken (100% ✅)
- 2/2 theorems proven
- Token minting and transfers with balances mapping
- **Proofs**: [SpecCorrectness/SimpleToken.lean](SpecCorrectness/SimpleToken.lean)

## Quick Start

```bash
# Build all Layer 1 proofs
lake build Compiler.Proofs.SpecCorrectness.SimpleStorage
lake build Compiler.Proofs.SpecCorrectness.Counter
lake build Compiler.Proofs.SpecCorrectness.SafeCounter
lake build Compiler.Proofs.SpecCorrectness.Owned

# Build infrastructure
lake build Compiler.Proofs.Automation
lake build Compiler.Proofs.SpecInterpreter
```

**Current Status**: ✅ All files compile successfully

## Infrastructure Components

### SpecInterpreter ([SpecInterpreter.lean](SpecInterpreter.lean))

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

### Automation Library ([Automation.lean](Automation.lean))

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
lake build Compiler.Proofs.SpecCorrectness.SimpleStorage
lake build Compiler.Proofs.SpecCorrectness.Counter
lake build Compiler.Proofs.SpecCorrectness.SafeCounter
lake build Compiler.Proofs.SpecCorrectness.Owned

# Build infrastructure
lake build Compiler.Proofs.Automation
lake build Compiler.Proofs.SpecInterpreter

# Build everything
lake build
```

### Expected Warnings

None. All Layer 1 proofs compile with zero placeholders.

## Metrics

| Metric | Value |
|--------|-------|
| Layer 1 Progress | 100% (27/27) |
| Total Lines | ~1,900 |
| Proven Theorems | 27 |
| Automation Lemmas | 20+ |
| Build Status | ✅ Success |
| Strategic Sorries | 0 |

## Documentation

- **[LAYER1_STATUS.md](LAYER1_STATUS.md)** - Detailed progress tracking with contract-by-contract breakdown
- **[SpecInterpreter.lean](SpecInterpreter.lean)** - Spec execution semantics implementation
- **[Automation.lean](Automation.lean)** - Proof helper lemmas and automation

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

## Future Layers

### Layer 2: ContractSpec → IR ✅ Complete
- IR interpreter implementation
- End-to-end preservation theorems for 7 contracts
- Conversions and result equivalence formalized

### Layer 3: IR → Yul (In Progress)
- ✅ Yul runtime semantics with selector-aware calldata
- ✅ Mapping slot model shared with IR semantics
- ⏳ Codegen correctness proofs for `emitYul`
- ⏳ Preservation theorem: `emitYul` preserves semantics

### Layer 4: Trust Assumptions
- Documented: solc compiles Yul → EVM correctly
- Validated: 70,000+ differential tests
- Trusted: Lean 4 kernel, EVM implementations

---

**Status**: Layer 1 Complete, Layer 2 Complete, Layer 3 In Progress | **Last Updated**: 2026-02-12 | **Maintainer**: Verification Team
