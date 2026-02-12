# Layer 2: ContractSpec → IR Code Generation Verification

**Status**: 🚀 **PHASE 2 FRAMEWORK COMPLETE** - Proofs underway
**Last Updated**: 2026-02-12
**Completion**: Infrastructure 100%, Phase 2 Framework 100%, Proofs ~20% (SimpleStorage + Counter)

## Overview

Layer 2 proves that compiling ContractSpec to IR preserves semantics:

```lean
interpretIR (compile spec) ≈ interpretSpec spec
```

This layer bridges the gap between high-level declarative specifications and executable IR code.

## Completed Work ✅

### Phase 1: Type Conversion Infrastructure (195 lines) ✅

**File**: `Compiler/Proofs/IRGeneration/Conversions.lean`

**Components**:
- `addressToNat` + address table (`addressFromNat`): Address ↔ Nat conversion
- `uint256ToNat` / `natToUint256`: Uint256 ↔ Nat conversion
- `contractStateToIRState`: Convert ContractState → IRState
- `transactionToIRTransaction`: Convert Transaction → IRTransaction
- `resultsMatch`: Define IR ≡ Spec result equivalence (mapping scoped to address list)
- `addressToNat_injective`: Axiom for address encoding uniqueness

**Build Status**: ✅ Compiles with zero errors/warnings

---

### Phase 2: Expression Compilation Framework (172 lines) ✅

**File**: `Compiler/Proofs/IRGeneration/Expr.lean`

**Strategic Decision**: End-to-end contract proofs instead of compositional expression proofs

**Rationale**:
- `compileExpr` is private, inaccessible from external modules
- Public `compile` API is the proper interface for verification
- End-to-end proofs validate the full pipeline
- More maintainable (doesn't depend on internal implementation)

**Components**:
- Proven SimpleStorage preservation theorems:
  - `simpleStorage_store_correct`: Store function correctness
  - `simpleStorage_retrieve_correct`: Retrieve function correctness
- Proven Counter preservation theorems:
  - `counter_increment_correct`: Increment correctness
  - `counter_decrement_correct`: Decrement correctness
  - `counter_getCount_correct`: Getter correctness
- General preservation theorem template
- Detailed 4-step proof strategy documentation

**Build Status**: ✅ Compiles with zero errors/warnings

**Next**: Generalize proof pattern to SafeCounter

---

### Infrastructure: IR Interpreter (192 lines) ✅

**File**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean`

**Components**:
- `IRState`: Execution state
  - Variable bindings (name → value)
  - Storage slots (slot → value)
  - Storage mappings (baseSlot → key → value)
  - Return value, sender address

- `evalIRExpr`: Yul expression evaluation
  - Literals, identifiers, function calls
  - EVM operations: add, sub, mul, div, mod, lt, gt, eq
  - Storage operations: sload, caller
  - Modular arithmetic (mod 2^256)

- `execIRStmt` / `execIRStmts`: Statement execution (mutual recursion)
  - Variable declaration/assignment (let_, assign)
  - Storage writes (sstore via expr)
  - Control flow (if_, switch, block)
  - Returns and reverts

- `interpretIR`: Top-level contract interpreter
  - Function dispatch by selector
  - Parameter initialization
  - Result packaging (success, returnValue, storage)

**Key Design Decisions**:
1. **IR = Yul**: Uses Yul AST directly (IRExpr = YulExpr, IRStmt = YulStmt)
2. **Simple State**: Only Nat everywhere (no type distinctions)
3. **Operational Semantics**: Variables, assignment, explicit sstore
4. **No Monadic Nesting**: Unlike SpecInterpreter, much simpler control flow

### Exploration: SimpleStorage IR Structure

**File**: `Compiler/Proofs/IRGeneration/SimpleStorageProof.lean` (exploration)

**Purpose**: Explore compiled IR and test proof approaches

**Key Findings**:
- Successfully inspected compiled IR using `#eval compile simpleStorageSpec [...]`
- Identified clean Yul structure: store uses sstore, retrieve uses sload/mstore/return
- Created basic theorem templates for testing
- Informed decision to keep axioms in Expr.lean vs. attempting full proofs immediately

This exploration validates that the compiled IR is straightforward and amenable to verification.

## The Type Alignment Challenge

**The Central Problem**: SpecInterpreter and IRInterpreter use different type universes.

### Spec Side (Rich Types)
```lean
ContractState:
  storage : Nat → Uint256
  storageAddr : Nat → Address
  sender : Address  (where Address = String)

Transaction:
  sender : Address
  functionName : String
  args : List Nat

Result:
  success : Bool
  returnValue : Option Nat
  finalStorage : SpecStorage  (with typed slots/mappings)
```

### IR Side (Uniform Nat)
```lean
IRState:
  vars : List (String × Nat)
  storage : Nat → Nat
  sender : Nat

IRTransaction:
  sender : Nat
  functionSelector : Nat
  args : List Nat

IRResult:
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
```

### Required Conversions

To prove `interpretIR (compile spec) ≈ interpretSpec spec`, we need:

1. **Address Encoding**: `Address → Nat` and `Nat → Address`
   ```lean
   def addressToNat : Address → Nat
   def addressFromNat (addrs : List Address) : Nat → Option Address
   -- Prove: addressFromNat addrs (addressToNat a) = some a (for a ∈ addrs)
   ```

2. **Uint256 Conversion**: `Uint256 ↔ Nat`
   ```lean
   def uint256ToNat (u : Uint256) : Nat := u.val
   def natToUint256 (n : Nat) : Uint256 := n % (2^256)
   ```

3. **State Conversion**: `ContractState → IRState`
   ```lean
   def stateToIRState (s : ContractState) : IRState :=
     { vars := []
       storage := fun slot => (s.storage slot).val
       mappings := fun base key =>
         match addressFromNat addrs key with
         | some addr => (s.storageMap base addr).val
         | none => 0
       sender := addressToNat s.sender }
   ```

4. **Transaction Conversion**: `Transaction → IRTransaction`
   ```lean
   def txToIRTx (tx : Transaction) (selector : Nat) : IRTransaction :=
     { sender := addressToNat tx.sender
       functionSelector := selector
       args := tx.args }
   ```

5. **Result Equivalence**: Define when `IRResult ≈ SpecInterpreter.Result`
   ```lean
   def resultsMatch (addrs : List Address) (ir : IRResult) (spec : SpecInterpreter.Result) : Prop :=
     ir.success = spec.success ∧
     ir.returnValue = spec.returnValue ∧
     (∀ slot, ir.finalStorage slot = spec.finalStorage.getSlot slot)
   ```

## Proof Strategy

With conversion infrastructure in place, the preservation theorem becomes:

```lean
theorem compile_preserves_semantics (spec : ContractSpec) (selectors : List Nat)
    (tx : Transaction) (state : ContractState) :
    let compiled := compile spec selectors
    let irResult := interpretIR compiled (txToIRTx tx selector)
    let specResult := interpretSpec spec (stateToSpecStorage state) tx
    resultsMatch addrs irResult specResult := by
  -- Proof by structural induction on spec and tx
  sorry
```

### Why This is Promising

Compared to Layer 1 (EDSL ↔ Spec), Layer 2 has advantages:

1. **Deterministic Compilation**: `compile` is a pure, structural function
   - No execution semantics to align
   - Just syntax-directed translation
   - Much easier to reason about than interpreter equivalence

2. **Simpler IR Semantics**:
   - No monadic nesting (flat variable environment)
   - No complex pattern matching on ContractResult
   - Direct assignment and sstore instead of bind chains

3. **Clear Separation of Concerns**:
   - Compilation: ContractSpec → IR (pure syntax transformation)
   - Execution: IR → Result (interpreter semantics)
   - Layer 1 conflates these (Spec ≡ EDSL execution)

4. **Potential Automation Reuse**:
   - If we build IR simplification tactics
   - They might be simpler than Spec simplification
   - Could inform how to complete Layer 1

## Next Steps

### Phase 3: Actual Proofs (1-2 weeks)

Now that the framework is complete, prove the axiomatized theorems:

1. **Prove SimpleStorage theorems** (~50 lines) ✅
   - Convert `simpleStorage_store_correct` from axiom to theorem
   - Convert `simpleStorage_retrieve_correct` from axiom to theorem
   - Both theorems are in `Compiler/Proofs/IRGeneration/Expr.lean`
   - Strategy: Unfold compile, interpretIR, interpretSpec, show equivalence

2. **Generalize to Counter** (~100 lines) ✅
   - Prove increment/decrement/getCount preservation
   - Handle arithmetic operations (add, sub)
   - Use same end-to-end pattern

3. **Extend to SafeCounter** (~100 lines) ⏳ Next
   - Prove safe arithmetic with overflow checks
   - Handle Option returns (Some/None cases)

4. **Complete remaining contracts** (~350 lines)
   - Owned (authorization)
   - OwnedCounter (composition)
   - Ledger (mappings)
   - SimpleToken (full complexity)

### Phase 4: Complete All 7 Contracts (after SimpleStorage + Counter proven)

Once SimpleStorage is proven, apply the same pattern to:
- Counter (arithmetic)
- SafeCounter (overflow checks)
- Owned (authorization)
- OwnedCounter (composition)
- Ledger (mappings)
- SimpleToken (full complexity)

## Estimated Effort

| Phase | Component | Lines | Time | Status |
|-------|-----------|-------|------|--------|
| 1 | Type Conversions | 195 | 1-2 days | ✅ **COMPLETE** |
| 2 | Proof Framework | 172 | 1-2 days | ✅ **COMPLETE** |
| 3 | SimpleStorage proofs | 50 | 2-3 days | ✅ **COMPLETE** |
| 3 | Counter proofs | 100 | 3-4 days | ✅ **COMPLETE** |
| 3 | SafeCounter proofs | 100 | 3-4 days | Pending |
| 4 | Owned proofs | 100 | 3-4 days | Pending |
| 4 | OwnedCounter proofs | 100 | 3-4 days | Pending |
| 4 | Ledger proofs | 100 | 4-5 days | Pending |
| 4 | SimpleToken proofs | 150 | 4-5 days | Pending |
| | **Infrastructure Total** | **367** | **2-4 days** | ✅ **COMPLETE** |
| | **Proof Total** | **700** | **3-4 weeks** | **~21%** |
| | **Layer 2 Total** | **~1067** | **3-5 weeks** | **~48% (Infrastructure + SimpleStorage + Counter)** |

**Progress**: Infrastructure and framework are done. SafeCounter proofs are next.

## Strategic Value

Layer 2 provides strategic benefits beyond just completing verification:

1. **De-risk Layer 1**: If IR proves easier to reason about, informs Layer 1 completion
2. **Incremental Progress**: Can complete Layer 2 while Layer 1 automation develops
3. **Different Proof Patterns**: May discover techniques applicable to Layer 1
4. **Validation of Approach**: If Layer 2 succeeds, validates overall architecture

## Open Questions

1. **Should we complete Layer 2 before finishing Layer 1?**
   - Pro: Might reveal simpler proof patterns
   - Con: Doubles work if Layer 1 patterns transfer directly
   - **Recommendation**: Complete conversions + SimpleStorage proof, then reassess

2. **Can IR automation help Layer 1?**
   - If IR simplification tactics are simpler
   - They might inform Spec interpreter automation
   - Worth exploring after Phase 1

3. **Type conversion soundness**
   - Need to ensure `addressToNat` is injective
   - May need additional constraints on Address type
   - Should investigate early in Phase 1

## Conclusion

Layer 2 infrastructure is **production-ready**. The IR interpreter is simpler and more tractable than the Spec interpreter. The type alignment challenge is well-understood and solvable.

**Recommendation**: Proceed with Phase 1 (Conversions) to validate the approach, then complete SimpleStorage proof as a proof-of-concept before scaling to all contracts.

This provides a concrete, achievable path to meaningful verification progress while Layer 1 automation questions are resolved.
