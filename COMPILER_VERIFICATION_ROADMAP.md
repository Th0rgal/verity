# Compiler Verification Roadmap

**Goal**: Prove that compiled EVM bytecode matches verified EDSL semantics

**Current Status**:
- ✅ 252 EDSL correctness proofs (the contracts work correctly)
- ✅ 70,000+ differential tests (bytecode ≈ EDSL empirically)
- ❌ **NO formal proof connecting EDSL → ContractSpec → IR → Yul → Bytecode**

---

## The Problem: Two Gaps in Our Trust Chain

```
┌─────────────────────────────────────────────────────────────────┐
│                    CURRENT STATE                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  EDSL Contract (SimpleStorage.lean)                             │
│  ✅ 252 proofs: "store then retrieve = identity"                │
│                                                                  │
│           ⬇ ❌ GAP 1: Manual translation, not proven!           │
│                                                                  │
│  ContractSpec (simpleStorageSpec in Specs.lean)                 │
│  Declarative DSL: Stmt.setStorage, Expr.param, etc.             │
│                                                                  │
│           ⬇ ❌ GAP 2: Automatic but not proven!                 │
│                                                                  │
│  IR → Yul → Bytecode                                            │
│  Generated code (compiles and runs)                             │
│                                                                  │
│  ✅ 70k+ tests: Bytecode ≈ EDSL (empirical validation)          │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**What we need to prove:**

1. **Gap 1**: `simpleStorageSpec` accurately represents `SimpleStorage` EDSL
2. **Gap 2**: Compiler transformations preserve semantics (Spec → IR → Yul)

---

## Three-Layer Verification Strategy

### Layer 1: EDSL ≡ ContractSpec (Spec Correctness)
**Prove**: Manually written specs match EDSL semantics

### Layer 2: ContractSpec → IR (Code Generation)
**Prove**: IR generation preserves spec semantics

### Layer 3: IR → Yul (Lowering)
**Prove**: Yul codegen preserves IR semantics

### Layer 4: Yul → Bytecode (Trust Assumption)
**Accept**: We trust `solc` (validated by 70k+ differential tests)

---

## Layer 1: Prove ContractSpec ≡ EDSL

### The Challenge

We manually wrote 7 specs in `Compiler/Specs.lean`:

```lean
-- In Compiler/Specs.lean (line ~60)
def simpleStorageSpec : ContractSpec := {
  name := "SimpleStorage"
  fields := [
    { name := "value", ty := FieldType.uint256 }
  ]
  functions := [
    { name := "store"
      params := [{ name := "newValue", ty := ParamType.uint256 }]
      body := [
        Stmt.setStorage "value" (Expr.param "newValue"),
        Stmt.stop
      ]
    },
    { name := "retrieve"
      params := []
      returnType := some FieldType.uint256
      body := [
        Stmt.return (Expr.storage "value")
      ]
    }
  ]
}
```

**Question**: Does this match the EDSL in `DumbContracts/Examples/SimpleStorage.lean`?

```lean
-- In DumbContracts/Examples/SimpleStorage.lean
def store (state : State) (newValue : Uint256) : State :=
  { state with stored := newValue }

def retrieve (state : State) : Option Uint256 :=
  some state.stored
```

**We assume yes, but haven't proven it!**

### What to Build

#### Step 1: ContractSpec Interpreter

Create `Compiler/Proofs/SpecInterpreter.lean`:

```lean
import Compiler.ContractSpec
import DumbContracts.Core

namespace Compiler.Proofs

/-!
## ContractSpec Semantics

Define what it *means* to execute a ContractSpec.
This is the reference semantics for our declarative DSL.
-/

-- Evaluation context
structure EvalContext where
  state : State
  sender : Address
  msgValue : Uint256
  blockTimestamp : Nat
  params : List Nat
  localVars : List (String × Nat)  -- Local variables from letVar

-- Evaluate expressions
def evalExpr (ctx : EvalContext) (fields : List Field) (e : Expr) : Nat :=
  match e with
  | Expr.literal n => n
  | Expr.param name =>
      -- Look up parameter by name in function definition
      -- Return param value from ctx.params
      sorry
  | Expr.storage fieldName =>
      -- Look up field slot by name
      -- Read from ctx.state at that slot
      sorry
  | Expr.mapping fieldName key =>
      -- Compute keccak256(key, slot)
      -- Read from ctx.state
      sorry
  | Expr.caller => ctx.sender.toNat
  | Expr.msgValue => ctx.msgValue.val
  | Expr.add a b => evalExpr ctx fields a + evalExpr ctx fields b
  | Expr.sub a b =>
      let va := evalExpr ctx fields a
      let vb := evalExpr ctx fields b
      (va - vb) % (2^256)  -- Modular arithmetic
  | Expr.localVar name =>
      -- Look up in ctx.localVars
      sorry
  -- ... other cases

-- Execute statements
def execStmt (ctx : EvalContext) (fields : List Field) (s : Stmt) :
    Option (State × List (String × Nat)) :=
  match s with
  | Stmt.setStorage fieldName expr =>
      let val := evalExpr ctx fields expr
      -- Find field slot, update state
      some (updatedState, ctx.localVars)
  | Stmt.setMapping fieldName key value =>
      -- Compute mapping slot, update state
      sorry
  | Stmt.require cond msg =>
      let result := evalExpr ctx fields cond
      if result == 0 then none  -- Revert
      else some (ctx.state, ctx.localVars)
  | Stmt.letVar name expr =>
      let val := evalExpr ctx fields expr
      some (ctx.state, (name, val) :: ctx.localVars)
  | Stmt.return _ => some (ctx.state, ctx.localVars)
  | Stmt.stop => some (ctx.state, ctx.localVars)

-- Execute function body
def execFunction (spec : ContractSpec) (fname : String)
    (state : State) (sender : Address) (args : List Nat) :
    Option State :=
  -- Find function in spec
  -- Execute statements sequentially
  -- Return final state or none (if reverted)
  sorry

-- Top-level interpreter
def interpretSpec (spec : ContractSpec) (state : State) (tx : Transaction) :
    ExecutionResult :=
  match execFunction spec tx.functionName state tx.sender tx.args with
  | none =>
      { success := false
        returnValue := none
        revertReason := some "execution reverted"
        storageChanges := []
        storageAddrChanges := []
        mappingChanges := [] }
  | some newState =>
      { success := true
        returnValue := none  -- TODO: handle return values
        revertReason := none
        storageChanges := computeChanges state newState
        storageAddrChanges := []
        mappingChanges := [] }

end Compiler.Proofs
```

**Estimated effort**: 200-300 lines, 2-3 days

#### Step 2: Prove Spec Correctness (7 theorems)

For each contract, prove the spec matches the EDSL.

**Example**: `Compiler/Proofs/SpecCorrectness/SimpleStorage.lean`

```lean
import Compiler.Specs
import Compiler.Proofs.SpecInterpreter
import DumbContracts.Examples.SimpleStorage
import DumbContracts.Proofs.SimpleStorage.Correctness

namespace Compiler.Proofs.SpecCorrectness

open Compiler.ContractSpec
open DumbContracts.Examples

/-!
## SimpleStorage Spec Correctness

Prove that `simpleStorageSpec` accurately represents the `SimpleStorage` EDSL.
-/

-- Helper: Convert EDSL state to Spec state
def edslStateToSpecState (s : SimpleStorage.SimpleStorageState) : State :=
  State.empty.setSlot 0 s.stored.val

-- Helper: Convert Spec state to EDSL state
def specStateToEdslState (s : State) : SimpleStorage.SimpleStorageState :=
  { stored := Uint256.ofNat (s.getSlot 0) }

-- Main theorem: spec matches EDSL for 'store' function
theorem store_spec_correct (state : SimpleStorage.SimpleStorageState)
    (sender : Address) (newValue : Uint256) :
    let edslResult := SimpleStorage.store state newValue
    let specState := edslStateToSpecState state
    let specResult := interpretSpec simpleStorageSpec specState
      { functionName := "store", sender := sender, args := [newValue.val] }
    specStateToEdslState (extractState specResult) = edslResult := by
  -- Proof:
  -- 1. Unfold interpretSpec
  -- 2. Show it finds "store" function
  -- 3. Show it executes Stmt.setStorage "value" (Expr.param "newValue")
  -- 4. Show this updates slot 0 to newValue
  -- 5. Show this equals SimpleStorage.store
  simp [interpretSpec, execFunction, execStmt, evalExpr]
  simp [SimpleStorage.store]
  rfl

-- Main theorem: spec matches EDSL for 'retrieve' function
theorem retrieve_spec_correct (state : SimpleStorage.SimpleStorageState)
    (sender : Address) :
    let edslResult := SimpleStorage.retrieve state
    let specState := edslStateToSpecState state
    let specResult := interpretSpec simpleStorageSpec specState
      { functionName := "retrieve", sender := sender, args := [] }
    extractReturnValue specResult = edslResult := by
  -- Similar proof
  sorry

-- Combine into main correctness theorem
theorem simpleStorageSpec_correct :
    ∀ (state : SimpleStorage.SimpleStorageState) (tx : Transaction),
      interpretEDSL SimpleStorage state tx =
      interpretSpec simpleStorageSpec (edslStateToSpecState state) tx := by
  intro state tx
  cases tx.functionName
  case store => apply store_spec_correct
  case retrieve => apply retrieve_spec_correct

end Compiler.Proofs.SpecCorrectness
```

**Estimated effort per contract**:
- SimpleStorage: 100 lines, 1-2 days (template for others)
- Counter: 150 lines, 2 days
- Owned: 150 lines, 2 days
- SafeCounter: 200 lines, 2-3 days
- OwnedCounter: 200 lines, 2-3 days
- Ledger: 250 lines, 3-4 days
- SimpleToken: 300 lines, 3-4 days

**Total Layer 1**: ~1350 lines, 3-4 weeks

### Challenges & Solutions

**Challenge 1**: State representation mismatch
- EDSL: `{ stored : Uint256 }`
- Spec: `State` (generic slot storage)

**Solution**: Write bidirectional conversion functions + prove they're inverses

**Challenge 2**: Function dispatch
- EDSL: Direct function calls
- Spec: String-based lookup

**Solution**: Case split on function name, prove each matches

**Challenge 3**: Constructor parameters
- Some contracts (Owned, SimpleToken) have constructor args
- Need to prove bytecode arg loading matches EDSL initialization

**Solution**: Model constructor execution separately

---

## Layer 2: Prove ContractSpec → IR Preserves Semantics

### The Challenge

Code in `Compiler/ContractSpec.lean` automatically generates IR:

```lean
-- In ContractSpec.lean, line ~140
def Function.toIR (f : Function) (fields : List Field)
    (selectors : List Nat) : IRFunction :=
  -- Find function selector
  -- Generate parameter loading code
  -- Compile body statements to IR
  -- ...
```

**Question**: Does this IR generation preserve the spec's semantics?

### What to Build

#### Step 1: IR Semantics

Create `Compiler/Proofs/IRSemantics.lean`:

```lean
import Compiler.IR
import DumbContracts.Core

namespace Compiler.Proofs

/-!
## IR Semantics

Define what it means to execute IR code.
-/

-- IR evaluation context
structure IRContext where
  stack : List Nat
  memory : List Nat
  storage : State
  -- ...

def evalIRExpr (ctx : IRContext) (e : IRExpr) : Nat :=
  match e with
  | IRExpr.lit n => n
  | IRExpr.sload slot => ctx.storage.getSlot slot
  | IRExpr.add a b => evalIRExpr ctx a + evalIRExpr ctx b
  -- ...

def execIRStmt (ctx : IRContext) (s : IRStmt) : Option IRContext :=
  match s with
  | IRStmt.sstore slot val =>
      let v := evalIRExpr ctx val
      some { ctx with storage := ctx.storage.setSlot slot v }
  -- ...

def interpretIR (ir : IRContract) (state : State) (tx : Transaction) :
    ExecutionResult :=
  -- Find function by selector
  -- Execute IR statements
  -- Return result
  sorry

end Compiler.Proofs
```

**Estimated effort**: 250-350 lines, 2-3 days

#### Step 2: Prove IR Generation Correctness

Create `Compiler/Proofs/IRGeneration/`:

**a) Expression translation** (`Expr.lean`):
```lean
theorem exprToIR_correct (e : Expr) (fields : List Field)
    (specCtx : EvalContext) (irCtx : IRContext) :
    -- If contexts are equivalent
    contextsEquiv specCtx irCtx →
    -- Then evaluation gives same result
    evalIRExpr irCtx (compileExpr fields e) =
    evalExpr specCtx fields e := by
  induction e <;> simp [compileExpr, evalExpr, evalIRExpr]
  -- Case analysis on expression type
  sorry
```

**b) Statement translation** (`Stmt.lean`):
```lean
theorem stmtToIR_correct (s : Stmt) (fields : List Field)
    (specCtx : EvalContext) (irCtx : IRContext) :
    contextsEquiv specCtx irCtx →
    -- Executing IR gives same state as executing spec
    execIRStmt irCtx (compileStmt fields s) =
    liftToIR (execStmt specCtx fields s) := by
  cases s <;> simp [compileStmt, execStmt, execIRStmt]
  sorry
```

**c) Function translation** (`Function.lean`):
```lean
theorem functionToIR_correct (f : Function) (spec : ContractSpec) :
    -- IR function semantics match spec function semantics
    interpretIRFunction (f.toIR spec.fields selectors) =
    execFunction spec f.name := by
  sorry
```

**d) Full preservation** (`Preservation.lean`):
```lean
theorem toIR_preserves_semantics (spec : ContractSpec) :
    ∀ (state : State) (tx : Transaction),
      interpretIR (specToIR spec) state tx =
      interpretSpec spec state tx := by
  intro state tx
  -- Compose expression, statement, function correctness
  apply functionToIR_correct
  apply stmtToIR_correct
  apply exprToIR_correct
```

**Estimated effort**:
- Expr.lean: 200 lines, 2-3 days
- Stmt.lean: 250 lines, 3-4 days
- Function.lean: 150 lines, 2 days
- Preservation.lean: 100 lines, 1-2 days

**Total Layer 2**: ~700 lines, 2-3 weeks

---

## Layer 3: Prove IR → Yul Preserves Semantics

### The Challenge

Code in `Compiler/Codegen.lean` generates Yul from IR:

```lean
-- In Codegen.lean
def codegenExpr (e : IRExpr) : YulExpr :=
  match e with
  | IRExpr.lit n => YulExpr.lit n
  | IRExpr.sload slot => YulExpr.call "sload" [YulExpr.lit slot]
  -- ...
```

**Question**: Does Yul codegen preserve IR semantics?

### The Problem: Yul Semantics

Yul is a low-level language close to EVM. We need to either:

**Option A**: Define simplified Yul semantics ourselves
**Option B**: Import existing formal Yul semantics (if available)

### What to Build

#### Step 1: Yul Semantics (or Import)

Create `Compiler/Proofs/YulSemantics.lean`:

```lean
import Compiler.Yul.Ast

namespace Compiler.Proofs

/-!
## Yul Semantics

Simplified formal semantics for the Yul subset we generate.
-/

structure YulState where
  stack : List Nat
  memory : List Nat
  storage : State
  -- Simplified: ignore calldata, returndata details

-- Evaluate Yul expressions
def evalYulExpr (s : YulState) (e : YulExpr) : Nat :=
  match e with
  | YulExpr.lit n => n
  | YulExpr.ident x =>
      -- Look up variable (in simplified model)
      sorry
  | YulExpr.call "sload" [slot] =>
      let slotNum := evalYulExpr s slot
      s.storage.getSlot slotNum
  | YulExpr.call "add" [a, b] =>
      evalYulExpr s a + evalYulExpr s b
  -- ... other opcodes

-- Execute Yul statements
def execYulStmt (s : YulState) (stmt : YulStmt) : Option YulState :=
  match stmt with
  | YulStmt.let_ x e =>
      -- Bind variable
      sorry
  | YulStmt.assign x e =>
      -- Update variable
      sorry
  | YulStmt.expr (YulExpr.call "sstore" [slot, val]) =>
      let slotNum := evalYulExpr s slot
      let value := evalYulExpr s val
      some { s with storage := s.storage.setSlot slotNum value }
  -- ...

def interpretYul (yul : YulCode) (state : State) (tx : Transaction) :
    ExecutionResult :=
  -- Execute Yul function dispatch
  -- Run function body
  -- Extract result
  sorry

end Compiler.Proofs
```

**Estimated effort**: 400-600 lines, 4-6 days

**Alternative**: If we find existing formal Yul semantics, import instead (~1 day)

#### Step 2: Prove Yul Codegen Correctness

Create `Compiler/Proofs/YulGeneration/`:

**a) Expression codegen** (`Expr.lean`):
```lean
theorem exprCodegen_correct (e : IRExpr)
    (irCtx : IRContext) (yulState : YulState) :
    statesEquiv irCtx yulState →
    evalYulExpr yulState (codegenExpr e) =
    evalIRExpr irCtx e := by
  induction e <;> simp [codegenExpr, evalYulExpr, evalIRExpr]
  sorry
```

**b) Statement codegen** (`Stmt.lean`):
```lean
theorem stmtCodegen_correct (s : IRStmt)
    (irCtx : IRContext) (yulState : YulState) :
    statesEquiv irCtx yulState →
    execYulStmt yulState (codegenStmt s) =
    liftToYul (execIRStmt irCtx s) := by
  cases s <;> simp [codegenStmt, execYulStmt, execIRStmt]
  sorry
```

**c) Full preservation** (`Preservation.lean`):
```lean
theorem yulCodegen_preserves_semantics (ir : IRContract) :
    ∀ (state : State) (tx : Transaction),
      interpretYul (generateYul ir) state tx =
      interpretIR ir state tx := by
  intro state tx
  apply stmtCodegen_correct
  apply exprCodegen_correct
```

**Estimated effort**:
- Expr.lean: 250 lines, 3 days
- Stmt.lean: 300 lines, 3-4 days
- Preservation.lean: 150 lines, 2 days

**Total Layer 3**: ~1100 lines, 3-4 weeks

---

## Layer 4: Trust solc (Yul → Bytecode)

We **do not verify solc**. Instead:

### Document Trust Assumption

Create `Compiler/Proofs/TrustAssumptions.lean`:

```lean
/-!
## Trust Assumptions

The compiler verification relies on these trusted components:
-/

namespace Compiler.Proofs

-- We assume solc correctly compiles Yul to EVM bytecode
axiom solc_correct :
  ∀ (yul : YulCode) (state : EVMState) (tx : EVMTransaction),
    executeEVM (solc.compile yul) state tx =
    interpretYul yul state tx

-- We trust the Lean 4 kernel
-- (Small TCB: ~10k lines, extensively reviewed)

-- We trust the EVM implementation (geth, etc.)
-- (Consensus-critical, heavily tested)

end Compiler.Proofs
```

### Justify with Differential Testing

**In documentation**:

> While we don't formally verify solc, we have strong empirical evidence:
> - 70,000+ differential tests compare compiled bytecode vs EDSL
> - Zero mismatches found
> - Our generated Yul is simple (no complex features)
> - solc is mature, widely used, heavily tested
>
> This gives high confidence that solc correctly compiles our Yul subset.

**Estimated effort**: 1 day for documentation

---

## End-to-End Theorem

Create `Compiler/Proofs/EndToEnd.lean`:

```lean
import Compiler.Proofs.SpecCorrectness
import Compiler.Proofs.IRGeneration.Preservation
import Compiler.Proofs.YulGeneration.Preservation
import Compiler.Proofs.TrustAssumptions

namespace Compiler.Proofs

/-!
## End-to-End Compiler Correctness

Compose all three layers into one theorem.
-/

-- Full compiler correctness (without solc)
theorem compiler_correct (contract : EDSLContract) (spec : ContractSpec) :
    -- Assuming spec represents contract
    spec_represents contract spec →
    ∀ (state : State) (tx : Transaction),
      -- EDSL execution equals Yul execution
      interpretEDSL contract state tx =
      interpretYul (compile spec) state tx := by
  intro h_spec state tx
  -- Chain of equalities:
  calc interpretEDSL contract state tx
      = interpretSpec spec state tx := by
          apply spec_represents_correct h_spec
    _ = interpretIR (specToIR spec) state tx := by
          apply toIR_preserves_semantics
    _ = interpretYul (generateYul (specToIR spec)) state tx := by
          apply yulCodegen_preserves_semantics

-- With solc assumption: full stack correctness
theorem compiler_correct_with_solc (contract : EDSLContract) (spec : ContractSpec) :
    spec_represents contract spec →
    ∀ (state : State) (tx : Transaction),
      interpretEDSL contract state tx =
      executeEVM (solc.compile (compile spec)) state tx := by
  intro h_spec state tx
  rw [← solc_correct]
  exact compiler_correct contract spec h_spec state tx

end Compiler.Proofs
```

**Estimated effort**: 100 lines, 1 day

---

## Summary: Timeline & Effort

| Phase | Deliverable | Lines of Code | Duration |
|-------|-------------|---------------|----------|
| **Layer 1: Spec Correctness** | | | |
| - SpecInterpreter | Define spec semantics | 200-300 | 2-3 days |
| - SimpleStorage proof | Template proof | 100 | 1-2 days |
| - 6 other contract proofs | Spec correctness | 1250 | 2-3 weeks |
| **Layer 2: IR Generation** | | | |
| - IR Semantics | Define IR semantics | 250-350 | 2-3 days |
| - Expression proofs | `exprToIR_correct` | 200 | 2-3 days |
| - Statement proofs | `stmtToIR_correct` | 250 | 3-4 days |
| - Function proofs | `functionToIR_correct` | 150 | 2 days |
| - Preservation | Full theorem | 100 | 1-2 days |
| **Layer 3: Yul Generation** | | | |
| - Yul Semantics | Define or import | 400-600 | 4-6 days |
| - Expression codegen | `exprCodegen_correct` | 250 | 3 days |
| - Statement codegen | `stmtCodegen_correct` | 300 | 3-4 days |
| - Preservation | Full theorem | 150 | 2 days |
| **Layer 4: Trust** | | | |
| - Documentation | Trust assumptions | 50 | 1 day |
| **End-to-End** | | | |
| - Compose theorems | Final correctness | 100 | 1 day |
| **TOTAL** | | **~4,000 lines** | **8-11 weeks** |

---

## Getting Started: Week 1 Plan

### Day 1-2: Infrastructure Setup
- [ ] Create `Compiler/Proofs/` directory structure
- [ ] Create `Compiler/Proofs/SpecInterpreter.lean` skeleton
- [ ] Define `ExecutionResult` equivalence predicates

### Day 3-4: Spec Interpreter Implementation
- [ ] Implement `evalExpr` for all expression types
- [ ] Implement `execStmt` for all statement types
- [ ] Implement `execFunction` and `interpretSpec`
- [ ] Write unit tests (in comments/examples)

### Day 5-7: First Proof (SimpleStorage)
- [ ] Create `Compiler/Proofs/SpecCorrectness/SimpleStorage.lean`
- [ ] Prove `store_spec_correct`
- [ ] Prove `retrieve_spec_correct`
- [ ] Prove `simpleStorageSpec_correct` (combined)

### Success Criteria (Week 1)
- ✅ `interpretSpec simpleStorageSpec` runs and matches EDSL
- ✅ First spec correctness proof compiles with zero `sorry`
- ✅ Template established for other 6 contracts

---

## Success Metrics

### Layer 1 Complete When:
- ✅ `interpretSpec` implemented (200-300 lines)
- ✅ All 7 spec correctness theorems proven (~1350 lines)
- ✅ `lake build Compiler/Proofs/SpecCorrectness` has zero `sorry`

### Layer 2 Complete When:
- ✅ `interpretIR` implemented (250-350 lines)
- ✅ Expression, statement, function translation proven (~700 lines)
- ✅ `toIR_preserves_semantics` theorem proven
- ✅ `lake build Compiler/Proofs/IRGeneration` has zero `sorry`

### Layer 3 Complete When:
- ✅ Yul semantics defined or imported (400-600 lines)
- ✅ Codegen correctness proven (~700 lines)
- ✅ `yulCodegen_preserves_semantics` theorem proven
- ✅ `lake build Compiler/Proofs/YulGeneration` has zero `sorry`

### Full Verification Complete When:
- ✅ All 3 layers proven
- ✅ End-to-end theorem composed
- ✅ Trust assumptions documented
- ✅ `lake build Compiler/Proofs` has zero `sorry`
- ✅ Verification paper/documentation written

---

## FAQ

**Q: Why not just trust the 70,000+ differential tests?**

A: Differential tests give high *empirical* confidence but not *mathematical certainty*. They can't test all possible inputs, and might miss edge cases. Formal verification proves correctness for *all* inputs.

**Q: Do we really need Layer 1? Can't we skip to proving IR/Yul correct?**

A: No! Layer 1 proves the specs match the verified EDSL. Without it, even if the compiler is perfect, we might be compiling the wrong thing.

**Q: Can we verify solc too?**

A: Technically yes, but it's massive (~500k lines). Instead, we:
1. Trust it (mature, widely tested)
2. Validate with 70k+ differential tests
3. Generate simple Yul (avoids complex features)

**Q: What if we find bugs while proving?**

A: Great! That's the point. We fix them and gain confidence. Formal verification often finds bugs that testing misses.

**Q: How does this compare to other verified compilers?**

A: Similar to CompCert (verified C compiler). We're doing:
1. Spec correctness (unique to our setup)
2. Compilation correctness (standard verified compiler work)
3. Differential testing (extra validation)

This gives defense-in-depth: proofs + extensive testing.

---

## Next Steps

1. **This week**: Set up infrastructure, implement `interpretSpec`, prove SimpleStorage
2. **Weeks 2-4**: Complete Layer 1 (all 7 spec proofs)
3. **Weeks 5-8**: Complete Layer 2 (IR generation proofs)
4. **Weeks 9-12**: Complete Layer 3 (Yul codegen proofs)
5. **Week 13**: Documentation, CI integration, announce verified compiler

**Ready to start?** Begin with Week 1 Day 1 tasks above!
