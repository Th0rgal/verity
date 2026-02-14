# DumbContracts Roadmap to Completion

**Project Health**: 92/100 🎯

**Goal**: Achieve full end-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Executive Summary

DumbContracts has achieved **92% completion** toward production-ready, fully verified smart contracts:

- ✅ **Layer 1 Complete**: 228 properties proven across 7 contracts (EDSL ≡ ContractSpec)
- ✅ **Layer 2 Complete**: All IR generation with preservation proofs (ContractSpec → IR)
- 🔄 **Layer 3 In Progress**: Semantics complete, need statement-level equivalence (IR → Yul)
- ✅ **Property Testing**: 70% coverage (203/292), all testable properties covered
- ✅ **Differential Testing**: Production-ready with 10k+ tests

**Estimated Time to Production-Ready**: 2-3 months of focused work on Layer 3 + trust reduction.

---

## 🎯 Three Critical Work Streams

Here's what stands between current state (92%) and full completion (100%):

### 🔴 **Layer 3 Statement Proofs** (THE Critical Path)
**What**: Prove 9 theorems showing IR → Yul compilation correctness
**Status**: 0/10 complete (1 prerequisite + 8 statement proofs + 1 composition)
**Impact**: 92% → 98% (statements) → 100% (composition)
**Effort**: 3-5 weeks (1 week prerequisite + 2-4 weeks proofs)
**Parallelizable**: Yes! All 8 statement proofs are independent (after prerequisite)

⚠️ **PREREQUISITE**: Add `execIRStmtFuel` before statement proofs can begin

| # | Statement | Difficulty | Effort | Status | Blocker |
|---|-----------|------------|--------|--------|---------|
| 0 | **Add execIRStmtFuel** | **Medium** | **1w** | ⚪ **TODO** | **BLOCKS ALL** |
| 1 | Variable Assignment | Low | 1h | ⚪ TODO | Needs #0 |
| 2 | Storage Load | Low | 1h | ⚪ TODO | Needs #0 |
| 3 | Storage Store | Low | 1h | ⚪ TODO | Needs #0 |
| 4 | Mapping Load | Medium | 2-4h | ⚪ TODO | Needs #0 |
| 5 | Mapping Store | Medium | 2-4h | ⚪ TODO | Needs #0 |
| 6 | Conditional (if) | Medium-High | 4-8h | ⚪ TODO | Needs #0 |
| 7 | Return | Low | 1-2h | ⚪ TODO | Needs #0 |
| 8 | Revert | Low-Medium | 2-3h | ⚪ TODO | Needs #0 |
| 9 | **Composition** | High | 1-2d | ⚪ TODO | Needs #1-8 |

### 🟡 **Trust Reduction** (3 Components)
**What**: Eliminate or verify all trusted components
**Status**: 0/3 complete
**Impact**: Achieves zero-trust end-to-end verification
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | Function Selectors | keccak256 axiom + CI | 1-2w | ⚪ TODO |
| 2 | Yul→EVM Bridge | Integrate KEVM | 1-3m | ⚪ TODO |
| 3 | EVM Semantics | Strong testing + docs | Ongoing | ⚪ TODO |

### 🟢 **Ledger Sum Properties** (7 Properties)
**What**: Prove total supply equals sum of all balances
**Status**: 0/7 complete
**Impact**: Completes Ledger contract to 100%
**Effort**: 1-2 weeks
**Blocker**: Need finite address set modeling first

| # | Property | Description | Status |
|---|----------|-------------|--------|
| 1 | `mint_sum_equation` | Mint increases total | ⚪ TODO |
| 2 | `burn_sum_equation` | Burn decreases total | ⚪ TODO |
| 3 | `transfer_sum_preservation` | Transfer preserves total | ⚪ TODO |
| 4 | `totalSupply_equals_sum` | Supply = sum of balances | ⚪ TODO |
| 5 | `mint_increases_supply` | Mint increases supply | ⚪ TODO |
| 6 | `burn_decreases_supply` | Burn decreases supply | ⚪ TODO |
| 7 | `transfer_preserves_supply` | Transfer preserves supply | ⚪ TODO |

**Key Insight**: Layer 3 statement proofs are the highest priority. Once complete, you have end-to-end verified contracts! Trust reduction and ledger properties are polish/completeness work.

---

## Critical Path: Layer 3 Completion (🔴 Highest Priority)

**Progress**: 92% → 98% (with statement proofs) → 100% (with composition)

### The Main Blocker

Complete the final verification layer proving **IR → Yul correctness**. This is the only remaining gap in the end-to-end verification chain.

### Current Status

**✅ Completed Components**:
- Yul semantics with executable interpreter
- Preservation theorem structure and scaffolding
- State alignment definitions and result matching predicates
- Fuel-parametric execution models
- Smoke tests demonstrating equivalence for specific cases

**🔄 Pending Work**: 10 items remaining
- **1 PREREQUISITE**: Add `execIRStmtFuel` (blocks all statement proofs)
- **8 statement-level equivalence proofs** (parallelizable, independent, after prerequisite)
- **1 composition theorem** (depends on all 8 statement proofs)

### ⚠️ Prerequisite: Add `execIRStmtFuel`

**Status**: ⚪ BLOCKED - Must be completed before any statement proofs

**Problem**: Current theorem stubs cannot be proven because:
- `execIRStmt` is marked `partial` in `IRInterpreter.lean`
- Lean cannot reason about `partial` functions in proofs
- Cannot unfold, case-split, or prove properties about them

**Example of the issue**:
```lean
theorem assign_equiv :
    execResultsAligned selector
      (execIRStmt irState stmt)           -- ← partial (unprovable!)
      (execYulStmtFuel fuel yulState stmt) -- ← total with fuel (provable)
```

**Solution**: Add fuel-parametric version of `execIRStmt`:

```lean
def execIRStmtFuel (fuel : Nat) (state : IRState) (stmt : YulStmt) : IRExecResult :=
  match fuel, stmt with
  | 0, _ => .revert state  -- Out of fuel
  | Nat.succ fuel', .assign name value =>
      match evalIRExpr state value with
      | some v => .continue (state.setVar name v)
      | none => .revert state
  | Nat.succ fuel', .let_ name value =>
      match evalIRExpr state value with
      | some v => .continue (state.setVar name v)
      | none => .revert state
  -- ... (pattern for all statement types)
```

**Required Work**:
1. Add `execIRStmtFuel` to `Compiler/Proofs/YulGeneration/Equivalence.lean`
2. Mirror the structure of `execYulStmtFuel` from `Semantics.lean`
3. Handle all statement cases: assign, let, expr (sstore/sload/etc), if, switch, block
4. Update `execIRStmtsFuel` to call `execIRStmtFuel` instead of `execIRStmt`
5. Prove adequacy theorem: `execIRStmtFuel (sizeOf stmt + 1) s stmt = execIRStmt s stmt`
6. Update `StatementEquivalence.lean` theorem stubs to use `execIRStmtFuel`

**Estimated Effort**: 1 week
- Day 1-2: Implement `execIRStmtFuel` with all cases
- Day 3-4: Update `execIRStmtsFuel` and test
- Day 5: Prove adequacy theorem
- Day 6-7: Update theorem stubs and verify compilation

**Impact**: Unblocks all 8 statement proofs

**Note**: This is why `StatementEquivalence.lean` currently has all `sorry` statements - the proof infrastructure wasn't complete yet!

### Required Theorems

The core blocker is proving this theorem:

```lean
theorem stmt_equiv :
    ∀ selector fuel stmt irState yulState,
      statesAligned selector irState yulState →
      execResultsAligned selector
        (execIRStmt irState stmt)
        (execYulStmtFuel fuel yulState stmt)
```

**What This Means**: For each IR/Yul statement type, prove that executing it in IR matches executing it in Yul when states are aligned.

### Statement Types to Prove (8 theorems)

Progress tracked in `Compiler/Proofs/YulGeneration/StatementEquivalence.lean`:

| # | Statement Type | Theorem | Difficulty | Effort | Status |
|---|----------------|---------|------------|--------|--------|
| 1 | Variable Assignment | `assign_equiv` | Low | 1h | ⚪ TODO (example provided) |
| 2 | Storage Load | `storageLoad_equiv` | Low | 1h | ⚪ TODO |
| 3 | Storage Store | `storageStore_equiv` | Low | 1h | ⚪ TODO |
| 4 | Mapping Load | `mappingLoad_equiv` | Medium | 2-4h | ⚪ TODO |
| 5 | Mapping Store | `mappingStore_equiv` | Medium | 2-4h | ⚪ TODO |
| 6 | Conditional (if) | `conditional_equiv` | Medium-High | 4-8h | ⚪ TODO |
| 7 | Return | `return_equiv` | Low | 1-2h | ⚪ TODO |
| 8 | Revert | `revert_equiv` | Low-Medium | 2-3h | ⚪ TODO |
| 9 | **Composition** | `stmtList_equiv` | High | 1-2d | ⚪ TODO (depends on 1-8) |

**Legend**: ⚪ TODO | 🔵 In Progress | ✅ Complete

**Total Estimated Effort**: 2-4 weeks (12-25 hours of proof work + composition)

### Composition Strategy

Once individual statement types are proven, use the composition theorem:

```lean
theorem execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
```

This lifts statement-level equivalence to full function body equivalence, completing Layer 3.

### Alternative Approaches

If the fuel-parametric approach proves too complex:

1. **Well-Founded Recursion**: Replace fuel with well-founded recursion on statement structure
2. **Defunctionalization**: Convert to continuation-passing style
3. **Shallow Embedding**: Use Lean's built-in termination checking more directly

### Estimated Effort

**2-4 weeks** of focused Lean proof work, depending on proof automation quality.

### Implementation Guide

**NEW**: We've created a skeleton file with theorem stubs and a worked example to help contributors:

📁 **`Compiler/Proofs/YulGeneration/StatementEquivalence.lean`**
- Contains theorem stubs for all 8 statement types
- Includes a worked example (variable assignment)
- Documents proof strategy, difficulty, and dependencies for each theorem
- Ready for contributors to replace `sorry` with actual proofs

**Getting Started**:
1. Read the roadmap context (this file)
2. Open `StatementEquivalence.lean` and pick a theorem stub
3. Study the worked example to understand the proof pattern
4. Review IR/Yul semantics in `IRInterpreter.lean` and `Semantics.lean`
5. Replace `sorry` with your proof
6. Add smoke tests to verify correctness

**Tracking Progress**:
- Each statement type has a corresponding GitHub issue (label: `layer-3`)
- Use `.github/ISSUE_TEMPLATE/layer3-statement-proof.md` to create issues
- See "Contributing" section below for high-impact opportunities

### Files to Work With

- **Main Work**: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean` - Replace `sorry` stubs
- **Reference**: `Compiler/Proofs/YulGeneration/Equivalence.lean` - State alignment definitions
- **Reference**: `Compiler/Proofs/IRGeneration/IRInterpreter.lean` - IR execution semantics
- **Reference**: `Compiler/Proofs/YulGeneration/Semantics.lean` - Yul execution semantics
- **Testing**: `Compiler/Proofs/YulGeneration/SmokeTests.lean` - Add tests for proven statements
- **Final Step**: `Compiler/Proofs/YulGeneration/Preservation.lean` - Already proven modulo statement equivalence

---

## Trust Reduction (🟡 High Priority)

**Goal**: Eliminate all trust assumptions → Zero-trust verification

### The 3 Remaining Trusted Components

Currently, we trust:

1. **Function Selectors** (keccak256 hash computation) - Not proven in Lean
2. **`solc` Yul Compiler** (Yul → EVM bytecode) - Compilation unverified
3. **EVM Semantics** (assumed to match specification) - No formal link

**Impact**: Eliminating these completes end-to-end zero-trust verification EDSL → EVM

### 1. Function Selector Verification

**Current**: Function selectors are precomputed keccak256 hashes, validated in CI against `solc --hashes` but not proven in Lean.

**Options**:
- **Option A**: Prove keccak256 computation in Lean (hard, but zero-trust)
- **Option B**: Add keccak256 axiom with CI validation (pragmatic)
- **Option C**: Use selector oracle with runtime verification

**Recommended**: Option B (axiom + CI validation)

**Estimated Effort**: 1-2 weeks

**Impact**: Eliminates function dispatch trust assumption

### 2. Yul → EVM Bridge

**Current**: `solc` compilation from Yul to EVM bytecode is trusted.

**Options**:
- **Option A**: Integrate existing EVM semantics (KEVM, Yul+ formalization)
- **Option B**: Prove Yul interpreter matches EVM execution directly
- **Option C**: Use verified Yul compiler (if one exists)
- **Option D**: Runtime verification with differential testing (current mitigation)

**Recommended**: Option A (integrate KEVM or similar)

**Estimated Effort**: 1-3 months (depends on integration complexity)

**Impact**: Achieves end-to-end verification EDSL → EVM with zero trust in compilation

### 3. EVM Semantics

**Current**: EVM execution is assumed to match specification used in proofs. Mitigated by differential testing against actual EVM execution (Foundry).

**Options**:
- **Option A**: Integrate formal EVM semantics (KEVM, eth-isabelle)
- **Option B**: Strengthen differential testing coverage
- **Option C**: Accept as fundamental assumption

**Recommended**: Option B + Option C (strong testing + documented assumption)

**Estimated Effort**: Ongoing (improve test coverage)

**Impact**: High confidence in correctness, not full proof

---

## Property Extraction Polish (🟢 Low Priority - Nearly Complete!)

### Current Status

**After PR #24**:
- ✅ **203/292 properties covered** (70%)
- ✅ **89 exclusions remaining** - ALL are proof-only or modeling limitations
- ✅ **0 missing properties** - Everything testable is tested!

### Remaining Addressable Work

#### Ledger Sum Properties (7 properties)

**Issue**: Properties like `mint_sum_equation` and total supply invariants require proving that the sum of all balances equals total supply.

**Blocker**: Requires finite address set modeling (currently addresses are unbounded).

**The 7 Properties**:
1. `mint_sum_equation` - Minting increases total by amount
2. `burn_sum_equation` - Burning decreases total by amount
3. `transfer_sum_preservation` - Transfers preserve total
4. `totalSupply_equals_sum` - Total supply equals sum of all balances
5. `mint_increases_supply` - Minting increases total supply
6. `burn_decreases_supply` - Burning decreases total supply
7. `transfer_preserves_supply` - Transfers don't change total supply

**Solution**:
```lean
-- Add finite address set abstraction
structure FiniteAddressSet where
  addresses : Finset Address
  maxSize : addresses.card ≤ 2^160

-- Prove sum properties with quantification over finite set
theorem mint_preserves_supply_sum (s : FiniteAddressSet) :
    sum_balances s.addresses state = totalSupply state
```

**Estimated Effort**: 1-2 weeks

**Impact**: Enables proving supply invariants, completes Ledger contract verification to 100%

#### Proof-Only Properties (82 exclusions)

**Status**: No action needed - these are correct exclusions.

**Examples**:
- Storage helpers: `setStorage_*`, `getStorage_*`, `setMapping_*`, `getMapping_*`
- Internal helpers: `isOwner_*` functions
- Low-level operations used only in proofs

**Rationale**: These properties are internal proof machinery, tested implicitly through higher-level properties. They cannot and should not be tested directly in Foundry.

---

## Ecosystem & Scalability (🔵 Medium Priority)

### 1. Realistic Example Contracts

**Goal**: Demonstrate scalability beyond toy examples.

**Proposed Contracts**:
1. **ERC721** (NFT standard)
   - Complex state management (owner mapping, approvals, metadata)
   - Transfer safety checks
   - Enumeration extensions
   - **Effort**: 2-3 weeks

2. **Governance** (voting/proposals)
   - Proposal lifecycle (created → active → executed)
   - Vote tallying
   - Timelock enforcement
   - **Effort**: 2-3 weeks

3. **AMM** (Automated Market Maker)
   - Constant product formula (x * y = k)
   - Swap calculations
   - Liquidity provision/removal
   - **Effort**: 3-4 weeks

**Total Estimated Effort**: 2-3 months for all three

**Impact**: Proves verification approach scales to production contracts

### 2. Developer Experience

**Improvements**:
- **IDE Integration**: VS Code extension with proof highlighting, tactics suggestions
- **Interactive Proof Development**: Lean InfoView integration
- **Better Error Messages**: Context-aware proof failure diagnostics
- **Documentation**: Comprehensive tutorials and proof patterns guide

**Estimated Effort**: 2-3 months

**Impact**: Lowers barrier to entry for new contributors

### 3. Performance Optimization

**Areas for Improvement**:
- Proof automation (faster tactics, better lemma libraries)
- CI optimization (caching, incremental builds)
- Property test generation (smarter fuzzing)

**Estimated Effort**: Ongoing

**Impact**: Faster iteration cycle, better developer experience

---

## Timeline & Milestones

### Phase 1: Core Verification Complete (2-3 months)

**Milestone**: End-to-end verification with minimal trust assumptions

**Work Items**:
- ✅ Complete Layer 3 statement-level proofs (2-4 weeks)
- ✅ Function selector verification (1-2 weeks)
- ✅ Ledger sum properties (1-2 weeks)
- 🔄 Yul → EVM bridge investigation (1-2 months)

**Success Metrics**:
- Layer 3 preservation theorem proven
- Zero unverified assumptions in EDSL → Yul chain
- All addressable properties covered

### Phase 2: Production Readiness (3-6 months)

**Milestone**: First real-world verified contract deployment

**Work Items**:
- Add ERC721 example contract (2-3 weeks)
- Strengthen differential testing coverage (ongoing)
- Comprehensive documentation and tutorials (1 month)
- Performance optimization (ongoing)

**Success Metrics**:
- At least one realistic contract fully verified
- External contributors successfully verify contracts
- CI runs complete in < 30 minutes

### Phase 3: Ecosystem Growth (6-12 months)

**Milestone**: Community adoption and ecosystem maturity

**Work Items**:
- Add Governance and AMM contracts (2-3 months)
- IDE integration (VS Code extension) (2 months)
- Automated property extraction (2-3 months)
- Integration with production smart contract tooling (ongoing)

**Success Metrics**:
- 10+ verified contracts in repository
- Active external contributors
- Production deployments using DumbContracts verification

---

## Success Criteria

### Minimum Viable Product (92 → 98)

**Required**:
- ✅ Layer 3 statement-level proofs complete
- ✅ Function selector verification
- ✅ All testable properties covered

**Result**: End-to-end verification EDSL → Yul with documented trust assumptions

### Production Ready (98 → 100)

**Required**:
- ✅ Yul → EVM bridge verification
- ✅ At least one realistic contract (ERC721)
- ✅ Comprehensive documentation
- ✅ External contributor onboarding successful

**Result**: Production-grade verification framework ready for real-world use

---

## Current Blockers & Risks

### Technical Blockers

1. **Layer 3 Statement Proofs** (🔴 Critical)
   - **Risk**: Fuel-parametric approach may be too complex
   - **Mitigation**: Have 3 alternative proof strategies ready
   - **Owner**: Needs focused Lean expert time

2. **EVM Semantics Integration** (🟡 Medium)
   - **Risk**: Existing formalizations may not align with our model
   - **Mitigation**: Can accept as trust assumption with strong testing
   - **Owner**: Research/design work required

### Resource Constraints

1. **Lean Proof Expertise**
   - **Need**: 2-4 weeks of focused proof work for Layer 3
   - **Current**: Ad-hoc availability
   - **Mitigation**: Document proof patterns, enable parallel work

2. **Testing Infrastructure**
   - **Current**: Excellent (8-shard CI, 10k+ tests)
   - **Need**: Maintain as project scales
   - **Mitigation**: Ongoing investment in CI optimization

---

## Open Questions

1. **Should we prioritize Yul → EVM bridge or accept it as trust assumption?**
   - Tradeoff: 1-3 months of effort vs. documented trust
   - Recommendation: Start with documented trust, revisit after Phase 1

2. **What's the right balance between proof automation and manual proofs?**
   - Current: Good automation for common patterns
   - Opportunity: More powerful tactics for statement equivalence
   - Recommendation: Build automation as we prove Layer 3 statements

3. **Should we support multiple smart contract languages (Solidity, Vyper, Fe)?**
   - Current: EDSL only
   - Opportunity: Broader adoption
   - Recommendation: After Phase 2, if community demand exists

---

## Contributing

### High-Impact Contribution Opportunities

1. **Layer 3 Statement Proofs** (🔴 Critical, Lean expertise required)
   - **NEW**: We've created skeleton file `StatementEquivalence.lean` with theorem stubs!
   - Pick a statement type from the progress table (8 theorems + composition)
   - Study the worked example (variable assignment)
   - Replace `sorry` with your proof
   - See: `Compiler/Proofs/YulGeneration/StatementEquivalence.lean`
   - **Quick Start**:
     1. Start with low-difficulty proofs (storageLoad, storageStore, return)
     2. Work up to medium (mappingLoad, mappingStore)
     3. Tackle conditional (requires recursion/induction)
     4. Final boss: composition theorem (depends on all others)

2. **Property Test Expansion** (🟢 Low priority, Solidity/Foundry skills)
   - Add more differential tests for edge cases
   - Improve property test coverage reporting
   - See: `test/Property*.t.sol`, `scripts/`

3. **Documentation** (🔵 Medium priority, technical writing)
   - Tutorial: "Verifying Your First Contract"
   - Proof patterns guide
   - Architecture deep-dive
   - See: `docs/`, `docs-site/`

4. **Example Contracts** (🔵 Medium priority, smart contract expertise)
   - Implement and verify ERC721, Governance, or AMM
   - Document verification process
   - See: `DumbContracts/Examples/`

### Getting Started

See `VERIFICATION_STATUS.md` for current project state and `Compiler/Proofs/README.md` for proof development guide.

---

**Last Updated**: 2026-02-14
**Status**: Layers 1-2 complete, Layer 3 in progress, property extraction complete
**Next Milestone**: Layer 3 statement-level proofs (2-4 weeks)
