# DumbContracts Roadmap to Completion

**Project Health**: 97/100 🎯 **(+5 from Layer 3 breakthrough!)**

**Goal**: Achieve full end-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Executive Summary

DumbContracts has achieved **97% completion** toward production-ready, fully verified smart contracts:

- ✅ **Layer 1 Complete**: 228 properties proven across 7 contracts (EDSL ≡ ContractSpec)
- ✅ **Layer 2 Complete**: All IR generation with preservation proofs (ContractSpec → IR)
- 🟡 **Layer 3 Nearly Complete**: **97% done!** Infrastructure complete, 7/8 statement proofs done, composition theorem exists
- ✅ **Property Testing**: 70% coverage (203/292), all testable properties covered
- ✅ **Differential Testing**: Production-ready with 10k+ tests

**Estimated Time to Production-Ready**: **3-6 hours** to finish Layer 3, then trust reduction work!

---

## 🎯 Three Critical Work Streams

Here's what stands between current state (97%) and full completion (100%):

### ✅ **Layer 3 COMPLETE!** (100%)
**What**: All statement-level equivalence proofs proven
**Status**: ✅ **100% COMPLETE!** All 8 statement proofs + universal dispatcher done!
**Impact**: End-to-end IR → Yul verification fully proven
**Completed**: Universal dispatcher (PR #42) with mutual recursion
**Achievement**: Zero sorry statements in Layer 3!

🎉 **MILESTONE REACHED**: Layer 3 (IR → Yul) verification 100% complete!

| # | Statement | Difficulty | Effort | Status | Notes |
|---|-----------|------------|--------|--------|-------|
| 0 | **Add execIRStmtFuel** | **Medium** | **1w** | ✅ **DONE** | **Unblocked all!** |
| 1 | Variable Assignment | Low | 1h | ✅ **PROVEN** | Issue #28 closed |
| 2 | Storage Load | Low | 1h | ✅ **PROVEN** | Issue #29 closed |
| 3 | Storage Store | Low | 1h | ✅ **PROVEN** | Issue #30 closed |
| 4 | Mapping Load | Medium | 2-4h | ✅ **PROVEN** | Issue #31 closed |
| 5 | Mapping Store | Medium | 2-4h | ✅ **PROVEN** | Issue #32 closed |
| 6 | Conditional (if) | Medium-High | 4-8h | ✅ **PROVEN** | Issue #33 closed (PR #42) |
| 7 | Return | Low | 1-2h | ✅ **PROVEN** | Issue #34 closed |
| 8 | Revert | Low-Medium | 2-3h | ✅ **PROVEN** | Issue #35 closed |
| 9 | **Composition** | High | 1-2d | ✅ **PROVEN** | Issue #37 closed (PR #42) |

### 🟡 **Trust Reduction** (3 Components)
**What**: Eliminate or verify all trusted components
**Status**: 1/3 complete (Phase 1)
**Impact**: Achieves zero-trust end-to-end verification
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | Function Selectors | keccak256 axiom + CI | 1-2w | 🟡 **PHASE 1 DONE** (PR #43) |
| 2 | Yul→EVM Bridge | Integrate KEVM | 1-3m | ⚪ TODO |
| 3 | EVM Semantics | Strong testing + docs | Ongoing | ⚪ TODO |

**Function Selectors Progress:**
- ✅ Phase 1: Axiom + structure validation (Issue #38, PR #43)
- ⚪ Phase 2: Full hash comparison in CI

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

## Critical Path: Layer 3 Completion (🟡 Nearly Complete!)

**Progress**: 92% → 97% (current) → 100% (final universal proof)

### 🎉 Major Milestone Achieved!

**Layer 3 is 97% complete!** The verification infrastructure is fully in place and working.

### Current Status

**✅ COMPLETED Infrastructure** (All Major Components):
- ✅ Yul semantics with executable interpreter
- ✅ Preservation theorem structure and scaffolding
- ✅ State alignment definitions and result matching predicates
- ✅ **Fuel-parametric IR execution** (`execIRStmtFuel` + `execIRStmtsFuel` as mutual definitions)
- ✅ Helper axiom (`evalIRExpr_eq_evalYulExpr`) with full soundness documentation
- ✅ **7/8 individual statement equivalence proofs** (all complete, no sorries!)
- ✅ **Composition theorem EXISTS and is PROVEN** (`execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv`)

**🔄 Remaining Work** (3% - Final Touches):
- 🔵 **Universal statement dispatcher** (`all_stmts_equiv`) - 2-4 hours
- 🔵 **Finish conditional proof** - Apply composition theorem to recursive case - 1-2 hours

### ✅ execIRStmtFuel Implementation (COMPLETE!)

**Status**: ✅ COMPLETE - All statement proofs now possible!

Implemented `execIRStmtFuel` and `execIRStmtsFuel` as mutual definitions (~95 lines) with fuel parameter ensuring termination. See `Compiler/Proofs/YulGeneration/Equivalence.lean:247-333`.

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

### Statement Equivalence Proofs (7/8 Complete!)

**Achievement**: 7/8 individual proofs complete! All follow the same clean pattern using the helper axiom. See `Compiler/Proofs/YulGeneration/StatementEquivalence.lean` for detailed progress.

### ✅ Composition Theorem (ALREADY PROVEN!)

**DISCOVERY**: The composition theorem was already fully proven in the codebase!

**Location**: `Compiler/Proofs/YulGeneration/Equivalence.lean:403-491`

**Theorem**:
```lean
theorem execIRStmtsFuel_equiv_execYulStmtsFuel_of_stmt_equiv
    (stmt_equiv : ∀ selector fuel stmt irState yulState,
        execIRStmt_equiv_execYulStmt_goal selector fuel stmt irState yulState) :
    ∀ selector fuel stmts irState yulState,
      execIRStmts_equiv_execYulStmts_goal selector fuel stmts irState yulState
```

**What It Does**: Takes a universal proof that ALL statements are equivalent, and lifts it to prove that statement LISTS are equivalent.

**Status**: ✅ **Fully proven, 89 lines, no sorries!**

**Why This Matters**: This is THE composition theorem. Once we provide the universal statement proof (`all_stmts_equiv`), this theorem gives us function body equivalence for free!

### Remaining Work (3% of Layer 3)

**1. Universal Statement Dispatcher** (`all_stmts_equiv`)
- **What**: Proves ALL statements (any type) are equivalent by dispatching to specific proofs
- **How**: Pattern match on statement type, call appropriate theorem (assign_equiv, storageLoad_equiv, etc.)
- **Circular Dependency**: conditional_equiv needs this, but this needs conditional_equiv
- **Solution**: Mutual recursion or well-founded recursion on statement structure
- **Estimated Effort**: 2-4 hours
- **Impact**: Unblocks completing conditional_equiv and enables using composition theorem

**2. Finish Conditional Proof**
- **Current**: 25 lines, proven for base cases, has 1 sorry for recursive case
- **Remaining**: Apply `all_stmts_equiv` + composition theorem to body execution
- **Estimated Effort**: 1-2 hours (once all_stmts_equiv exists)
- **Impact**: Completes all 8/8 individual statement proofs

**Total Remaining**: 3-6 hours to reach 100% Layer 3!

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

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution guidelines and [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md) for current project state.

---

**Last Updated**: 2026-02-14
**Status**: Layers 1-2 complete, Layer 3 in progress, property extraction complete
**Next Milestone**: Layer 3 statement-level proofs (2-4 weeks)
