# DumbContracts Roadmap

**Goal**: End-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Current Status

- ✅ **Layer 1 Complete**: 228 properties proven across 7 contracts (EDSL ≡ ContractSpec)
- ✅ **Layer 2 Complete**: All IR generation with preservation proofs (ContractSpec → IR)
- ✅ **Layer 3 Complete**: All 8 statement equivalence proofs + universal dispatcher (PR #42)
- ✅ **Property Testing**: 70% coverage (203/292), all testable properties covered
- ✅ **Differential Testing**: Production-ready with 10k+ tests
- ✅ **Trust Reduction Phase 1**: keccak256 axiom + CI validation (PR #43, #46)
- ✅ **External Linking**: Cryptographic library support (PR #49)

---

## Remaining Work Streams

### 🟡 **Trust Reduction** (3 Components)
**What**: Eliminate or verify all trusted components
**Status**: 1/3 complete (Phase 1)
**Impact**: Achieves zero-trust end-to-end verification
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | Function Selectors | keccak256 axiom + CI | 1-2w | ✅ **DONE** (PR #43, #46) |
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

## Trust Reduction (🟡 High Priority)

**Goal**: Eliminate all trust assumptions → Zero-trust verification

### The 3 Remaining Trusted Components

Currently, we trust:

1. ~~**Function Selectors**~~ → ✅ Resolved via keccak256 axiom + CI validation (PR #43, #46)
2. **`solc` Yul Compiler** (Yul → EVM bytecode) - Compilation unverified
3. **EVM Semantics** (assumed to match specification) - No formal link

### Yul → EVM Bridge

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
- ✅ Complete Layer 3 statement-level proofs (PR #42)
- ✅ Function selector verification (PR #43, #46)
- 🔄 Ledger sum properties (Issue #39, PR #47 WIP)
- 🔄 Yul → EVM bridge investigation

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
**Status**: Layers 1-3 complete, trust reduction in progress
