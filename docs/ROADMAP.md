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

### 🟡 **Trust Reduction** (2 Remaining Components)
**What**: Eliminate or verify remaining trusted components
**Status**: 1/3 complete (function selectors resolved)
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | ~~Function Selectors~~ | keccak256 axiom + CI | — | ✅ **DONE** (PR #43, #46) |
| 2 | Yul→EVM Bridge | Integrate KEVM or similar | 1-3m | ⚪ TODO |
| 3 | EVM Semantics | Strong testing + documented assumption | Ongoing | ⚪ TODO |

**Yul→EVM Bridge**: Currently `solc` compilation is trusted. Best option: integrate existing EVM semantics (KEVM). Alternative: accept as trust assumption with strong differential testing (current mitigation).

**EVM Semantics**: Mitigated by differential testing against actual EVM execution (Foundry). Likely remains a documented fundamental assumption.

### 🟢 **Ledger Sum Properties** (7 Properties)
**What**: Prove total supply equals sum of all balances
**Status**: Infrastructure complete (PR #47, #51), proofs pending (Issue #39)
**Remaining**: Complete 7 theorem proofs (~10-14 days Lean expertise)

| # | Property | Description |
|---|----------|-------------|
| 1 | `Spec_deposit_sum_equation` | Deposit increases total by amount |
| 2 | `Spec_withdraw_sum_equation` | Withdraw decreases total by amount |
| 3 | `Spec_transfer_sum_preservation` | Transfer preserves total |
| 4 | `Spec_deposit_sum_singleton_sender` | Singleton set deposit property |
| 5 | `Spec_withdraw_sum_singleton_sender` | Singleton set withdraw property |
| 6 | `Spec_transfer_sum_preserved_unique` | Transfer with unique addresses preserves sum |
| 7 | `Spec_deposit_withdraw_sum_cancel` | Deposit then withdraw cancels out |

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
- ✅ Ledger sum properties infrastructure (PR #47, #51)
- 🔄 Complete sum property proofs (Issue #39 - requires Lean expertise)
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

## Open Questions

1. **Should we prioritize Yul → EVM bridge or accept it as trust assumption?**
   - Tradeoff: 1-3 months of effort vs. documented trust
   - Recommendation: Start with documented trust, revisit after ledger sum properties are complete

2. **Should we support multiple smart contract languages (Solidity, Vyper, Fe)?**
   - Current: EDSL only
   - Recommendation: After Phase 2, if community demand exists

---

## Contributing

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution guidelines and [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md) for current project state.

---

**Last Updated**: 2026-02-14
**Status**: Layers 1-3 complete, trust reduction in progress
