# Verity Roadmap

**Goal**: End-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Current Status

- ✅ **Layer 1 Complete**: 401 theorems across 9 categories (8 contracts + Stdlib math library)
- ✅ **Layer 2 Complete**: All IR generation with preservation proofs (ContractSpec → IR)
- ✅ **Layer 3 Complete**: All 8 statement equivalence proofs + universal dispatcher (PR #42)
- ✅ **Property Testing**: 56% coverage (231/412), all testable properties covered
- ✅ **Differential Testing**: Production-ready with 70k+ tests
- ✅ **Trust Reduction Phase 1**: keccak256 axiom + CI validation (PR #43, #46)
- ✅ **External Linking**: Cryptographic library support (PR #49)
- ✅ **ContractSpec Real-World Support**: Loops, branching, arrays, events, multi-mappings, internal calls, verified extern linking (#153, #154, #179, #180, #181, #184)
- ✅ **Unified AST (#364)**: All 7 contracts migrated with equivalence proofs (28 theorems, PR #370)

---

## Lessons from UnlinkPool (#185)

[UnlinkPool](https://github.com/Th0rgal/unlink-contracts/pull/4) — a ZK privacy pool — was the first non-trivial contract built with Verity (37 theorems, 0 `sorry`, 64 Foundry tests). It exposed gaps in the ContractSpec compilation path that prevented real-world contracts from using the verified pipeline (Layers 2+3).

### What was added

| Feature | Issue | ContractSpec | Core/Interpreter |
|---------|-------|-------------|-----------------|
| If/else branching | #179 | `Stmt.ite` | `execStmt` mutual recursion |
| ForEach loops | #179 | `Stmt.forEach` | `execStmtsFuel` + `expandForEach` desugaring |
| Array/bytes params | #180 | `ParamType.bytes32`, `.array`, `.fixedArray`, `.bytes` | `arrayParams` in `EvalContext` |
| Internal function calls | #181 | `Stmt.internalCall`, `Expr.internalCall`, `FunctionSpec.isInternal` | Statement + expression evaluation |
| Multi-mapping types | #154 | `Expr.mapping2`, `Stmt.setMapping2`, `MappingType`, `FieldType.mappingTyped` | `storageMap2`/`storageMapUint` in `ContractState` |
| Events/logs | #153 | `EventDef`, `EventParam`, `Stmt.emit` | `Event` struct, `emitEvent`, LOG opcodes in codegen |
| Verified extern linking | #184 | `ExternalFunction` with axiom names | Axiom-tracked external calls |

### What this enables

A developer can now write a `ContractSpec` for contracts with conditional logic, loops over arrays, nested mappings (`address → address → uint256` for ERC20 allowances), event emission, internal helper functions, and linked external libraries — and compile through the verified pipeline (Layers 2+3). Previously only simple counter/token contracts were supported.

### Remaining gap

The EDSL path remains more expressive (supports arbitrary Lean, `List.foldl`, pattern matching). Contracts like UnlinkPool that use advanced Lean features still need the EDSL path. The ContractSpec path now covers the subset needed for standard DeFi contracts (ERC20, ERC721, governance, simple AMMs).

### Known interpreter limitations

The SpecInterpreter's basic `execStmts` path does not yet fully model all new constructs:
- **forEach** reverts in `execStmts` — use `execStmtsFuel` for contracts with loops
- **Stmt.internalCall** reverts in `execStmts` — use `execStmtsFuel` with `functions` parameter for contracts with internal calls
- **Expr.internalCall** always returns 0 — internal function lookup as expression not yet implemented (requires threading `functions` through the mutual recursion block)
- **arrayParams** is not populated from `Transaction` — array element access returns 0

These limitations affect only the basic interpreter path (used for proofs). The fuel-based `execStmtsFuel` supports forEach and Stmt.internalCall. The compiler correctly handles all constructs.

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

### ✅ **Unified AST** (Issue #364, PR #370)
**What**: Single deep embedding where `denote ast = edsl_fn` holds by equivalence proof
**Status**: All 7/7 contracts migrated (27 theorems, 0 sorry)

The unified AST (`Verity.AST`) provides a deep embedding that maps 1:1 to EDSL primitives. Simple contracts use `rfl` (definitional equality). Contracts with helper composition (e.g., `onlyOwner`) use `bind_assoc` to flatten nested `bind` before `rfl` closes the goal.

**Next step**: Build the `contract` macro (Phase 4) and compiler `AST → Yul` (Phase 5).

### ✅ **Ledger Sum Properties** (Complete)
**What**: Prove total supply equals sum of all balances
**Status**: All 7/7 proven with zero `sorry` (PR #47, #51, Issue #65 resolved)

| # | Property | Description |
|---|----------|-------------|
| 1 | ~~`Spec_deposit_sum_equation`~~ | ✅ Deposit increases total by amount |
| 2 | ~~`Spec_withdraw_sum_equation`~~ | ✅ Withdraw decreases total by amount |
| 3 | ~~`Spec_transfer_sum_preservation`~~ | ✅ Transfer preserves total |
| 4 | ~~`Spec_deposit_sum_singleton_sender`~~ | ✅ Singleton set deposit property |
| 5 | ~~`Spec_withdraw_sum_singleton_sender`~~ | ✅ Singleton set withdraw property |
| 6 | ~~`Spec_transfer_sum_preserved_unique`~~ | ✅ Transfer with unique addresses preserves sum |
| 7 | ~~`Spec_deposit_withdraw_sum_cancel`~~ | ✅ Deposit then withdraw cancels out |

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
- ✅ Complete sum property proofs (Issue #65 - all 7/7 proven)
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
- Production deployments using Verity verification

---

## Open Questions

1. **Should we prioritize Yul → EVM bridge or accept it as trust assumption?**
   - Tradeoff: 1-3 months of effort vs. documented trust
   - Recommendation: Start with documented trust (ledger sum properties now complete — revisit when resources allow)

2. **Should we support multiple smart contract languages (Solidity, Vyper, Fe)?**
   - Current: EDSL only
   - Recommendation: After Phase 2, if community demand exists

---

## Contributing

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for contribution guidelines and [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md) for current project state.

---

**Last Updated**: 2026-02-18
**Status**: Layers 1-3 complete. Trust reduction 1/3 done. Sum properties complete (7/7 proven). Unified AST complete: all 7/7 contracts migrated (Issue #364). ContractSpec now supports real-world contracts (loops, branching, events, multi-mappings, internal calls, verified externs).
