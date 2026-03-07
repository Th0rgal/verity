# Verity Roadmap

**Goal**: End-to-end verified smart contracts from EDSL to EVM bytecode with minimal trust assumptions.

---

## Current Status

- ✅ **Layer 1 Complete**: see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md) for the current theorem totals and contract coverage table
- ✅ **Layer 2 Complete**: All IR generation with preservation proofs (CompilationModel → IR)
- ✅ **Layer 3 Complete**: All 8 statement equivalence proofs + universal dispatcher (PR #42)
- ✅ **Property Testing**: see [VERIFICATION_STATUS.md](VERIFICATION_STATUS.md) for current coverage totals and exclusions
- ✅ **Differential Testing**: Production-ready with 70k+ tests
- ✅ **Trust Reduction Phase 1**: keccak256 axiom + CI validation (PR #43, #46)
- ✅ **External Linking**: Cryptographic library support (PR #49)
- ✅ **CompilationModel Real-World Support**: Loops, branching, arrays, events, multi-mappings, internal calls, verified extern linking (#153, #154, #179, #180, #181, #184)

---

## Migration + Optimization Execution Tracker (P0 -> P2)

This tracker is the execution order for migration-oriented compiler work. Later phases are blocked on earlier phases unless noted.

| Priority | Milestone | Issues | Dependency | Exit Criteria |
|---|---|---|---|---|
| P0 | Canonical equivalence baseline | [#581](https://github.com/Th0rgal/verity/issues/581) | none | Canonical Yul equivalence check in CI for at least one real contract pair |
| P1 | Proven optimization foundation | [#582](https://github.com/Th0rgal/verity/issues/582), [#583](https://github.com/Th0rgal/verity/issues/583), [#584](https://github.com/Th0rgal/verity/issues/584) | blocked by #581 | Proven patch framework + initial patch pack + warning non-regression gate |
| P2 | Interop + verification docs hardening | [#585](https://github.com/Th0rgal/verity/issues/585), [#586](https://github.com/Th0rgal/verity/issues/586) | blocked by P0/P1 outputs | Generated verification artifact consumed by docs + published interop support profile |

Current P0 baseline artifact coverage:
- `artifacts/evmyullean_capability_report.json` tracks builtin overlap boundaries and explicit unsupported adapter nodes.
- `artifacts/evmyullean_unsupported_nodes.json` provides a dedicated machine-readable unsupported-node list for adapter-lowering gaps.
- `artifacts/evmyullean_adapter_report.json` tracks adapter AST-lowering coverage (`supported`/`partial`/`gap`) and runtime seam status.

Current P1 foundation coverage (Issue #582):
- Deterministic expression patch DSL + pass engine in `Compiler/Yul/PatchFramework.lean`
- Initial patch pack in `Compiler/Yul/PatchRules.lean` with explicit metadata (`pattern`, `rewrite`, `side_conditions`, `proof_id`, `pass_phase`, `priority`)
- Proof hooks + preservation theorems in `Compiler/Proofs/YulGeneration/PatchRulesProofs.lean`
- Opt-in compiler path via `Compiler.emitYulWithOptions` (`YulEmitOptions.patchConfig`)
- Report-capable compiler path via `Compiler.emitYulWithOptionsReport` to surface patch manifest/iteration metadata to CI and tooling
- `verity-compiler` patch coverage emission (`--patch-report`) now writes per-contract/rule TSV output and CI uploads it as an artifact for Issue #583 tuning
- Static gas delta gate for patch impact (`scripts/check_patch_gas_delta.py`) now compares baseline vs patch-enabled reports in CI with median/p90 non-regression and measurable-improvement requirements
- CI now runs `check_yul.py` + `check_gas.py coverage` on `artifacts/yul-patched` as part of Issue #582 fail-closed hardening for patch-enabled output, including filename-set parity checks against baseline Yul output
- CI now runs a dedicated Foundry patched-Yul smoke gate (`DIFFTEST_YUL_DIR=artifacts/yul-patched`) so differential/property harnesses execute against patch-enabled output

Execution policy:
1. Do not start patch-pack expansion in `#583` before `#582` proof hooks are merged.
2. Treat `#584` as a release gate for ongoing compiler work after initial warning cleanup lands.
3. Enforce Lean warning non-regression via `artifacts/lean_warning_baseline.json` + CI check (`scripts/check_lean_warning_regression.py`) until warning count reaches zero.
4. Treat `#585` docs generation as authoritative source for public metrics before broader docs expansion.
5. Keep issue bodies and this section synchronized when scope/order changes.

### Solidity Interop Profile (Issue #586)

Interop priority is based on migration friction observed in the Morpho integration path.

Status legend:
- `supported`: available end-to-end for migration use
- `partial`: usable with limits or missing proof/diagnostics coverage
- `unsupported`: no first-class support yet

| Priority | Feature | Spec support | Codegen support | Proof status | Test status | Current status |
|---|---|---|---|---|---|---|
| 1 | Custom errors + typed revert payloads | partial | partial | n/a | partial | partial |
| 2 | Low-level calls (`call`/`staticcall`/`delegatecall`) + returndata handling | partial | partial | n/a | partial | partial |
| 3 | `fallback` / `receive` / payable entrypoint modeling | partial | partial | n/a | partial | partial |
| 4 | Full event ABI parity (indexed dynamic + tuple hashing) | supported | supported | supported | supported | supported |
| 5 | Storage layout controls (packed fields + explicit slot mapping) | partial | partial | partial | partial | partial |
| 6 | ABI JSON artifact generation | partial | partial | n/a | partial | partial |

Recent progress for storage layout controls (`#623`):
- `CompilationModel.Field` now supports optional explicit slot assignment (`slot := some <n>`), with backward-compatible positional slots when omitted.
- Compiler now fails fast on conflicting effective slot assignments with an issue-linked diagnostic.
- `CompilationModel.Field` now supports compatibility mirror-write slots (`aliasSlots := [...]`), so `setStorage`/`setMapping`/`setMapping2` write to canonical and alias slots in one declarative policy.
- `CompilationModel` now supports slot remap policies (`slotAliasRanges := [{ sourceStart := a, sourceEnd := b, targetStart := c }, ...]`) so compatibility windows like `8..11 -> 20..23` can be declared once and applied automatically to canonical field writes.
- `CompilationModel` now supports declarative reserved storage slot ranges (`reservedSlotRanges := [{ start := a, end_ := b }, ...]`) with compile-time overlap checks and fail-fast diagnostics when field canonical/alias write slots intersect reserved intervals.
- `CompilationModel.Field` now supports packed subfield placement (`packedBits := some { offset := o, width := w }`) so multiple fields can share a slot with disjoint bit ranges; codegen performs masked read-modify-write updates and masked reads directly from layout metadata.
- `FieldType.mappingStruct` / `FieldType.mappingStruct2` plus `Expr.structMember` / `Stmt.setStructMember` now make struct-valued mappings and packed submembers first-class in the CompilationModel surface, and `verity_contract` now exposes matching `MappingStruct(...)` / `MappingStruct2(...)` storage declarations so Morpho-style layouts no longer require handwritten CompilationModel shims.

Recent progress for low-level calls + returndata handling (`#622`):
- `CompilationModel.Expr` now supports first-class low-level call primitives (`call`, `staticcall`, `delegatecall`) with explicit gas/value/target/input/output operands and deterministic Yul lowering.
- `CompilationModel.Expr.returndataSize`, `Stmt.returndataCopy`, and `Stmt.revertReturndata` now provide first-class returndata access and revert-data forwarding without raw Yul builtin injection.
- `CompilationModel.Expr.returndataOptionalBoolAt(outOffset)` now provides a first-class ERC20 compatibility helper for optional return-data bool decoding (`returndatasize()==0 || (returndatasize()==32 && mload(outOffset)==1)`), so low-level token call acceptance paths can be expressed without raw Yul builtins.
- Raw `Expr.externalCall` interop names for low-level/builtin opcodes remain fail-fast rejected, preserving explicit migration diagnostics while the first-class surface continues to expand.
- ABI artifact emission now reflects explicit function mutability markers (`isView`, `isPure`) as `stateMutability: "view" | "pure"` in generated JSON.

Recent progress for custom errors (`#586`):
- `Stmt.requireError` / `Stmt.revertError` now support ABI encoding for tuple/fixed-array/array/bytes payloads (including nested dynamic composites) when arguments are direct `Expr.param` references.
- Static scalar payload args remain expression-friendly (`uint256`, `address`, `bool`, `bytes32`), while composite/dynamic payload args fail fast with issue-linked diagnostics when not provided as direct parameter references.

Recent progress for ABI JSON artifact generation (`#688`):
- `verity-compiler --abi-output <dir>` emits one `<Contract>.abi.json` file per compiled CompilationModel in the supported compilation path.

Delivery policy for unsupported features:
1. Compiler diagnostics must identify the exact unsupported construct.
2. Error text must suggest the nearest currently-supported pattern.
3. Error text must include the tracking issue reference.

---

## Lessons from UnlinkPool (#185)

[UnlinkPool](https://github.com/Th0rgal/unlink-contracts/pull/4) — a ZK privacy pool — was the first non-trivial contract built with Verity (37 theorems, 0 `sorry`, 64 Foundry tests). It exposed gaps in the CompilationModel compilation path that prevented real-world contracts from using the verified pipeline (Layers 2+3).

### What was added

| Feature | Issue | CompilationModel | Core/Interpreter |
|---------|-------|-------------|-----------------|
| If/else branching | #179 | `Stmt.ite` | `execStmt` mutual recursion |
| ForEach loops | #179 | `Stmt.forEach` | `execStmtsFuel` + `expandForEach` desugaring |
| Array/bytes params | #180 | `ParamType.bytes32`, `.array`, `.fixedArray`, `.bytes` | `arrayParams` in `EvalContext` |
| Internal function calls | #181 | `Stmt.internalCall`, `Expr.internalCall`, `FunctionSpec.isInternal` | Statement + expression evaluation |
| Multi-mapping types | #154 | `Expr.mapping2`, `Stmt.setMapping2`, `MappingType`, `FieldType.mappingTyped` | `storageMap2`/`storageMapUint` in `ContractState` |
| Events/logs | #153 | `EventDef`, `EventParam`, `Stmt.emit` | `Event` struct, `emitEvent`, LOG opcodes in codegen |
| Verified extern linking | #184 | `ExternalFunction` with axiom names | Axiom-tracked external calls |

### What this enables

A developer can now write a `CompilationModel` for contracts with conditional logic, loops over arrays, nested mappings (`address → address → uint256` for ERC20 allowances), event emission, internal helper functions, and linked external libraries — and compile through the verified pipeline (Layers 2+3). Previously only simple counter/token contracts were supported.

### Remaining gap

The EDSL path remains more expressive (supports arbitrary Lean, `List.foldl`, pattern matching). Contracts like UnlinkPool that use advanced Lean features still need the EDSL path. The CompilationModel path now covers the subset needed for standard DeFi contracts (ERC20, ERC721, governance, simple AMMs).

### Interpreter feature-support contract

A comprehensive feature matrix documents which CompilationModel constructs each interpreter supports, their proof status, and known limitations:

- **Human-readable**: [`docs/INTERPRETER_FEATURE_MATRIX.md`](INTERPRETER_FEATURE_MATRIX.md)
- **Machine-readable**: `artifacts/interpreter_feature_matrix.json`
- **Smoke tests**: `Compiler/Proofs/InterpreterFeatureTest.lean` (22 `native_decide` proofs)

Key: the default path is `execStmtsFuel` (fuel-based), which supports the full construct set including loops and internal calls. The basic `execStmts` path is used only for proofs that do not need these features.

---

## Remaining Work Streams

### 🟡 **Trust Reduction** (2 Remaining Components)
**What**: Eliminate or verify remaining trusted components
**Status**: 1/3 complete (function selectors resolved)
**Effort**: 1-4 months total

| # | Component | Approach | Effort | Status |
|---|-----------|----------|--------|--------|
| 1 | ~~Function Selectors~~ | keccak256 axiom + CI | — | ✅ **DONE** (PR #43, #46) |
| 2 | Yul/EVM Semantics Bridge | EVMYulLean integration | 1-3m | 🟡 **IN PROGRESS** |
| 3 | EVM Semantics | Strong testing + documented assumption | Ongoing | ⚪ TODO |

**Yul/EVM Semantics Bridge**: EVMYulLean (NethermindEth) provides formally-defined Yul AST types and UInt256 operations. Current integration status:
- AST adapter: all 11 statement types + 5 expression types lower to EVMYulLean AST (0 gaps)
- Builtin bridge: 15 pure arithmetic/comparison/bitwise builtins delegate to EVMYulLean `UInt256` operations with compile-time equivalence checks
- State-dependent builtins (sload, caller, calldataload) and Verity helpers (mappingSlot) remain on the Verity evaluation path
- Next: full semantic evaluation via EVMYulLean interpreter, bridging proofs for state-dependent builtins

**EVM Semantics**: Mitigated by differential testing against actual EVM execution (Foundry). Likely remains a documented fundamental assumption.

### 🟡 **Parity-Pack Identity Track** (Issue #967)
**What**: Move from deterministic output-shape parity to exact pinned-`solc` Yul identity with proof-carrying rewrites.
**Status**: Groundwork + initial implementation (pack registry + CLI selection + validation guard).

Planned phases:
1. versioned parity packs keyed to pinned compiler tuples;
2. typed subtree rewrite model with mandatory semantic-preservation proof refs;
3. AST-level identity checker + CI gate + unsupported-manifest workflow.

Reference docs:
- `docs/SOLIDITY_PARITY_PROFILE.md`
- `docs/PARITY_PACKS.md`
- `docs/REWRITE_RULES.md`
- `docs/IDENTITY_CHECKER.md`
### ✅ **Ledger Sum Properties** (Complete)
**What**: Prove total supply equals sum of all balances
**Status**: All 7/7 proven with zero `sorry` (PR #47, #51, Issue #65 resolved)

| # | Property | Description |
|---|----------|-------------|
| 1 | ~~`deposit_sum_equation`~~ | ✅ Deposit increases total by amount |
| 2 | ~~`withdraw_sum_equation`~~ | ✅ Withdraw decreases total by amount |
| 3 | ~~`transfer_sum_preservation`~~ | ✅ Transfer preserves total |
| 4 | ~~`deposit_sum_singleton_sender`~~ | ✅ Singleton set deposit property |
| 5 | ~~`withdraw_sum_singleton_sender`~~ | ✅ Singleton set withdraw property |
| 6 | ~~`transfer_sum_preserved_unique`~~ | ✅ Transfer with unique addresses preserves sum |
| 7 | ~~`deposit_withdraw_sum_cancel`~~ | ✅ Deposit then withdraw cancels out |

---

## Ecosystem & Scalability (🔵 Medium Priority)

### 1. Realistic Example Contracts

**Goal**: Demonstrate scalability beyond toy examples.

**Completed Contracts**:
1. **ERC721** (NFT standard) — implemented with 11 theorems, differential + property tests

**Proposed Contracts**:
1. **Governance** (voting/proposals)
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
- ~~Add ERC721 example contract~~ (done — 11 theorems)
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

**Last Updated**: 2026-02-20
**Status**: Layers 1-3 complete. Trust reduction 1/3 done. Sum properties complete (7/7 proven). CompilationModel now supports real-world contracts (loops, branching, events, multi-mappings, internal calls, verified externs).
