# Audit Guide

Entry point for security auditors. For full trust boundary analysis, see [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md). For axiom details, see [AXIOMS.md](AXIOMS.md).

## Architecture

```
Proven path (ContractSpec):
  EDSL (Verity/)          User-facing contract DSL with formal specs
      ↓ Layer 1            Proven: spec preserves EDSL semantics
  ContractSpec            Intermediate specification language
      ↓ Layer 2            Proven: IR preserves spec semantics
  IR                      Flat intermediate representation
      ↓ Layer 3            Proven: Yul preserves IR semantics (1 axiom)
  Yul AST → text          Pretty-printed, compiled by solc
      ↓ Trusted            solc (pinned version)
  EVM bytecode

Unproven path (AST):
  Verity.AST.Stmt         Unified AST (Phase 4 of #364)
      ↓                    ASTCompile: direct Stmt → YulStmt translation
  Yul AST → text          Shared Codegen/PrettyPrint/Linker infrastructure
      ↓ Trusted            solc (pinned version)
  EVM bytecode
```

**Two compilation paths exist.** The ContractSpec path is fully verified across three layers. The AST path (`--ast` flag) bypasses ContractSpec/IR and compiles `Verity.AST.Stmt` directly to Yul — it is **not covered by formal proofs**. CI enforces bytecode equivalence where both paths compile the same contract (6 known diffs tracked in `scripts/fixtures/yul_ast_bytecode_diffs.allowlist`).

All three ContractSpec layers are fully verified in Lean 4. Zero `sorry` placeholders. One axiom (`keccak256_first_4_bytes`) — CI-validated against solc output.

### Key files

| File | Role |
|------|------|
| `Compiler/ContractSpec.lean` | Spec → IR compilation, ABI encoding, all validation |
| `Compiler/Codegen.lean` | IR → Yul AST emission |
| `Compiler/Yul/PrettyPrint.lean` | Yul AST → text rendering |
| `Compiler/Linker.lean` | External library injection (outside proof boundary) |
| `Compiler/Selector.lean` | Function selector computation via keccak256 |
| `Compiler/Specs.lean` | All contract specifications (ContractSpec path) |
| `Compiler/ASTDriver.lean` | AST path: orchestration, constructor loading, validation |
| `Compiler/ASTSpecs.lean` | All contract specifications (AST path) |
| `Compiler/ASTCompile.lean` | AST path: Stmt → YulStmt direct translation |
| `Verity/Core.lean` | Core EDSL types and semantics |

## Trust boundaries

### Where external input enters

1. **Contract specifications** (`Compiler/Specs.lean`): All specs are Lean source — no runtime input parsing. The `compile` function validates specs exhaustively (7+ validators for functions, 5 for constructors) before emitting code.

2. **Calldata**: Generated decoder reads ABI-encoded calldata. `calldatasizeGuard` enforces minimum size for fixed params. Dynamic param bounds rely on EVM semantics (out-of-bounds calldataload returns zero), matching solc behavior.

3. **External libraries** (`Compiler/Linker.lean`): Injected as raw Yul text. Validated for name collisions and call arity but NOT for semantic correctness. **This is outside the proof boundary.** Libraries are the highest-risk trust boundary.

4. **Selector computation** (`Compiler/Selector.lean`): Shells out to `scripts/keccak256.py`. CI cross-validates against `solc --hashes`.

### Where trust changes

| Boundary | What's trusted | What's verified |
|----------|---------------|-----------------|
| EDSL → Spec | Nothing | Full semantic preservation |
| Spec → IR | Nothing | Full semantic preservation |
| IR → Yul | `keccak256_first_4_bytes` axiom | Everything else |
| AST → Yul (AST path) | ASTCompile correctness | CI bytecode diff baseline only |
| Yul → EVM | solc correctness | Yul text correctness |
| Linked libraries | Library code correctness | Name/arity constraints only |
| Storage slots | Keccak256 collision freedom | Slot derivation logic |
| Arithmetic | Wrapping semantics match intent | Wrapping is correctly implemented |

## Security model

### Threat assumptions

- **Solc is correct**: Pinned version, CI-validated. See `scripts/check_solc_pin.py`.
- **Keccak256 is collision-resistant**: Standard assumption. One axiom depends on first-4-bytes uniqueness for selectors.
- **EVM semantics are correct**: Lean model assumes standard EVM behavior.
- **No gas modeling**: Proofs assume infinite gas. Contracts with unbounded loops could be DoS'd. See TRUST_ASSUMPTIONS.md §9.

### Arithmetic semantics

EDSL uses **wrapping** `mod 2^256` arithmetic. Solidity uses **checked** arithmetic (reverts on overflow). Contracts must add explicit `require` guards for overflow-sensitive operations. This is documented in TRUST_ASSUMPTIONS.md §8.

### Revert state semantics

`ContractResult.snd` returns the state **including partial mutations** on revert. The EVM discards all state changes on REVERT. Contracts must follow **checks-before-effects** (all `require` before any `setStorage`/`setMapping`). This is NOT compiler-enforced — see `Verity/Core.lean:80-85` and issue #254.

## Design decisions

| Decision | Rationale |
|----------|-----------|
| Wrapping arithmetic | Simpler formal model; overflow checks are contract-specific policy |
| Single axiom for selectors | Avoids embedding full keccak256 in Lean; CI-validated against solc |
| `partial def` in compiler | ~25 functions recurse on `ParamType` (finite depth); termination proofs would add complexity without security value |
| `allowUnsafeReducibility` | One use in `Semantics.lean:247` for `execYulFuel`; fuel-bounded, provably terminating. See TRUST_ASSUMPTIONS.md §7 |
| Raw text linker injection | Libraries are inherently outside the proof boundary; semantic validation would require a Yul verifier |
| Shared `isInteropEntrypointName` | Single definition filters fallback/receive consistently across Selector, ABI (`renderSpecialEntry` uses it as guard + derives ABI type from `fn.name`), and ContractSpec.compile |
| Shared `isDynamicParamType`/`paramHeadSize` | Single definitions used by both event encoding and calldata parameter loading; eliminates divergence risk |
| Shared `fieldTypeToParamType` | ABI.lean reuses ContractSpec's canonical definition instead of maintaining a private copy; eliminates FieldType→ParamType divergence |
| Non-short-circuit `logicalAnd`/`logicalOr` | Compiled to EVM bitwise `and`/`or` — both operands always evaluated. Simpler codegen; no side-effecting expressions in current DSL |
| Shared `Selector.runKeccak` | Single keccak subprocess helper shared between ContractSpec and AST compilation paths; eliminates duplicated subprocess handling |
| Shared `internalFunctionPrefix` | `"internal_"` prefix for generated Yul internal function names defined once; CI validates no user function name collides with this prefix |
| Shared `errorStringSelectorWord` | `Error(string)` selector (`0x08c379a0 << 224`) defined once in ContractSpec; reused in revert codegen and proof terms. Interpreter keeps a private copy (decimal) to avoid importing ContractSpec; CI validates both values match |
| Shared `addressMask` | 160-bit address mask `(2^160)-1` defined once in ContractSpec; used across codegen (ContractSpec, ASTDriver) and proof terms (Expr.lean). Interpreter keeps private `addressModulus` (`2^160`); CI validates both |
| Shared `selectorShift` | Selector shift amount (`224` bits) defined in ContractSpec; Codegen and proof Builtins keep private copies to avoid cross-module imports. CI validates all three definitions match |

## Known risks

1. **Revert state gap**: Partial mutations visible on revert. Mitigation: checks-before-effects convention. Not enforced.
2. **Linked library correctness**: No semantic validation. Mitigation: name/arity checks, explicit trust boundary documentation.
3. **No gas bounds**: Unbounded loops could exhaust gas. Mitigation: gas calibration tests, manual review.
4. **Wrapping overflow**: No automatic overflow protection. Mitigation: explicit `require` guards per contract.
5. **Non-short-circuit logic ops**: `Expr.logicalAnd`/`logicalOr` always evaluate both operands. Safe today (no side-effecting sub-expressions), but must be revisited if low-level calls (#622) are added to `Expr`.
6. **AST path unproven**: `ASTCompile` translates `Verity.AST.Stmt` → `YulStmt` without formal verification. CI tracks a bytecode diff baseline (6 known mismatches) but cannot prove semantic equivalence. The AST path also lacks events, custom errors, internal functions, and `isPayable` support.

## External dependencies

| Dependency | Why trusted |
|------------|-------------|
| Lean 4 type checker | Foundational trust; widely used, formally specified |
| solc (pinned) | Industry standard; version pinned in `foundry.toml`, CI-validated |
| Python keccak256 | Selector computation only; cross-validated against solc |
| Foundry | Testing only; not in production TCB |

## Attack surface

| Surface | Risk | Mitigation |
|---------|------|------------|
| Malformed calldata | Low | ABI decoding matches solc; EVM protects OOB reads |
| Storage slot collision | Very low | Standard keccak256 mapping layout |
| Selector collision | Very low | CI validates against solc; `firstDuplicateSelector` check in compiler |
| Linked library bugs | Medium | Outside proof boundary; auditor must review library code separately |
| Integer overflow | Low | Documented wrapping semantics; contract-level guards required |

## CI validation suite

30+ scripts enforce consistency between proofs, tests, and documentation. Key checks:

- `check_yul_compiles.py`: All generated Yul compiles with solc; legacy/AST bytecode diff baseline
- `check_selectors.py` / `check_selector_fixtures.py`: Selector cross-validation (both ContractSpec and ASTSpecs; cross-checks signature equivalence; reserved prefix collision check; Error(string) selector constant sync; address mask constant sync; selector shift constant sync; internal prefix sync; special entrypoint names sync)
- `check_doc_counts.py`: Theorem/test counts consistent across all docs
- `check_lean_warning_regression.py`: Zero-warning policy
- `check_axiom_locations.py`: All axioms documented in AXIOMS.md
- `check_storage_layout.py`: Storage layout validation
- `check_solc_pin.py`: solc version pinned
- `check_builtin_list_sync.py`: Linker/ContractSpec opcode list sync
