# Audit Guide

Entry point for security auditors. For full trust boundary analysis, see [TRUST_ASSUMPTIONS.md](TRUST_ASSUMPTIONS.md). For axiom details, see [AXIOMS.md](AXIOMS.md).

## Architecture

```
EDSL (Verity/)          User-facing contract DSL with formal specs
    ↓ Layer 1            Proven: spec preserves EDSL semantics
ContractSpec            Intermediate specification language
    ↓ Layer 2            Proven: IR preserves spec semantics
IR                      Flat intermediate representation
    ↓ Layer 3            Proven: Yul preserves IR semantics (1 axiom)
Yul AST → text          Pretty-printed, compiled by solc
    ↓ Trusted            solc (pinned version)
EVM bytecode
```

All three layers are fully verified in Lean 4. Zero `sorry` placeholders. One axiom (`keccak256_first_4_bytes`) — CI-validated against solc output.

### Key files

| File | Role |
|------|------|
| `Compiler/ContractSpec.lean` | Spec → IR compilation, ABI encoding, all validation |
| `Compiler/Codegen.lean` | IR → Yul AST emission |
| `Compiler/Yul/PrettyPrint.lean` | Yul AST → text rendering |
| `Compiler/Linker.lean` | External library injection (outside proof boundary) |
| `Compiler/Selector.lean` | Function selector computation via keccak256 |
| `Compiler/Specs.lean` | All contract specifications |
| `Verity/Core.lean` | Core EDSL types and semantics |

## Trust boundaries

### Where external input enters

1. **Contract specifications** (`Compiler/Specs.lean`): All specs are Lean source — no runtime input parsing. The `compile` function validates specs exhaustively (7+ validators) before emitting code.

2. **Calldata**: Generated decoder reads ABI-encoded calldata. `calldatasizeGuard` enforces minimum size for fixed params. Dynamic param bounds rely on EVM semantics (out-of-bounds calldataload returns zero), matching solc behavior.

3. **External libraries** (`Compiler/Linker.lean`): Injected as raw Yul text. Validated for name collisions and call arity but NOT for semantic correctness. **This is outside the proof boundary.** Libraries are the highest-risk trust boundary.

4. **Selector computation** (`Compiler/Selector.lean`): Shells out to `scripts/keccak256.py`. CI cross-validates against `solc --hashes`.

### Where trust changes

| Boundary | What's trusted | What's verified |
|----------|---------------|-----------------|
| EDSL → Spec | Nothing | Full semantic preservation |
| Spec → IR | Nothing | Full semantic preservation |
| IR → Yul | `keccak256_first_4_bytes` axiom | Everything else |
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
| Shared `isInteropEntrypointName` | Single definition filters fallback/receive consistently across Selector, ABI, and ContractSpec.compile |
| Shared `isDynamicParamType`/`paramHeadSize` | Single definitions used by both event encoding and calldata parameter loading; eliminates divergence risk |

## Known risks

1. **Revert state gap**: Partial mutations visible on revert. Mitigation: checks-before-effects convention. Not enforced.
2. **Linked library correctness**: No semantic validation. Mitigation: name/arity checks, explicit trust boundary documentation.
3. **No gas bounds**: Unbounded loops could exhaust gas. Mitigation: gas calibration tests, manual review.
4. **Wrapping overflow**: No automatic overflow protection. Mitigation: explicit `require` guards per contract.

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

- `check_yul_compiles.py`: All generated Yul compiles with solc; bytecode parity
- `check_selectors.py` / `check_selector_fixtures.py`: Selector cross-validation
- `check_doc_counts.py`: Theorem/test counts consistent across all docs
- `check_lean_warning_regression.py`: Zero-warning policy
- `check_axiom_locations.py`: All axioms documented in AXIOMS.md
- `check_storage_layout.py`: Storage layout validation
- `check_solc_pin.py`: solc version pinned
