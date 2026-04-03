# Provable Intent DSL — Design Plan

> RFC: A minimal, composable DSL for describing transaction intent in natural language,
> with the property that intent correctness can be verified via a Groth16 proof.

See PR #1676 description for the full design document.

## Quick Start

### Build

```bash
lake build   # compiles all Lean, including intent DSL smoke tests
make check   # runs CI checks
```

### End-to-End Circom Test

The script `scripts/test_circom_e2e.sh` validates the full pipeline from Lean
to verified Circom witness:

```bash
# Prerequisites: circom, node, npm, snarkjs
# Install circom: https://docs.circom.io/getting-started/installation/
# Install snarkjs: npm install -g snarkjs

./scripts/test_circom_e2e.sh
```

This script:
1. Generates `.circom` files from the ERC-20 `IntentSpec` (via `lake env lean`)
2. Compiles them with `circom` (checks syntax + constraint generation)
3. Computes Poseidon commitment inputs using `circomlibjs`
4. Generates witnesses and verifies R1CS constraint satisfaction with `snarkjs`

### Test Cases

| Test | Function | Input | Branch | TemplateId | Constraints |
|------|----------|-------|--------|------------|-------------|
| `transfer_amount_1000` | `transfer(to=0xdead, amount=1000)` | Specific amount | else | 1 | 605 NL |
| `transfer_amount_max` | `transfer(to=0xdead, amount=MAX_UINT256)` | All tokens | then | 0 | 605 NL |
| `approve_amount_500` | `approve(spender=0xbeef, amount=500)` | Specific amount | else | 1 | 605 NL |

All three test cases generate correct witnesses that satisfy R1CS constraints.

## Architecture

```
IntentSpec (Lean)
    │
    ├── Verity/Intent/Types.lean     AST types
    ├── Verity/Intent/Eval.lean      Reference evaluator (total)
    ├── Verity/Intent/Validate.lean  Validates against CompilationModel
    ├── Verity/Intent/Example.lean   ERC-20 example + smoke tests
    │
    └── Compiler/Circom.lean         Circom circuit generator
         │
         └── .circom files
              │
              ├── circom compiler → R1CS + WASM
              └── snarkjs → witness → proof
```

## Phase 1 Status

- [x] `Verity/Intent/Types.lean` — AST types (Expr, Stmt, FnDecl, IntentSpec)
- [x] `Verity/Intent/Eval.lean` — Reference evaluator (total, fuel-based)
- [x] `Verity/Intent/Validate.lean` — Validates IntentSpec against CompilationModel
- [x] `Compiler/Circom.lean` — Circom circuit generator (Poseidon commitments, uint256 lo/hi)
- [x] `--circom-output <dir>` CLI flag (wired through compile pipeline)
- [x] ERC-20 example with 3 end-to-end test cases
- [x] `lake build` passes, `make check` passes

### Constraint Budget (Measured)

| Component | Constraints |
|-----------|------------|
| 2× Poseidon(4) commitments | ~480 |
| uint256 equality (2× IsEqual) | ~10 |
| Branch selection | ~2 |
| Signal routing | ~113 |
| **Total (non-linear)** | **605** |

This is well within the estimated ~700–1,500 range from the design document.
