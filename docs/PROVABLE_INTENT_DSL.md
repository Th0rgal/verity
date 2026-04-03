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

### End-to-End Test (Circom + Groth16)

The script `scripts/test_circom_e2e.sh` validates the **complete pipeline** from Lean
to verified Groth16 proof:

```bash
# Prerequisites: circom, node, npm, snarkjs
# Install circom: https://docs.circom.io/getting-started/installation/
# Install snarkjs: npm install -g snarkjs

./scripts/test_circom_e2e.sh
```

This script runs 6 tests across 5 pipeline stages:

1. **Generate** `.circom` files from the ERC-20 `IntentSpec` (via `lake env lean`)
2. **Compile** circuits with `circom` (syntax check + constraint generation)
3. **Compute** Poseidon commitment inputs using `circomlibjs`
4. **Witness** generation and R1CS constraint verification with `snarkjs`
5. **Prove** Groth16 proof generation (trusted setup → prove → verify)

### Test Matrix

| Test | Function | Input | Branch | TemplateId | Constraints | Witness | Proof |
|------|----------|-------|--------|------------|-------------|---------|-------|
| `transfer_1000` | `transfer(to=0xdead, amount=1000)` | Specific amount | else | 1 | 605 NL | PASS | PASS |
| `transfer_max` | `transfer(to=0xdead, amount=MAX)` | All tokens | then | 0 | 605 NL | PASS | PASS |
| `approve_500` | `approve(spender=0xbeef, amount=500)` | Specific amount | else | 1 | 605 NL | PASS | PASS |

All 6 tests pass: 3 witness verifications + 3 Groth16 proof verifications.

### What the Proof Proves

For each test case, the Groth16 proof demonstrates:

> "I know parameter values `(to, amount_lo, amount_hi)` such that:
> 1. The selector matches `0xa9059cbb` (transfer) or `0x095ea7b3` (approve)
> 2. `Poseidon(selector, to, amount_lo, amount_hi) == calldataCommitment`
> 3. Evaluating the intent DSL program selects the correct template and holes
> 4. `Poseidon(templateId, holes...) == outputCommitment`"

The proof is **128 bytes** and can be verified with a single pairing check (~200K gas on-chain).

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
              ├── snarkjs wchk → witness verification
              └── snarkjs groth16 → proof generation + verification
```

### CLI Integration

```bash
# Generate Circom circuits from a compiled module with IntentSpec:
verity-compiler --module Contracts.ERC20.ERC20 --circom-output artifacts/circom
```

The `--circom-output` flag triggers:
1. Loading the module's `intentSpec` constant
2. Validating against the `CompilationModel`
3. Computing selectors from the ABI
4. Writing one `.circom` file per intent binding

## Phase 1 Status

- [x] `Verity/Intent/Types.lean` — AST types (Expr, Stmt, FnDecl, IntentSpec)
- [x] `Verity/Intent/Eval.lean` — Reference evaluator (total, fuel-based)
- [x] `Verity/Intent/Validate.lean` — Validates IntentSpec against CompilationModel
- [x] `Compiler/Circom.lean` — Circom circuit generator (Poseidon commitments, uint256 lo/hi)
- [x] `Compiler/CircomTest.lean` — Regression tests for generated Circom structure
- [x] `--circom-output <dir>` CLI flag (wired through compile pipeline)
- [x] ERC-20 example with 3 test cases (witness + proof)
- [x] Groth16 proof generation and verification
- [x] `lake build` passes, `make check` passes

### Constraint Budget (Measured)

| Component | Constraints |
|-----------|------------|
| 2× Poseidon(4) commitments | ~480 |
| uint256 equality (2× IsEqual) | ~10 |
| Branch selection | ~2 |
| Signal routing | ~113 |
| **Total (non-linear)** | **605** |

This is well within the estimated ~700-1,500 range from the design document.
