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

This script runs 26 tests across 5 pipeline stages (3 contracts, 9 circuits):

1. **Generate** `.circom` files from the ERC-20 and Ledger `IntentSpec`s (via `lake env lean`)
2. **Compile** circuits with `circom` (syntax check + constraint generation)
3. **Compute** Poseidon commitment inputs using `circomlibjs`
4. **Witness** generation and R1CS constraint verification with `snarkjs`
5. **Prove** Groth16 proof generation (trusted setup → prove → verify)

### Test Matrix

**ERC-20 Contract:**

| Test | Function | Input | Branch | TemplateId | Witness | Proof |
|------|----------|-------|--------|------------|---------|-------|
| `transfer_1000` | `transfer(to=0xdead, amount=1000)` | Specific amount | else | 1 | PASS | PASS |
| `transfer_max` | `transfer(to=0xdead, amount=MAX)` | All tokens | then | 0 | PASS | PASS |
| `approve_500` | `approve(spender=0xbeef, amount=500)` | Specific amount | else | 1 | PASS | PASS |
| `transferFrom_2000` | `transferFrom(from=0xcafe, to=0xdead, amount=2000)` | Specific amount | else | 1 | PASS | PASS |
| `transferFrom_max` | `transferFrom(from=0xcafe, to=0xdead, amount=MAX)` | All tokens | then | 0 | PASS | PASS |

**Ledger Contract:**

| Test | Function | Input | Branch | TemplateId | Witness | Proof |
|------|----------|-------|--------|------------|---------|-------|
| `deposit_5000` | `deposit(amount=5000)` | Deposit | — | 0 | PASS | PASS |
| `withdraw_3000` | `withdraw(amount=3000)` | Withdraw | — | 0 | PASS | PASS |
| `ledger_transfer_2000` | `transfer(to=0xdead, amount=2000)` | Specific amount | else | 1 | PASS | PASS |
| `ledger_transfer_max` | `transfer(to=0xdead, amount=MAX)` | All tokens | then | 0 | PASS | PASS |

**ERC-721 Contract:**

| Test | Function | Input | Branch | TemplateId | Witness | Proof |
|------|----------|-------|--------|------------|---------|-------|
| `erc721_approve_42` | `approve(approved=0xbeef, tokenId=42)` | Approve token | — | 0 | PASS | PASS |
| `setApproval_true` | `setApprovalForAll(operator=0xbeef, approved=true)` | Approve | then | 0 | PASS | PASS |
| `setApproval_false` | `setApprovalForAll(operator=0xbeef, approved=false)` | Revoke | else | 1 | PASS | PASS |
| `erc721_transferFrom_99` | `transferFrom(from=0xcafe, to=0xdead, tokenId=99)` | Transfer token | — | 0 | PASS | PASS |

All 26 tests pass: 13 witness verifications + 13 Groth16 proof verifications.

### What the Proof Proves

For each test case, the Groth16 proof demonstrates:

> "I know parameter values `(params...)` such that:
> 1. The selector matches the expected constant (e.g. `0xa9059cbb` for transfer)
> 2. `Poseidon(selector, params...) == calldataCommitment`
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
    ├── Verity/Intent/Example.lean   ERC-20 + ERC-721 examples + smoke tests
    │
    ├── Compiler/Circom.lean         Circom circuit generator
    ├── Compiler/ERC7730.lean        ERC-7730 clear-signing JSON generator
    │
    ├── Contracts/ERC20/Display.lean   Production ERC-20 intentSpec
    ├── Contracts/Ledger/Display.lean  Production Ledger intentSpec
    └── Contracts/ERC721/Display.lean  Production ERC-721 intentSpec
         │
         ├── .circom files → circom compiler → snarkjs → Groth16 proof
         └── .erc7730.json files → wallet clear-signing display
```

### CLI Integration

```bash
# Generate Circom circuits from a compiled module with IntentSpec:
verity-compiler --module Contracts.ERC20.ERC20 --circom-output artifacts/circom

# Generate ERC-7730 clear-signing JSON:
verity-compiler --module Contracts.ERC20.ERC20 --erc7730-output artifacts/erc7730

# Both can be combined:
verity-compiler --module Contracts.ERC20.ERC20 --circom-output artifacts/circom --erc7730-output artifacts/erc7730
```

The `--circom-output` flag triggers:
1. Loading the module's `intentSpec` constant
2. Validating against the `CompilationModel`
3. Computing selectors from the ABI
4. Writing one `.circom` file per intent binding

The `--erc7730-output` flag triggers:
1. Loading the module's `intentSpec` constant
2. Computing selectors from the ABI
3. Writing one `.erc7730.json` file per contract (ERC-7730 Structured Data Clear Signing Format)

## Phase 1 Status

- [x] `Verity/Intent/Types.lean` — AST types (Expr, Stmt, FnDecl, IntentSpec)
- [x] `Verity/Intent/Eval.lean` — Reference evaluator (total, fuel-based)
- [x] `Verity/Intent/Validate.lean` — Validates IntentSpec against CompilationModel
- [x] `Compiler/Circom.lean` — Circom circuit generator (Poseidon commitments, uint256 lo/hi)
- [x] `Compiler/CircomTest.lean` — Regression tests for generated Circom structure
- [x] `Compiler/ERC7730.lean` — ERC-7730 clear-signing JSON generator
- [x] `Compiler/ERC7730Test.lean` — Regression tests for generated ERC-7730 JSON
- [x] `--circom-output <dir>` CLI flag (wired through compile pipeline)
- [x] `--erc7730-output <dir>` CLI flag (wired through compile pipeline)
- [x] `Contracts/ERC20/Display.lean` — Production `intentSpec` for the ERC-20 contract
- [x] `Contracts/Ledger/Display.lean` — Production `intentSpec` for the Ledger contract
- [x] `Contracts/ERC721/Display.lean` — Production `intentSpec` for the ERC-721 contract
- [x] ERC-20 example with 5 test cases: transfer, approve, transferFrom (witness + proof)
- [x] Ledger example with 4 test cases: deposit, withdraw, transfer (witness + proof)
- [x] ERC-721 example with 4 test cases: approve, setApprovalForAll, transferFrom (witness + proof)
- [x] Groth16 proof generation and verification
- [x] `lake build` passes, `make check` passes

### Constraint Budget (Measured)

| Circuit | Non-linear Constraints | Notes |
|---------|----------------------|-------|
| ERC20 Transfer | 605 | 2 params, conditional |
| ERC20 Approve | 605 | 2 params, conditional |
| ERC20 TransferFrom | 653 | 3 params, conditional, Poseidon(5) |
| Ledger Deposit | 528 | 1 param, unconditional |
| Ledger Withdraw | 528 | 1 param, unconditional |
| Ledger Transfer | 605 | 2 params, conditional |
| ERC721 Approve | TBD | 2 params (addr+uint256), unconditional |
| ERC721 SetApprovalForAll | 507 | 2 params (addr+bool), conditional |
| ERC721 TransferFrom | TBD | 3 params (addr+addr+uint256), unconditional |

All well within the estimated ~700-1,500 range from the design document. Unconditional
circuits (deposit, withdraw) are smaller since they skip the IsEqual comparator. The
bool-conditioned `setApprovalForAll` circuit is the smallest since `bool` maps to a
single signal (no uint256 lo/hi splitting) and uses smaller Poseidon instances.
