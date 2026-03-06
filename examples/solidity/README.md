# Solidity Reference Implementations

These Solidity contracts serve as **reference implementations** for Verity's differential testing infrastructure. Each file corresponds to a formally verified Lean contract and is used to cross-validate the compiled Yul output against standard Solidity semantics.

## Contracts

| Solidity File | Lean EDSL | Lean Proofs | What it demonstrates |
|---------------|-----------|-------------|---------------------|
| `SimpleStorage.sol` | `Contracts/SimpleStorage/Contract.lean` | 20 theorems | Single storage slot (store/retrieve) |
| `Counter.sol` | `Contracts/Counter/Contract.lean` | 28 theorems | Increment/decrement with wrapping arithmetic |
| `SafeCounter.sol` | `Contracts/SafeCounter/Contract.lean` | 25 theorems | Overflow-safe arithmetic (reverts on overflow) |
| `Owned.sol` | `Contracts/Owned/Contract.lean` | 23 theorems | Access control (owner-only functions) |
| `OwnedCounter.sol` | `Contracts/OwnedCounter/Contract.lean` | 48 theorems | Combined access control + counter |
| `Ledger.sol` | `Contracts/Ledger/Contract.lean` | 33 theorems | Balance mapping (deposit/withdraw/transfer) |
| `SimpleToken.sol` | `Contracts/SimpleToken/Contract.lean` | 61 theorems | Token with mint/transfer + supply invariants |
| `(pending)` | `Contracts/ERC20/Contract.lean` | 19 theorems | ERC20 scaffold with initial read-state/spec bridge proofs |
| `(pending)` | `Contracts/ERC721/Contract.lean` | 11 theorems | ERC721 scaffold with ownership/approval read-state proof baseline |
| `ReentrancyExample.sol` | `Contracts/ReentrancyExample/Contract.lean` | 5 theorems | Reentrancy guard pattern |

## How Testing Works

Each contract has two types of Foundry tests:

- **Property tests** (`test/Property<Name>.t.sol`) — Deploy the compiled Yul and test properties derived from the Lean theorems
- **Differential tests** (`test/Differential<Name>.t.sol`) — Run the same transactions on both the Lean interpreter and the compiled EVM, comparing results

Run all tests:
```bash
FOUNDRY_PROFILE=difftest forge test
```

## Arithmetic Semantics

Solidity 0.8+ uses **checked arithmetic** (reverts on overflow), while the EVM and Lean `Uint256` use **wrapping arithmetic** (mod 2^256). The compiled Yul uses wrapping semantics, matching the Lean model. See `Counter.sol` vs `SafeCounter.sol` for the contrast.
