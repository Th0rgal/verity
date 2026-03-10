# Solidity Reference Implementations

These Solidity contracts serve as **reference implementations** for Verity's differential testing infrastructure. Each file corresponds to a Lean contract with contract/spec proofs, and is used to cross-validate the compiled Yul output against standard Solidity semantics.

Important boundary: not every listed Lean contract currently has a dedicated whole-contract theorem showing `EDSL semantics = compiled Yul semantics`. For several contracts, the repo currently relies on differential tests plus partial/generic compiler proofs rather than a contract-specific end-to-end bridge theorem. See [`docs/VERIFICATION_STATUS.md`](../../docs/VERIFICATION_STATUS.md) for the exact current split.

## Contracts

| Solidity File | Lean EDSL | Lean Proofs | What it demonstrates |
|---------------|-----------|-------------|---------------------|
| `SimpleStorage.sol` | `Contracts/SimpleStorage/SimpleStorage.lean` | 20 theorems | Single storage slot (store/retrieve) |
| `Counter.sol` | `Contracts/Counter/Counter.lean` | 28 theorems | Increment/decrement with wrapping arithmetic |
| `SafeCounter.sol` | `Contracts/SafeCounter/SafeCounter.lean` | 25 theorems | Overflow-safe arithmetic (reverts on overflow) |
| `Owned.sol` | `Contracts/Owned/Owned.lean` | 23 theorems | Access control (owner-only functions) |
| `OwnedCounter.sol` | `Contracts/OwnedCounter/OwnedCounter.lean` | 48 theorems | Combined access control + counter |
| `Ledger.sol` | `Contracts/Ledger/Ledger.lean` | 33 theorems | Balance mapping (deposit/withdraw/transfer) |
| `Vault.sol` | `Contracts/Vault/Vault.lean` | scaffolding | Minimal ERC4626-style vault with 1:1 share accounting |
| `SimpleToken.sol` | `Contracts/SimpleToken/SimpleToken.lean` | 61 theorems | Token with mint/transfer + supply invariants |
| `(pending)` | `Contracts/ERC20/ERC20.lean` | 19 theorems | ERC20 scaffold with initial read-state/spec bridge proofs |
| `(pending)` | `Contracts/ERC721/ERC721.lean` | 11 theorems | ERC721 scaffold with ownership/approval read-state proof baseline |
| `ReentrancyExample.sol` | `Contracts/ReentrancyExample/Contract.lean` | 5 theorems | Reentrancy guard pattern; semantic case study rather than current `verity_contract` bridge example |

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
