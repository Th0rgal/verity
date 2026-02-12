# Safe Multisig Base ABI (Pinned)

This ABI snapshot is derived from the pinned interface
`contracts/interfaces/ISafe.sol` at v1.5.0 (commit `dc437e8`).

## Functions (ISafe)
- `setup(address[],uint256,address,bytes,address,address,uint256,address)`
- `execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)`
- `checkSignatures(address,bytes32,bytes)`
- `checkNSignatures(address,bytes32,bytes,uint256)`
- `approveHash(bytes32)`
- `domainSeparator()`
- `getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)`
- `VERSION()`
- `nonce()`
- `signedMessages(bytes32)`
- `approvedHashes(address,bytes32)`

## Events (ISafe)
- `SafeSetup(address,address[],uint256,address,address)`
- `ApproveHash(bytes32,address)`
- `SignMsg(bytes32)`
- `ExecutionFailure(bytes32,uint256)`
- `ExecutionSuccess(bytes32,uint256)`

## Notes
- This document only covers the ISafe surface. The Safe base contract also
  inherits interfaces from `INativeCurrencyPaymentFallback`, `IModuleManager`,
  `IGuardManager`, `IOwnerManager`, `IFallbackManager`, and `IStorageAccessible`.
- Additional ABI items from those interfaces will be added in a follow-up once
  they are pinned in `docs/safe-multisig-base/source/`.
