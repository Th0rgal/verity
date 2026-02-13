/-
  Formal specifications for Safe Multisig base operations (Scaffold).

  These specs are intentionally minimal placeholders. They will be
  expanded to match the Safe base contract behavior precisely.
-/

import DumbContracts.Core
import DumbContracts.Examples.SafeMultisigBase
import DumbContracts.Specs.SafeMultisigBase.Invariants

namespace DumbContracts.Specs.SafeMultisigBase

open DumbContracts
open DumbContracts.Examples.SafeMultisigBase

/-- Upstream Safe repo pin (for spec + bytecode parity). -/
def upstreamRepo : String := "safe-fndn/safe-smart-account"

/-- Upstream release tag targeted for this proof. -/
def upstreamTag : String := "v1.5.0"

/-- Upstream commit for the pinned Safe base contract. -/
def upstreamCommit : String := "dc437e8"

/-- Path to the base contract within the upstream repo. -/
def upstreamSafeSolPath : String := "contracts/Safe.sol"

/-- Base contract name in the upstream repo. -/
def upstreamBaseContractName : String := "Safe"

/-- Path to the ISafe interface within the upstream repo. -/
def upstreamISafeSolPath : String := "contracts/interfaces/ISafe.sol"

/-- Solidity pragma range in the pinned Safe base contract. -/
def upstreamPragmaRange : String := ">=0.7.0 <0.9.0"

/-- Safe contract version constant in the pinned source. -/
def upstreamVersionString : String := "1.5.0"

/-- SHA256 of the pinned Safe.sol source snapshot. -/
def upstreamSafeSolSha256 : String :=
  "4b54dce0ad9d9c1264ecd5c146c82b7bc17d24f981bd42525487be3bf6a40366"

/-- SHA256 of the pinned ISafe.sol interface source snapshot. -/
def upstreamISafeSolSha256 : String :=
  "ee9949b44f6b21f078e6b69dd927107f233fc38c1ea5b6d46b4618bf3a8af04d"

/-- ABI function signatures (ISafe interface only). -/
def abiFunctionSignatures : List String :=
  [ "setup(address[],uint256,address,bytes,address,address,uint256,address)"
  , "execTransaction(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes)"
  , "checkSignatures(address,bytes32,bytes)"
  , "checkNSignatures(address,bytes32,bytes,uint256)"
  , "approveHash(bytes32)"
  , "domainSeparator()"
  , "getTransactionHash(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,uint256)"
  , "VERSION()"
  , "nonce()"
  , "signedMessages(bytes32)"
  , "approvedHashes(address,bytes32)"
  , "enableModule(address)"
  , "disableModule(address,address)"
  , "execTransactionFromModule(address,uint256,bytes,uint8)"
  , "execTransactionFromModuleReturnData(address,uint256,bytes,uint8)"
  , "isModuleEnabled(address)"
  , "getModulesPaginated(address,uint256)"
  , "setModuleGuard(address)"
  , "setGuard(address)"
  , "addOwnerWithThreshold(address,uint256)"
  , "removeOwner(address,address,uint256)"
  , "swapOwner(address,address,address)"
  , "changeThreshold(uint256)"
  , "getThreshold()"
  , "isOwner(address)"
  , "getOwners()"
  , "setFallbackHandler(address)"
  , "getStorageAt(uint256,uint256)"
  , "simulateAndRevert(address,bytes)"
  , "isValidSignature(bytes32,bytes)"
  ]

/-- ABI event signatures (ISafe interface only). -/
def abiEventSignatures : List String :=
  [ "SafeSetup(address,address[],uint256,address,address)"
  , "ApproveHash(bytes32,address)"
  , "SignMsg(bytes32)"
  , "ExecutionFailure(bytes32,uint256)"
  , "ExecutionSuccess(bytes32,uint256)"
  , "EnabledModule(address)"
  , "DisabledModule(address)"
  , "ExecutionFromModuleSuccess(address)"
  , "ExecutionFromModuleFailure(address)"
  , "ChangedModuleGuard(address)"
  , "ChangedGuard(address)"
  , "AddedOwner(address)"
  , "RemovedOwner(address)"
  , "ChangedThreshold(uint256)"
  , "ChangedFallbackHandler(address)"
  , "SafeReceived(address,uint256)"
  ]

/-- Constructor spec: Safe singleton initializes threshold = 1 and preserves all other state. -/
def constructor_spec (s s' : ContractState) : Prop :=
  s'.storage threshold.slot = 1 ∧
  (∀ slot : Nat, slot ≠ threshold.slot → s'.storage slot = s.storage slot) ∧
  s'.storageAddr = s.storageAddr ∧
  s'.storageMap = s.storageMap ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Getter spec: threshold equals current storage slot. -/
def getThreshold_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage threshold.slot

/-- Placeholder setup spec: updates ownerCount and threshold, leaves other state unchanged. -/
def setup_spec (ownersList : List Address) (thresholdValue : Uint256)
    (fallbackHandler : Address)
    (s s' : ContractState) : Prop :=
  let ownersLen : Uint256 := DumbContracts.Core.Uint256.ofNat ownersList.length
  s.storage threshold.slot = 0 ∧
  ownersList.Nodup ∧
  (0 : Uint256) < ownersLen ∧
  (0 : Uint256) < thresholdValue ∧
  thresholdValue ≤ ownersLen ∧
  (∀ owner ∈ ownersList,
    owner ≠ zeroAddress ∧
    owner ≠ ownersSentinel ∧
    owner ≠ s.thisAddress ∧
    s.storageMap owners.slot owner = 0) ∧
  ownersLinkedList s' ownersList ∧
  (∀ addr : Address,
    addr ≠ ownersSentinel →
    addr ∉ ownersList →
    s'.storageMap owners.slot addr = s.storageMap owners.slot addr) ∧
  s'.storageMap modules.slot modulesSentinel = encodeAddress modulesSentinel ∧
  (∀ addr : Address, addr ≠ modulesSentinel →
    s'.storageMap modules.slot addr = s.storageMap modules.slot addr) ∧
  (if fallbackHandler = zeroAddress then
    s'.storage fallbackHandlerStorage.slot = s.storage fallbackHandlerStorage.slot
  else
    s'.storage fallbackHandlerStorage.slot = encodeAddress fallbackHandler) ∧
  s'.storage guardStorage.slot = 0 ∧
  s'.storage moduleGuardStorage.slot = 0 ∧
  s'.storage ownerCount.slot = ownersLen ∧
  s'.storage threshold.slot = thresholdValue ∧
  (∀ slot : Nat,
    slot ≠ ownerCount.slot ∧
    slot ≠ threshold.slot ∧
    slot ≠ fallbackHandlerStorage.slot ∧
    slot ≠ guardStorage.slot ∧
    slot ≠ moduleGuardStorage.slot →
    s'.storage slot = s.storage slot) ∧
  (∀ slot : Nat, slot ≠ owners.slot ∧ slot ≠ modules.slot →
    s'.storageMap slot = s.storageMap slot) ∧
  s'.storageAddr = s.storageAddr ∧
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Placeholder execTransaction spec: returns true and preserves state. -/
def execTransaction_spec (result : Bool) (s s' : ContractState) : Prop :=
  result = true ∧
  s' = s

end DumbContracts.Specs.SafeMultisigBase
