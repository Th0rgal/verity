/-
  Safe Multisig Base (Scaffold)

  This file is a minimal, compiling placeholder for the Safe base contract.
  The goal is to replace these definitions with the real EDSL implementation
  that mirrors the latest Safe base contract from safe-smart-account.

  TODO:
  - Implement core functions (setup, execTransaction, etc.) in EDSL
  - Align with Solidity ABI encoding rules
-/

import DumbContracts.Core

namespace DumbContracts.Examples.SafeMultisigBase

open DumbContracts

-- Safe base storage layout (linearized inheritance order).
-- NOTE: Some mappings use non-Address keys in Solidity; those are documented
-- in docs/safe-multisig-base/storage-layout.md and will be modeled later.
def singletonSlot : Nat := 0
def modulesSlot : Nat := 1
def ownersSlot : Nat := 2
def ownerCountSlot : Nat := 3
def thresholdSlot : Nat := 4
def nonceSlot : Nat := 5
def deprecatedDomainSeparatorSlot : Nat := 6
def signedMessagesSlot : Nat := 7
def approvedHashesSlot : Nat := 8

def singleton : StorageSlot Address := ⟨singletonSlot⟩
def modules : StorageSlot (Address → Uint256) := ⟨modulesSlot⟩
def owners : StorageSlot (Address → Uint256) := ⟨ownersSlot⟩
def ownerCount : StorageSlot Uint256 := ⟨ownerCountSlot⟩
def threshold : StorageSlot Uint256 := ⟨thresholdSlot⟩
def nonce : StorageSlot Uint256 := ⟨nonceSlot⟩
def deprecatedDomainSeparator : StorageSlot Uint256 := ⟨deprecatedDomainSeparatorSlot⟩
def signedMessages : StorageSlot (Address → Uint256) := ⟨signedMessagesSlot⟩
def approvedHashes : StorageSlot (Address → Uint256) := ⟨approvedHashesSlot⟩

-- Additional fixed storage slots (hashed constants from the Solidity source).
def guardStorageSlotHex : String :=
  "0x4a204f620c8c5ccdca3fd54d003badd85ba500436a431f0cbda4f558c93c34c8"
def fallbackHandlerStorageSlotHex : String :=
  "0x6c9a6c4a39284e37ed1cf53d337577d14212a4870fb976a4366c693b939918d5"
def moduleGuardStorageSlotHex : String :=
  "0xb104e0b93118902c651344349b610029d694cfdec91c589c91ebafbcd0289947"

/-- Placeholder constructor: Safe singleton initializes threshold = 1. -/
def constructor : Contract Unit := do
  setStorage threshold 1

/-- Placeholder getter: returns threshold. -/
def getThreshold : Contract Uint256 := do
  getStorage threshold

/-!
  Minimal EDSL skeletons for core Safe base entrypoints.

  These intentionally avoid full Safe semantics (modules, linked-list owners,
  signature checks, and gas refunding). They provide a compilable surface for
  the next proof iterations while keeping the ABI-level structure visible.
-/

/-- Placeholder setup: initializes ownerCount and threshold from inputs. -/
def setup (ownersList : List Address) (thresholdValue : Uint256) (to : Address)
    (data : Bytes) (fallbackHandler : Address) (paymentToken : Address)
    (payment : Uint256) (paymentReceiver : Address) : Contract Unit := do
  let _ := to
  let _ := data
  let _ := fallbackHandler
  let _ := paymentToken
  let _ := payment
  let _ := paymentReceiver
  let ownersLen : Uint256 := DumbContracts.Core.Uint256.ofNat ownersList.length
  require ((0 : Uint256) < ownersLen) "owners list empty"
  require ((0 : Uint256) < thresholdValue) "threshold zero"
  require (thresholdValue ≤ ownersLen) "threshold too high"
  -- TODO: initialize owners mapping, modules, fallback handler, and guard.
  -- TODO: handle setup call with `to` and `data`, and payment/refund logic.
  setStorage ownerCount ownersLen
  setStorage threshold thresholdValue
  pure ()

/-- Placeholder execTransaction: returns `true` without side effects. -/
def execTransaction (to : Address) (value : Uint256) (data : Bytes) (operation : Uint256)
    (safeTxGas : Uint256) (baseGas : Uint256) (gasPrice : Uint256)
    (gasToken : Address) (refundReceiver : Address) (signatures : Bytes) : Contract Bool := do
  let _ := to
  let _ := value
  let _ := data
  let _ := operation
  let _ := safeTxGas
  let _ := baseGas
  let _ := gasPrice
  let _ := gasToken
  let _ := refundReceiver
  let _ := signatures
  -- TODO: compute tx hash, check signatures, execute call, and pay refunds.
  pure true

end DumbContracts.Examples.SafeMultisigBase
