/-
  CryptoHash: Demonstrates external function linking for cryptographic operations

  This contract shows how to use external cryptographic libraries (like Poseidon)
  with formally verified contract logic. The hash function uses a placeholder
  implementation for proofs, but will be replaced with the real Poseidon hash
  at compile time via external linking.
-/

import DumbContracts.Core
import DumbContracts.EVM.Uint256

namespace DumbContracts.Examples.CryptoHash

open DumbContracts
open DumbContracts.EVM.Uint256

-- Storage: last computed hash
def lastHash : StorageSlot Uint256 := ⟨0⟩

/-!
## Placeholder hash function for proofs

In the EDSL, we use a simple placeholder (addition) for the hash function.
This allows us to prove properties about the contract logic without dealing
with complex cryptographic primitives.

At compile time, this will be replaced with a call to an external Poseidon
hash implementation via the @[extern] attribute (to be added in future).

For now, we demonstrate the pattern with a simple addition-based placeholder.
-/

-- Placeholder hash: just add the inputs (for proving)
-- In production: @[extern "PoseidonT3_hash"] would replace this
def hashTwo (a b : Uint256) : Contract Uint256 := do
  return add a b

-- Placeholder hash for three inputs
-- In production: @[extern "PoseidonT4_hash"]
def hashThree (a b c : Uint256) : Contract Uint256 := do
  return add (add a b) c

-- Store hash of two values
def storeHashTwo (a b : Uint256) : Contract Unit := do
  let h ← hashTwo a b
  setStorage lastHash h

-- Store hash of three values
def storeHashThree (a b c : Uint256) : Contract Unit := do
  let h ← hashThree a b c
  setStorage lastHash h

-- Get last hash
def getLastHash : Contract Uint256 := do
  getStorage lastHash

-- Example usage
def exampleUsage : Contract Uint256 := do
  storeHashTwo 100 200
  getLastHash

-- Evaluate the example
#eval (exampleUsage.run {
  storage := fun _ => 0,
  storageAddr := fun _ => "",
  storageMap := fun _ _ => 0,
  sender := "0xAlice",
  thisAddress := "0xCryptoHash",
  msgValue := 0,
  blockTimestamp := 0,
  knownAddresses := fun _ => DumbContracts.Core.FiniteAddressSet.empty
}).getValue?
-- Expected output: some 300 (with placeholder hash: 100 + 200)

end DumbContracts.Examples.CryptoHash
