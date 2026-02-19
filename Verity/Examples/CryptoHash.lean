/-
  CryptoHash: Demonstrates external function linking for cryptographic operations

  This contract shows how to use external cryptographic libraries (like Poseidon)
  with formally verified contract logic. The hash function uses a placeholder
  implementation for proofs, but will be replaced with the real Poseidon hash
  at compile time via external linking.
-/

import Verity.Core
import Verity.EVM.Uint256

namespace Verity.Examples.CryptoHash

open Verity
open Verity.EVM.Uint256

-- Storage: last computed hash
def lastHash : StorageSlot Uint256 := ⟨0⟩

/-!
## Placeholder hash function for proofs

In the EDSL, we use a simple placeholder (addition) for the hash function.
This allows us to prove properties about the contract logic without dealing
with complex cryptographic primitives.

At compile time, the real Poseidon hash is linked via `Expr.externalCall` in
the ContractSpec and the `--link` CLI flag. See `Compiler/Specs.lean` for the
ContractSpec that references `PoseidonT3_hash`/`PoseidonT4_hash`, and
`examples/external-libs/` for the Yul library files.

For now, we demonstrate the pattern with a simple addition-based placeholder.
-/

-- Placeholder hash: just add the inputs (for proving)
-- In production: linked via `lake exe verity-compiler --link examples/external-libs/PoseidonT3.yul`
def hashTwo (a b : Uint256) : Contract Uint256 := do
  return add a b

-- Placeholder hash for three inputs
-- In production: linked via `lake exe verity-compiler --link examples/external-libs/PoseidonT4.yul`
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
#eval (exampleUsage.run { defaultState with
  sender := 0xA11CE,
  thisAddress := 0xC2470
}).getValue?
-- Expected output: some 300 (with placeholder hash: 100 + 200)

end Verity.Examples.CryptoHash
