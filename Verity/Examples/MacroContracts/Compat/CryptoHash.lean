import Verity.Core
import Verity.Core.Semantics
import Verity.EVM.Uint256

namespace Verity.Examples.MacroContracts.Compat.CryptoHash

open Verity
open Verity.EVM.Uint256

abbrev lastHash : StorageSlot Uint256 := ⟨0⟩

def hashTwo (a b : Uint256) : Contract Uint256 := fun s =>
  ContractResult.success ((Verity.Env.ofWorld s).callOracle "PoseidonT3_hash" [a, b]) s

def hashThree (a b c : Uint256) : Contract Uint256 := fun s =>
  ContractResult.success ((Verity.Env.ofWorld s).callOracle "PoseidonT4_hash" [a, b, c]) s

def storeHashTwo (a b : Uint256) : Contract Unit := do
  let h ← hashTwo a b
  setStorage lastHash h

def storeHashThree (a b c : Uint256) : Contract Unit := do
  let h ← hashThree a b c
  setStorage lastHash h

def getLastHash : Contract Uint256 := do
  getStorage lastHash

end Verity.Examples.MacroContracts.Compat.CryptoHash
