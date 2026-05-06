import Compiler.Proofs.IRGeneration.IRStorageWord

namespace Compiler.Proofs.IRGeneration

/-- Proof-side transaction context shared by IR and native-runtime harnesses. -/
structure IRTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Proof-side observable execution result shared by IR and native-runtime harnesses. -/
structure IRResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : IRStorageSlot → IRStorageWord
  finalMappings : Nat → Nat → IRStorageWord
  events : List (List Nat)

end Compiler.Proofs.IRGeneration
