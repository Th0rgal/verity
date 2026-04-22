namespace Compiler.Proofs.YulGeneration

/-! Shared state structures for the reference-oracle Yul runtime. -/

structure YulState where
  vars : List (String × Nat)
  storage : Nat → Nat
  transientStorage : Nat → Nat := fun _ => 0
  memory : Nat → Nat
  calldata : List Nat
  selector : Nat
  returnValue : Option Nat
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  events : List (List Nat) := []
  deriving Nonempty

end Compiler.Proofs.YulGeneration
