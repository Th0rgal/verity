import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Mathlib.Data.Nat.Bitwise

namespace Compiler.Proofs.YulGeneration.Backends

private theorem uint256_size_eq_evmModulus :
    EvmYul.UInt256.size = Compiler.Constants.evmModulus := by
  decide

@[simp] theorem evalPureBuiltinViaEvmYulLean_iszero_native (a : Nat) :
    evalPureBuiltinViaEvmYulLean "iszero" [a] =
      some (if a % Compiler.Constants.evmModulus = 0 then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_lt_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "lt" [a, b] =
      some (if a % Compiler.Constants.evmModulus < b % Compiler.Constants.evmModulus then 1 else 0) := by
  rw [← uint256_size_eq_evmModulus]
  rfl

@[simp] theorem evalPureBuiltinViaEvmYulLean_and_native (a b : Nat) :
    evalPureBuiltinViaEvmYulLean "and" [a, b] =
      some ((a % Compiler.Constants.evmModulus) &&& (b % Compiler.Constants.evmModulus)) := by
  rw [← uint256_size_eq_evmModulus]
  change some (((Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size)) %
      EvmYul.UInt256.size)) =
    some (Nat.bitwise Bool.and (a % EvmYul.UInt256.size) (b % EvmYul.UInt256.size))
  congr 1
  rw [Nat.mod_eq_of_lt]
  exact Nat.bitwise_lt_two_pow (f := Bool.and) (n := 256)
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt a (by decide : 0 < EvmYul.UInt256.size))
    (by simpa [EvmYul.UInt256.size] using Nat.mod_lt b (by decide : 0 < EvmYul.UInt256.size))

end Compiler.Proofs.YulGeneration.Backends
