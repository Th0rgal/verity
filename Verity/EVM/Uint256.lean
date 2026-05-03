/-
  EVM-Compatible Uint256 Operations

  Re-export core Uint256 operations under Verity.EVM
  to keep existing imports stable.
-/

import Verity.Core.Uint256

namespace Verity.EVM

abbrev MAX_UINT256 : Nat := Verity.Core.MAX_UINT256

namespace Uint256

abbrev modulus := Verity.Core.Uint256.modulus

abbrev add := Verity.Core.Uint256.add
abbrev sub := Verity.Core.Uint256.sub
abbrev mul := Verity.Core.Uint256.mul
abbrev pow := Verity.Core.Uint256.pow
abbrev div := Verity.Core.Uint256.div
abbrev mod := Verity.Core.Uint256.mod

abbrev and := Verity.Core.Uint256.and
abbrev or := Verity.Core.Uint256.or
abbrev xor := Verity.Core.Uint256.xor
abbrev not := Verity.Core.Uint256.not

abbrev shl := Verity.Core.Uint256.shl
abbrev shr := Verity.Core.Uint256.shr

abbrev willAddOverflow := Verity.Core.Uint256.willAddOverflow
abbrev willSubUnderflow := Verity.Core.Uint256.willSubUnderflow
abbrev willMulOverflow := Verity.Core.Uint256.willMulOverflow

theorem add_eq_of_lt {a b : Verity.Core.Uint256} (h : (a : Nat) + (b : Nat) < 2^256) :
  ((add a b : Verity.Core.Uint256) : Nat) = (a : Nat) + (b : Nat) :=
  Verity.Core.Uint256.add_eq_of_lt h

theorem sub_eq_of_le {a b : Verity.Core.Uint256} (h : (b : Nat) ≤ (a : Nat)) :
  ((sub a b : Verity.Core.Uint256) : Nat) = (a : Nat) - (b : Nat) :=
  Verity.Core.Uint256.sub_eq_of_le h

theorem sub_add_cancel (a b : Verity.Core.Uint256) :
  sub (add a b) b = a :=
  Verity.Core.Uint256.sub_add_cancel a b

end Uint256

end Verity.EVM
