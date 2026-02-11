/-
  EVM-Compatible Uint256 Operations

  Re-export core Uint256 operations under DumbContracts.EVM
  to keep existing imports stable.
-/

import DumbContracts.Core.Uint256

namespace DumbContracts.EVM

abbrev MAX_UINT256 : Nat := DumbContracts.Core.MAX_UINT256

namespace Uint256

abbrev modulus := DumbContracts.Core.Uint256.modulus

abbrev add := DumbContracts.Core.Uint256.add
abbrev sub := DumbContracts.Core.Uint256.sub
abbrev mul := DumbContracts.Core.Uint256.mul
abbrev div := DumbContracts.Core.Uint256.div
abbrev mod := DumbContracts.Core.Uint256.mod

abbrev and := DumbContracts.Core.Uint256.and
abbrev or := DumbContracts.Core.Uint256.or
abbrev xor := DumbContracts.Core.Uint256.xor
abbrev not := DumbContracts.Core.Uint256.not

abbrev shl := DumbContracts.Core.Uint256.shl
abbrev shr := DumbContracts.Core.Uint256.shr

abbrev willAddOverflow := DumbContracts.Core.Uint256.willAddOverflow
abbrev willSubUnderflow := DumbContracts.Core.Uint256.willSubUnderflow
abbrev willMulOverflow := DumbContracts.Core.Uint256.willMulOverflow

theorem add_eq_of_lt {a b : DumbContracts.Core.Uint256} (h : (a : Nat) + (b : Nat) < 2^256) :
  ((add a b : DumbContracts.Core.Uint256) : Nat) = (a : Nat) + (b : Nat) :=
  DumbContracts.Core.Uint256.add_eq_of_lt h

theorem sub_eq_of_le {a b : DumbContracts.Core.Uint256} (h : (b : Nat) ≤ (a : Nat)) :
  ((sub a b : DumbContracts.Core.Uint256) : Nat) = (a : Nat) - (b : Nat) :=
  DumbContracts.Core.Uint256.sub_eq_of_le h

theorem sub_add_cancel (a b : DumbContracts.Core.Uint256) :
  sub (add a b) b = a :=
  DumbContracts.Core.Uint256.sub_add_cancel a b

theorem sub_add_cancel_of_lt {a b : DumbContracts.Core.Uint256}
  (_ha : (a : Nat) < 2^256) (_hb : (b : Nat) < 2^256) :
  sub (add a b) b = a :=
  DumbContracts.Core.Uint256.sub_add_cancel a b

end Uint256

end DumbContracts.EVM
