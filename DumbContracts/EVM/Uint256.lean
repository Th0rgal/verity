/-
  EVM-Compatible Uint256 Operations

  Re-export core Uint256 operations under DumbContracts.EVM
  to keep existing imports stable.
-/

import DumbContracts.Core.Uint256

namespace DumbContracts.EVM

abbrev MAX_UINT256 : Nat := DumbContracts.Core.MAX_UINT256

namespace Uint256

abbrev add := DumbContracts.Core.Uint256.add
abbrev sub := DumbContracts.Core.Uint256.sub
abbrev mul := DumbContracts.Core.Uint256.mul
abbrev div := DumbContracts.Core.Uint256.div
abbrev mod := DumbContracts.Core.Uint256.mod

abbrev willAddOverflow := DumbContracts.Core.Uint256.willAddOverflow
abbrev willSubUnderflow := DumbContracts.Core.Uint256.willSubUnderflow
abbrev willMulOverflow := DumbContracts.Core.Uint256.willMulOverflow

theorem add_eq_of_lt {a b : Nat} (h : a + b < 2^256) : add a b = a + b :=
  DumbContracts.Core.Uint256.add_eq_of_lt h

theorem sub_eq_of_le {a b : Nat} (h : b ≤ a) : sub a b = a - b :=
  DumbContracts.Core.Uint256.sub_eq_of_le h

theorem sub_add_cancel_of_lt {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) :
  sub (add a b) b = a :=
  DumbContracts.Core.Uint256.sub_add_cancel_of_lt ha hb

end Uint256

end DumbContracts.EVM
