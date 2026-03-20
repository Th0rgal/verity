/-
  EVM-Compatible Int256 Operations

  Re-export core Int256 operations under Verity.EVM
  to keep existing imports stable.
-/

import Verity.Core.Int256

namespace Verity.EVM

abbrev MIN_INT256 : Int := Verity.Core.Int256.minValue
abbrev MAX_INT256 : Int := Verity.Core.Int256.maxValue

namespace Int256

abbrev modulus := Verity.Core.Int256.modulus
abbrev signBit := Verity.Core.Int256.signBit
abbrev minValue := Verity.Core.Int256.minValue
abbrev maxValue := Verity.Core.Int256.maxValue

abbrev ofUint256 := Verity.Core.Int256.ofUint256
abbrev ofInt := Verity.Core.Int256.ofInt
abbrev toUint256 := Verity.Core.Int256.toUint256
abbrev toInt := Verity.Core.Int256.toInt

abbrev add := Verity.Core.Int256.add
abbrev sub := Verity.Core.Int256.sub
abbrev mul := Verity.Core.Int256.mul
abbrev div := Verity.Core.Int256.div
abbrev mod := Verity.Core.Int256.mod
abbrev neg := Verity.Core.Int256.neg

abbrev isNeg := Verity.Core.Int256.isNeg
abbrev isZero := Verity.Core.Int256.isZero

theorem toInt_in_range (value : Verity.Core.Int256) :
    minValue ≤ (value : Int) ∧ (value : Int) ≤ maxValue :=
  Verity.Core.Int256.toInt_in_range value

@[simp] theorem div_by_zero (value : Verity.Core.Int256) :
    div value (0 : Verity.Core.Int256) = 0 :=
  Verity.Core.Int256.div_by_zero value

@[simp] theorem mod_by_zero (value : Verity.Core.Int256) :
    mod value (0 : Verity.Core.Int256) = 0 :=
  Verity.Core.Int256.mod_by_zero value

end Int256

end Verity.EVM
