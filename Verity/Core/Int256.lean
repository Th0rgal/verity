import Verity.Core.Uint256

namespace Verity.Core

structure Int256 where
  word : Uint256
  deriving DecidableEq

namespace Int256

def modulus : Nat := Uint256.modulus

def signBit : Nat := 2 ^ 255

def minValue : Int := -Int.ofNat signBit

def maxValue : Int := Int.ofNat signBit - 1

def ofUint256 (value : Uint256) : Int256 := ⟨value⟩

def toUint256 (value : Int256) : Uint256 := value.word

def toInt (value : Int256) : Int :=
  let raw : Nat := value.word
  if raw < signBit then
    Int.ofNat raw
  else
    Int.ofNat raw - Int.ofNat modulus

def ofInt (value : Int) : Int256 :=
  if value < 0 then
    ofUint256 <| Uint256.ofNat (modulus - (Int.natAbs value % modulus))
  else
    ofUint256 <| Uint256.ofNat value.toNat

instance : Inhabited Int256 := ⟨ofUint256 0⟩
instance : Repr Int256 := ⟨fun value _ => repr value.toInt⟩
instance : OfNat Int256 n := ⟨ofUint256 n⟩
instance : Coe Int256 Uint256 := ⟨toUint256⟩
instance : Coe Int256 Int := ⟨toInt⟩
instance : Coe Uint256 Int256 := ⟨ofUint256⟩

@[simp] theorem toUint256_ofUint256 (value : Uint256) :
    toUint256 (ofUint256 value) = value := rfl

@[simp] theorem ofUint256_toUint256 (value : Uint256) :
    (ofUint256 value : Int256).toUint256 = value := rfl

@[simp] theorem ofInt_nonneg (value : Int) (h : ¬ value < 0) :
    (ofInt value).toUint256 = Uint256.ofNat value.toNat := by
  simp [ofInt, h]

@[simp] theorem ofInt_neg (value : Int) (h : value < 0) :
    (ofInt value).toUint256 = Uint256.ofNat (modulus - (Int.natAbs value % modulus)) := by
  simp [ofInt, h]

@[simp] theorem toInt_of_lt_signBit {value : Int256} (h : value.word.val < signBit) :
    (value : Int) = Int.ofNat value.word.val := by
  simp [Int256.toInt, h]

@[simp] theorem toInt_of_ge_signBit {value : Int256} (h : signBit ≤ value.word.val) :
    (value : Int) = Int.ofNat value.word.val - Int.ofNat modulus := by
  have h' : ¬ value.word.val < signBit := Nat.not_lt_of_ge h
  simp [Int256.toInt, h']

theorem signBit_lt_modulus : signBit < modulus := by
  native_decide

theorem modulus_eq_two_mul_signBit : modulus = 2 * signBit := by
  native_decide

theorem minValue_le (value : Int256) : minValue ≤ (value : Int) := by
  by_cases h : value.word.val < signBit
  · simp [toInt_of_lt_signBit h, minValue]
  · have hge : signBit ≤ value.word.val := Nat.le_of_not_lt h
    have hraw : value.word.val < modulus := value.word.isLt
    simp [toInt_of_ge_signBit hge, minValue, modulus_eq_two_mul_signBit]
    omega

theorem le_maxValue (value : Int256) : (value : Int) ≤ maxValue := by
  by_cases h : value.word.val < signBit
  · simp [toInt_of_lt_signBit h, maxValue]
    omega
  · have hge : signBit ≤ value.word.val := Nat.le_of_not_lt h
    have hraw : value.word.val < modulus := value.word.isLt
    have hneg : (value : Int) ≤ -1 := by
      simp [toInt_of_ge_signBit hge]
      omega
    have hs : (0 : Int) ≤ Int.ofNat signBit := by
      simp
    have hmax : (-1 : Int) ≤ maxValue := by
      simp [maxValue]
      omega
    omega

theorem toInt_in_range (value : Int256) : minValue ≤ (value : Int) ∧ (value : Int) ≤ maxValue := by
  exact ⟨minValue_le value, le_maxValue value⟩

@[simp] theorem val_zero : ((0 : Int256) : Int) = 0 := by
  native_decide

@[simp] theorem val_one : ((1 : Int256) : Int) = 1 := by
  native_decide

def add (a b : Int256) : Int256 := ofUint256 (a.word + b.word)

def sub (a b : Int256) : Int256 := ofUint256 (a.word - b.word)

def mul (a b : Int256) : Int256 := ofUint256 (a.word * b.word)

def neg (value : Int256) : Int256 := ofUint256 <| Uint256.ofNat (modulus - value.word.val)

private def signedAbsNat (value : Int) : Nat := Int.natAbs value

def div (a b : Int256) : Int256 :=
  let lhs : Int := a
  let rhs : Int := b
  if rhs = 0 then
    0
  else
    let quotient := signedAbsNat lhs / signedAbsNat rhs
    let sameSign := (lhs < 0) == (rhs < 0)
    if sameSign then
      ofInt (Int.ofNat quotient)
    else
      ofInt (-Int.ofNat quotient)

def mod (a b : Int256) : Int256 :=
  let lhs : Int := a
  let rhs : Int := b
  if rhs = 0 then
    0
  else
    let remainder := signedAbsNat lhs % signedAbsNat rhs
    if lhs < 0 then
      ofInt (-Int.ofNat remainder)
    else
      ofInt (Int.ofNat remainder)

def isNeg (value : Int256) : Bool :=
  signBit ≤ value.word.val

def isZero (value : Int256) : Bool :=
  value.word.val = 0

instance : LT Int256 := ⟨fun a b => (a : Int) < (b : Int)⟩
instance : LE Int256 := ⟨fun a b => (a : Int) ≤ (b : Int)⟩
instance (a b : Int256) : Decidable (a < b) := by
  change Decidable ((a : Int) < (b : Int))
  infer_instance
instance (a b : Int256) : Decidable (a ≤ b) := by
  change Decidable ((a : Int) ≤ (b : Int))
  infer_instance

@[simp] theorem le_def (a b : Int256) : (a ≤ b) = ((a : Int) ≤ (b : Int)) := rfl
@[simp] theorem lt_def (a b : Int256) : (a < b) = ((a : Int) < (b : Int)) := rfl

instance : HAdd Int256 Int256 Int256 := ⟨add⟩
instance : HSub Int256 Int256 Int256 := ⟨sub⟩
instance : HMul Int256 Int256 Int256 := ⟨mul⟩
instance : HDiv Int256 Int256 Int256 := ⟨div⟩
instance : HMod Int256 Int256 Int256 := ⟨mod⟩
instance : Add Int256 := ⟨add⟩
instance : Sub Int256 := ⟨sub⟩
instance : Mul Int256 := ⟨mul⟩
instance : Div Int256 := ⟨div⟩
instance : Mod Int256 := ⟨mod⟩
instance : Neg Int256 := ⟨neg⟩

@[simp] theorem add_toUint256 (a b : Int256) :
    (a + b).toUint256 = a.toUint256 + b.toUint256 := rfl

@[simp] theorem sub_toUint256 (a b : Int256) :
    (a - b).toUint256 = a.toUint256 - b.toUint256 := rfl

@[simp] theorem mul_toUint256 (a b : Int256) :
    (a * b).toUint256 = a.toUint256 * b.toUint256 := rfl

@[simp] theorem neg_toUint256 (value : Int256) :
    (-value).toUint256 = Uint256.ofNat (modulus - value.word.val) := rfl

@[simp] theorem div_by_zero (value : Int256) : value / (0 : Int256) = 0 := by
  simp [HDiv.hDiv, Int256.div]

@[simp] theorem mod_by_zero (value : Int256) : value % (0 : Int256) = 0 := by
  simp [HMod.hMod, Int256.mod]

@[ext] theorem ext {a b : Int256} (h : a.word = b.word) : a = b := by
  cases a
  cases b
  cases h
  rfl

section Examples

example : (((Int256.ofUint256 (Uint256.ofNat (modulus - 1)) : Int256) : Int)) = -1 := by
  native_decide

example : (((Int256.ofUint256 (Uint256.ofNat signBit) : Int256) : Int)) = minValue := by
  native_decide

example : (Int256.ofInt (-1)).toUint256 = Uint256.ofNat (modulus - 1) := by
  native_decide

example : (Int256.ofInt minValue).toUint256 = Uint256.ofNat signBit := by
  native_decide

example : (-(Int256.ofInt minValue) : Int256) = Int256.ofInt minValue := by
  native_decide

example : (Int256.ofInt (-7) / Int256.ofInt 3 : Int256) = Int256.ofInt (-2) := by
  native_decide

example : (Int256.ofInt 7 / Int256.ofInt (-3) : Int256) = Int256.ofInt (-2) := by
  native_decide

example : (Int256.ofInt (-7) % Int256.ofInt 3 : Int256) = Int256.ofInt (-1) := by
  native_decide

example : (Int256.ofInt 7 % Int256.ofInt (-3) : Int256) = Int256.ofInt 1 := by
  native_decide

example : (Int256.ofInt (-7) / (0 : Int256) : Int256) = 0 := by
  native_decide

example : (Int256.ofInt (-7) % (0 : Int256) : Int256) = 0 := by
  native_decide

example : (Int256.ofInt minValue / Int256.ofInt (-1) : Int256) = Int256.ofInt minValue := by
  native_decide

example : (Int256.ofInt maxValue + 1 : Int256) = Int256.ofInt minValue := by
  native_decide

end Examples

end Int256

end Verity.Core
