/-
  Core Address Type

  This module provides a proper 160-bit address type for EVM addresses.
  Addresses are bounded natural numbers (val < 2^160), matching EVM
  semantics exactly. This eliminates the unsound `addressToNat_injective`
  axiom that existed when Address was an alias for String.

  Design follows the Uint256 pattern in Core/Uint256.lean.
-/

namespace Verity.Core

-- EVM address space is 160 bits
def ADDRESS_MODULUS : Nat := 2^160

structure Address where
  val : Nat
  isLt : val < ADDRESS_MODULUS
  deriving DecidableEq

namespace Address

def modulus : Nat := ADDRESS_MODULUS

theorem modulus_pos : 0 < modulus := by
  have h2 : (0 : Nat) < (2 : Nat) := by decide
  have h : 0 < (2 : Nat) ^ 160 := Nat.pow_pos h2
  simp [modulus]
  exact h

def ofNat (n : Nat) : Address :=
  ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Address n := ⟨ofNat n⟩
instance : Inhabited Address := ⟨ofNat 0⟩
instance : Repr Address := ⟨fun a _ => repr a.val⟩
instance : Coe Address Nat := ⟨Address.val⟩

@[simp] theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl

@[ext] theorem ext {a b : Address} (h : a.val = b.val) : a = b := by
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases h
      have : ha = hb := by
        apply Subsingleton.elim
      cases this
      rfl

-- BEq instance derived from DecidableEq
instance : BEq Address := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq Address where
  eq_of_beq {a b} h := by
    simp only [BEq.beq] at h
    exact of_decide_eq_true h
  rfl {a} := by
    show decide (a = a) = true
    exact decide_eq_true rfl

-- Address.toNat is just val (coercion)
def toNat (a : Address) : Nat := a.val

@[simp] theorem toNat_ofNat (n : Nat) : (ofNat n).toNat = n % modulus := rfl
@[simp] theorem val_zero : (0 : Address).val = 0 := by
  change (ofNat 0).val = 0
  simp [ofNat]

@[simp] theorem ofNat_zero : ofNat 0 = (0 : Address) := rfl

-- Injectivity is now trivially provable (was an axiom!)
theorem toNat_injective (a b : Address) (h : a.toNat = b.toNat) : a = b :=
  ext h

-- Address value is always less than modulus
theorem val_lt_modulus (a : Address) : a.val < modulus := a.isLt

-- Mod identity
@[simp] theorem val_mod_modulus (a : Address) : a.val % modulus = a.val :=
  Nat.mod_eq_of_lt a.isLt

-- BEq self
@[simp] theorem beq_self (a : Address) : (a == a) = true := by
  simp [BEq.beq]

-- Ne implies beq false
theorem beq_false_of_ne (a b : Address) (h : a ≠ b) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

-- toNat respects inequality
theorem toNat_ne_of_ne (a b : Address) (h : a ≠ b) : a.toNat ≠ b.toNat := by
  intro h_nat
  exact h (toNat_injective a b h_nat)

-- toNat beq false when addresses differ
theorem toNat_beq_false_of_ne (a b : Address) (h : a ≠ b) :
    (a.toNat == b.toNat) = false :=
  beq_eq_false_iff_ne.mpr (toNat_ne_of_ne a b h)

end Address

end Verity.Core
