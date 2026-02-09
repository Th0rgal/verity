import DumbContracts.Lang
import DumbContracts.Semantics

namespace DumbContracts.Examples

open DumbContracts.Lang
open DumbContracts.Semantics
open DumbContracts

/-- Storage slots for a tiny ERC20-style layout. -/

def balanceSlot (addr : Nat) : Nat :=
  1000 + addr

def totalSupplySlot : Nat :=
  0

def totalSupply (s : Store) : Nat :=
  s totalSupplySlot

def setBalance (s : Store) (addr val : Nat) : Store :=
  updateStore s (balanceSlot addr) val

def sum2 (s : Store) (a b : Nat) : Nat :=
  s (balanceSlot a) + s (balanceSlot b)

/-- Sum of balances for a list of addresses. -/

def sumBalances (s : Store) : List Nat -> Nat
  | [] => 0
  | a :: rest => s (balanceSlot a) + sumBalances rest

-- Common store lemmas.

theorem updateStore_same (s : Store) (k : Nat) :
    updateStore s k (s k) = s := by
  funext a
  by_cases h : a = k
  · simp [updateStore, updateNat, h]
  · simp [updateStore, updateNat, h]

theorem updateStore_shadow (s : Store) (k v1 v2 : Nat) :
    updateStore (updateStore s k v1) k v2 = updateStore s k v2 := by
  funext a
  by_cases h : a = k
  · simp [updateStore, updateNat, h]
  · simp [updateStore, updateNat, h]

-- Slot distinctness.

theorem balanceSlot_ne (a b : Nat) (h : a ≠ b) : balanceSlot a ≠ balanceSlot b := by
  intro h'
  apply h
  exact Nat.add_left_cancel h'

theorem balanceSlot_ne_total (addr : Nat) : balanceSlot addr ≠ totalSupplySlot := by
  simp [balanceSlot, totalSupplySlot]

end DumbContracts.Examples
