/-
  Minimal finite set implementation for address tracking.

  This module provides a simple finite set structure to enable
  proving sum properties over contract balances.

  This is a simplified implementation without all the helper theorems.
  Theorems will be added as needed during proof development.
-/

namespace DumbContracts.Core

/-- A finite set implemented as a list without duplicates -/
structure FiniteSet (α : Type) where
  elements : List α
  nodup : elements.Nodup
  deriving Repr

namespace FiniteSet

variable {α : Type}

/-- Create an empty finite set -/
def empty : FiniteSet α :=
  ⟨[], List.nodup_nil⟩

/-- Insert an element into the set (maintains no duplicates) -/
def insert [DecidableEq α] (a : α) (s : FiniteSet α) : FiniteSet α :=
  if h : a ∈ s.elements then
    s
  else
    ⟨a :: s.elements, List.nodup_cons.mpr ⟨h, s.nodup⟩⟩

/-- Get the size of the set -/
def card (s : FiniteSet α) : Nat :=
  s.elements.length

/-- Sum a function over all elements in the set -/
def sum [Add β] [OfNat β 0] (s : FiniteSet α) (f : α → β) : β :=
  s.elements.foldl (fun acc x => acc + f x) 0

end FiniteSet

/-- Finite set of addresses -/
structure FiniteAddressSet where
  addresses : FiniteSet String
  deriving Repr

namespace FiniteAddressSet

/-- Create an empty address set -/
def empty : FiniteAddressSet :=
  ⟨FiniteSet.empty⟩

/-- Insert an address into the set -/
def insert (addr : String) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.insert addr⟩

/-- Get the number of addresses in the set -/
def card (s : FiniteAddressSet) : Nat :=
  s.addresses.card

end FiniteAddressSet

end DumbContracts.Core
