/-
  Finite set implementation for address tracking and sum properties.

  This module provides a finite set structure backed by duplicate-free
  lists, together with the operations and theorems needed for proving
  balance-conservation properties (e.g. Ledger sum proofs, issue #65).

  Key operations: empty, insert, sum.
  Key types: FiniteSet α, FiniteAddressSet.
  Key theorems: insert_of_not_mem, mem_elements_insert, sum_empty.
-/

import Verity.Core.Address

namespace Verity.Core

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

/-- Sum a function over all elements in the set -/
def sum [Add β] [OfNat β 0] (s : FiniteSet α) (f : α → β) : β :=
  s.elements.foldl (fun acc x => acc + f x) 0

/-!
### Theorems

Core lemmas for reasoning about finite set operations.
These are directly needed by Ledger sum proofs (#65).
-/

/-- The empty set has no members in its elements list -/
@[simp] theorem elements_empty : (empty : FiniteSet α).elements = [] := rfl

/-- Inserting a new element prepends it -/
theorem insert_of_not_mem [DecidableEq α] (a : α) (s : FiniteSet α) (h : a ∉ s.elements) :
    (s.insert a).elements = a :: s.elements := by
  unfold insert
  simp [dif_neg h]

/-- Membership in insert: either the new element or an existing one -/
theorem mem_elements_insert [DecidableEq α] (a b : α) (s : FiniteSet α) :
    a ∈ (s.insert b).elements ↔ a = b ∨ a ∈ s.elements := by
  unfold insert
  split
  · constructor
    · intro h; exact Or.inr h
    · intro h; cases h with
      | inl heq => subst heq; assumption
      | inr hmem => exact hmem
  · simp [List.mem_cons]

/-- Sum of empty set is zero -/
@[simp] theorem sum_empty [Add β] [OfNat β 0] (f : α → β) :
    (empty : FiniteSet α).sum f = 0 := rfl

end FiniteSet

/-- Finite set of addresses -/
structure FiniteAddressSet where
  addresses : FiniteSet Address
  deriving Repr

namespace FiniteAddressSet

/-- Create an empty address set -/
def empty : FiniteAddressSet :=
  ⟨FiniteSet.empty⟩

/-- Insert an address into the set -/
def insert (addr : Address) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.insert addr⟩

end FiniteAddressSet

end Verity.Core
