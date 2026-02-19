/-
  Finite set implementation for address tracking and sum properties.

  This module provides a finite set structure backed by duplicate-free
  lists, together with the operations and theorems needed for proving
  balance-conservation properties (e.g. Ledger sum proofs, issue #65).

  Key operations: empty, insert, remove, member, sum.
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

/-- Number of elements in the set. -/
def card (s : FiniteSet α) : Nat :=
  s.elements.length

/-- Membership predicate for finite sets. -/
def mem (s : FiniteSet α) (a : α) : Prop :=
  a ∈ s.elements

instance : Membership α (FiniteSet α) where
  mem := mem

/-- Insert an element into the set (maintains no duplicates) -/
def insert [DecidableEq α] (a : α) (s : FiniteSet α) : FiniteSet α :=
  if h : a ∈ s.elements then
    s
  else
    ⟨a :: s.elements, List.nodup_cons.mpr ⟨h, s.nodup⟩⟩

/-- Remove an element from the set (maintains no duplicates). -/
def remove [DecidableEq α] (a : α) (s : FiniteSet α) : FiniteSet α :=
  ⟨s.elements.erase a, s.nodup.erase a⟩

/-- Boolean membership test for finite sets. -/
def contains [DecidableEq α] (a : α) (s : FiniteSet α) : Bool :=
  decide (a ∈ s.elements)

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

/-- The cardinality of the empty set is zero. -/
@[simp] theorem card_empty : (empty : FiniteSet α).card = 0 := rfl

/-- Membership in set notation is list membership on elements. -/
@[simp] theorem mem_def (a : α) (s : FiniteSet α) : a ∈ s ↔ a ∈ s.elements := Iff.rfl

/-- Membership in the empty set is false. -/
@[simp] theorem not_mem_empty (a : α) : a ∉ (empty : FiniteSet α) := by
  simp [FiniteSet.mem]

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

/-- `contains` reflects propositional membership. -/
@[simp] theorem contains_eq_true [DecidableEq α] (a : α) (s : FiniteSet α) :
    s.contains a = true ↔ a ∈ s := by
  unfold contains
  simp [FiniteSet.mem]

/-- `contains = false` iff the element is not a member. -/
@[simp] theorem contains_eq_false [DecidableEq α] (a : α) (s : FiniteSet α) :
    s.contains a = false ↔ a ∉ s := by
  unfold contains
  simp [FiniteSet.mem]

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

/-- Number of tracked addresses. -/
def card (s : FiniteAddressSet) : Nat :=
  s.addresses.card

/-- Address membership proposition. -/
def mem (s : FiniteAddressSet) (addr : Address) : Prop :=
  addr ∈ s.addresses

instance : Membership Address FiniteAddressSet where
  mem := mem

/-- Insert an address into the set -/
def insert (addr : Address) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.insert addr⟩

/-- Remove an address from the set. -/
def remove (addr : Address) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.remove addr⟩

/-- Boolean address membership test. -/
def contains (addr : Address) (s : FiniteAddressSet) : Bool :=
  s.addresses.contains addr

@[simp] theorem card_empty : (empty : FiniteAddressSet).card = 0 := rfl

@[simp] theorem mem_def (addr : Address) (s : FiniteAddressSet) :
    addr ∈ s ↔ addr ∈ s.addresses.elements := Iff.rfl

@[simp] theorem mem_insert (a b : Address) (s : FiniteAddressSet) :
    a ∈ s.insert b ↔ a = b ∨ a ∈ s := by
  simpa [FiniteAddressSet.mem] using FiniteSet.mem_elements_insert a b s.addresses

@[simp] theorem contains_eq_true (addr : Address) (s : FiniteAddressSet) :
    s.contains addr = true ↔ addr ∈ s := by
  simpa [FiniteAddressSet.mem, FiniteAddressSet.contains] using
    FiniteSet.contains_eq_true addr s.addresses

@[simp] theorem contains_eq_false (addr : Address) (s : FiniteAddressSet) :
    s.contains addr = false ↔ addr ∉ s := by
  simpa [FiniteAddressSet.mem, FiniteAddressSet.contains] using
    FiniteSet.contains_eq_false addr s.addresses

end FiniteAddressSet

end Verity.Core
