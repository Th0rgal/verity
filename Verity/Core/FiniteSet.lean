/-
  Finite set implementation for address tracking and sum properties.

  This module provides a finite set structure backed by duplicate-free
  lists, together with the operations and theorems needed for proving
  balance-conservation properties (e.g. Ledger sum proofs, issue #65).

  Key operations: empty, insert, remove, member, sum.
  Key types: FiniteSet α, FiniteAddressSet, FiniteNatSet.
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

/-- Union of two finite sets. -/
def union [DecidableEq α] (s t : FiniteSet α) : FiniteSet α :=
  t.elements.foldl (fun acc x => acc.insert x) s

/-- Intersection of two finite sets. -/
def inter [DecidableEq α] (s t : FiniteSet α) : FiniteSet α :=
  ⟨s.elements.filter (fun x => decide (x ∈ t.elements)), s.nodup.filter _⟩

/-- Propositional subset relation. -/
def subset (s t : FiniteSet α) : Prop :=
  ∀ x, x ∈ s → x ∈ t

/-- Boolean subset check. -/
def isSubset [DecidableEq α] (s t : FiniteSet α) : Bool :=
  s.elements.all (fun x => decide (x ∈ t.elements))

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

/-- Membership in intersection is conjunction of memberships. -/
@[simp] theorem mem_elements_inter [DecidableEq α] (a : α) (s t : FiniteSet α) :
    a ∈ (s.inter t).elements ↔ a ∈ s.elements ∧ a ∈ t.elements := by
  simp [FiniteSet.inter, and_left_comm, and_assoc, FiniteSet.mem]

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

/-- Union of two address sets. -/
def union (s t : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.union t.addresses⟩

/-- Intersection of two address sets. -/
def inter (s t : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.inter t.addresses⟩

/-- Propositional subset relation. -/
def subset (s t : FiniteAddressSet) : Prop :=
  s.addresses.subset t.addresses

/-- Boolean subset check. -/
def isSubset (s t : FiniteAddressSet) : Bool :=
  s.addresses.isSubset t.addresses

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

@[simp] theorem mem_inter (a : Address) (s t : FiniteAddressSet) :
    a ∈ s.inter t ↔ a ∈ s ∧ a ∈ t := by
  simpa [FiniteAddressSet.mem, FiniteAddressSet.inter] using
    (FiniteSet.mem_elements_inter a s.addresses t.addresses)

end FiniteAddressSet

/-- Finite set of natural numbers. -/
structure FiniteNatSet where
  nats : FiniteSet Nat
  deriving Repr

namespace FiniteNatSet

/-- Create an empty nat set. -/
def empty : FiniteNatSet :=
  ⟨FiniteSet.empty⟩

/-- Number of tracked nat values. -/
def card (s : FiniteNatSet) : Nat :=
  s.nats.card

/-- Nat membership proposition. -/
def mem (s : FiniteNatSet) (n : Nat) : Prop :=
  n ∈ s.nats

instance : Membership Nat FiniteNatSet where
  mem := mem

/-- Insert a nat into the set. -/
def insert (n : Nat) (s : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.insert n⟩

/-- Remove a nat from the set. -/
def remove (n : Nat) (s : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.remove n⟩

/-- Union of two nat sets. -/
def union (s t : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.union t.nats⟩

/-- Intersection of two nat sets. -/
def inter (s t : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.inter t.nats⟩

/-- Propositional subset relation. -/
def subset (s t : FiniteNatSet) : Prop :=
  s.nats.subset t.nats

/-- Boolean subset check. -/
def isSubset (s t : FiniteNatSet) : Bool :=
  s.nats.isSubset t.nats

/-- Boolean nat membership test. -/
def contains (n : Nat) (s : FiniteNatSet) : Bool :=
  s.nats.contains n

@[simp] theorem card_empty : (empty : FiniteNatSet).card = 0 := rfl

@[simp] theorem mem_def (n : Nat) (s : FiniteNatSet) :
    n ∈ s ↔ n ∈ s.nats.elements := Iff.rfl

@[simp] theorem mem_insert (a b : Nat) (s : FiniteNatSet) :
    a ∈ s.insert b ↔ a = b ∨ a ∈ s := by
  simpa [FiniteNatSet.mem] using FiniteSet.mem_elements_insert a b s.nats

@[simp] theorem contains_eq_true (n : Nat) (s : FiniteNatSet) :
    s.contains n = true ↔ n ∈ s := by
  simpa [FiniteNatSet.mem, FiniteNatSet.contains] using
    FiniteSet.contains_eq_true n s.nats

@[simp] theorem contains_eq_false (n : Nat) (s : FiniteNatSet) :
    s.contains n = false ↔ n ∉ s := by
  simpa [FiniteNatSet.mem, FiniteNatSet.contains] using
    FiniteSet.contains_eq_false n s.nats

@[simp] theorem mem_inter (a : Nat) (s t : FiniteNatSet) :
    a ∈ s.inter t ↔ a ∈ s ∧ a ∈ t := by
  simpa [FiniteNatSet.mem, FiniteNatSet.inter] using
    (FiniteSet.mem_elements_inter a s.nats t.nats)

end FiniteNatSet

end Verity.Core
