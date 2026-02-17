/-
  Finite set implementation for address tracking and sum properties.

  This module provides a finite set structure backed by duplicate-free
  lists, together with the operations and theorems needed for proving
  balance-conservation properties (e.g. Ledger sum proofs, issue #65).

  Key operations: empty, insert, remove, contains, union, inter, filter, sum,
                  subset, member, toList, fromList.
  Key types: FiniteSet α, FiniteAddressSet, FiniteNatSet.
  Key theorems: insert_of_mem, insert_of_not_mem, mem_elements_insert,
                card_insert_of_not_mem, card_insert_of_mem, sum_empty.
-/

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

/-- Check if an element is in the set -/
def contains [DecidableEq α] (a : α) (s : FiniteSet α) : Bool :=
  s.elements.contains a

/-- Remove an element from the set -/
def remove [DecidableEq α] (a : α) (s : FiniteSet α) : FiniteSet α :=
  let filtered := s.elements.filter (fun x => !(x == a))
  ⟨filtered, List.Nodup.sublist (List.filter_sublist _) s.nodup⟩

/-- Get the size of the set -/
def card (s : FiniteSet α) : Nat :=
  s.elements.length

/-- Sum a function over all elements in the set -/
def sum [Add β] [OfNat β 0] (s : FiniteSet α) (f : α → β) : β :=
  s.elements.foldl (fun acc x => acc + f x) 0

/-- Filter elements satisfying a predicate -/
def filter (p : α → Bool) (s : FiniteSet α) : FiniteSet α :=
  ⟨s.elements.filter p, List.Nodup.sublist (List.filter_sublist _) s.nodup⟩

/-- Union of two sets -/
def union [DecidableEq α] (s₁ s₂ : FiniteSet α) : FiniteSet α :=
  s₂.elements.foldl (fun acc x => acc.insert x) s₁

/-- Intersection of two sets -/
def inter [DecidableEq α] (s₁ s₂ : FiniteSet α) : FiniteSet α :=
  s₁.filter (fun x => s₂.contains x)

/-- Convert to a list (the underlying elements) -/
def toList (s : FiniteSet α) : List α :=
  s.elements

/-- Create a finite set from a list (removes duplicates) -/
def fromList [DecidableEq α] (l : List α) : FiniteSet α :=
  l.foldl (fun acc x => acc.insert x) empty

/-- Check if one set is a subset of another -/
def subset [DecidableEq α] (s₁ s₂ : FiniteSet α) : Bool :=
  s₁.elements.all (fun x => s₂.contains x)

/-- Check if an element is a member (alias for contains, returns Prop for proofs) -/
def member [DecidableEq α] (a : α) (s : FiniteSet α) : Prop :=
  a ∈ s.elements

/-!
### Theorems

Core lemmas for reasoning about finite set operations.
These are directly needed by Ledger sum proofs (#65).
-/

/-- The empty set has no members in its elements list -/
@[simp] theorem elements_empty : (empty : FiniteSet α).elements = [] := rfl

/-- Inserting an element already in the set returns the same set -/
theorem insert_of_mem [DecidableEq α] (a : α) (s : FiniteSet α) (h : a ∈ s.elements) :
    s.insert a = s := by
  unfold insert
  simp [dif_pos h]

/-- Inserting a new element prepends it -/
theorem insert_of_not_mem [DecidableEq α] (a : α) (s : FiniteSet α) (h : a ∉ s.elements) :
    (s.insert a).elements = a :: s.elements := by
  unfold insert
  simp [dif_neg h]

/-- After inserting, the element is in the elements list -/
theorem mem_elements_insert_self [DecidableEq α] (a : α) (s : FiniteSet α) :
    a ∈ (s.insert a).elements := by
  unfold insert
  split
  · assumption
  · exact List.mem_cons_self a s.elements

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

/-- Card of empty is 0 -/
@[simp] theorem card_empty : (empty : FiniteSet α).card = 0 := rfl

/-- Card increases by 1 on fresh insert -/
theorem card_insert_of_not_mem [DecidableEq α] (a : α) (s : FiniteSet α) (h : a ∉ s.elements) :
    (s.insert a).card = s.card + 1 := by
  unfold insert card
  simp [dif_neg h]

/-- Card is unchanged for duplicate insert -/
theorem card_insert_of_mem [DecidableEq α] (a : α) (s : FiniteSet α) (h : a ∈ s.elements) :
    (s.insert a).card = s.card := by
  unfold insert card
  simp [dif_pos h]

/-- Sum of empty set is zero -/
@[simp] theorem sum_empty [Add β] [OfNat β 0] (f : α → β) :
    (empty : FiniteSet α).sum f = 0 := rfl

/-- Subset is reflexive -/
theorem subset_refl [DecidableEq α] (s : FiniteSet α) : s.subset s = true := by
  unfold subset
  simp [List.all_eq_true, contains]

/-- Empty set is subset of any set -/
theorem empty_subset [DecidableEq α] (s : FiniteSet α) : (empty : FiniteSet α).subset s = true := by
  unfold subset
  simp

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

/-- Check if an address is in the set -/
def contains (addr : String) (s : FiniteAddressSet) : Bool :=
  s.addresses.contains addr

/-- Remove an address from the set -/
def remove (addr : String) (s : FiniteAddressSet) : FiniteAddressSet :=
  ⟨s.addresses.remove addr⟩

/-- Get the number of addresses in the set -/
def card (s : FiniteAddressSet) : Nat :=
  s.addresses.card

end FiniteAddressSet

/-- Finite set of natural numbers (for ERC721 token ID tracking, issue #73) -/
structure FiniteNatSet where
  nats : FiniteSet Nat
  deriving Repr

namespace FiniteNatSet

/-- Create an empty nat set -/
def empty : FiniteNatSet :=
  ⟨FiniteSet.empty⟩

/-- Insert a nat into the set -/
def insert (n : Nat) (s : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.insert n⟩

/-- Check if a nat is in the set -/
def contains (n : Nat) (s : FiniteNatSet) : Bool :=
  s.nats.contains n

/-- Remove a nat from the set -/
def remove (n : Nat) (s : FiniteNatSet) : FiniteNatSet :=
  ⟨s.nats.remove n⟩

/-- Get the number of nats in the set -/
def card (s : FiniteNatSet) : Nat :=
  s.nats.card

/-- Check if one set is a subset of another -/
def subset (s₁ s₂ : FiniteNatSet) : Bool :=
  s₁.nats.subset s₂.nats

end FiniteNatSet

end Verity.Core
