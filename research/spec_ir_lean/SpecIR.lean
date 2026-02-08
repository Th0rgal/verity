namespace DumbContracts

-- Minimal state model (sketch only).
structure State where
  balances : Nat -> Int
  totalSupply : Int

abbrev Pred := State -> Prop
abbrev Rel := State -> State -> Prop

structure Spec where
  requires : Pred
  ensures : Rel

-- A transition satisfies a spec if any required pre-state implies the
-- post-state relation.
def holds (spec : Spec) (s s' : State) : Prop :=
  spec.requires s -> spec.ensures s s'

-- A checker is sound if, whenever it accepts a transition, the transition
-- satisfies the spec semantics.
-- This is just a placeholder signature; the proof would come later.
structure Checker where
  accepts : Spec -> State -> State -> Prop
  sound : forall (spec : Spec) (s s' : State),
    accepts spec s s' -> holds spec s s'

-- Example: a simple transfer spec skeleton (sketch).
def transferSpec (from to : Nat) (amount : Int) : Spec :=
  { requires := fun s =>
      (amount >= 0) /\ (s.balances from >= amount) /\ (to != from)
    ensures := fun s s' =>
      (s'.balances from = s.balances from - amount)
      /\ (s'.balances to = s.balances to + amount)
      /\ (s'.totalSupply = s.totalSupply)
  }

end DumbContracts
