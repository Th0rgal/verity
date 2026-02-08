namespace DumbContracts

abbrev Address := Nat

structure State where
  balance : Address -> Int
  totalSupply : Int

abbrev Pred := State -> Prop
abbrev Rel := State -> State -> Prop

structure Spec where
  requires : Pred
  ensures : Rel

-- Function update (finite map style) for balances.
def update (f : Address -> Int) (k : Address) (v : Int) : Address -> Int :=
  fun a => if a = k then v else f a

lemma update_eq (f : Address -> Int) (k : Address) (v : Int) :
  update f k v k = v := by
  simp [update]

lemma update_ne (f : Address -> Int) (k : Address) (v : Int) (a : Address)
    (h : a ≠ k) : update f k v a = f a := by
  simp [update, h]

-- Transfer precondition.
def preTransfer (from to : Address) (amount : Int) (s : State) : Prop :=
  amount >= 0 ∧ from ≠ to ∧ s.balance from >= amount

-- Transfer implementation (Lean-only prototype).
def transfer (from to : Address) (amount : Int) (s : State) : State :=
  { balance := update (update s.balance from (s.balance from - amount)) to (s.balance to + amount)
    totalSupply := s.totalSupply }

-- Transfer spec in Lean (no DSL).
def transferSpec (from to : Address) (amount : Int) : Spec :=
  { requires := preTransfer from to amount
    ensures := fun s s' =>
      s'.balance from = s.balance from - amount ∧
      s'.balance to = s.balance to + amount ∧
      (forall a, a ≠ from -> a ≠ to -> s'.balance a = s.balance a) ∧
      s'.totalSupply = s.totalSupply }

-- Proof: the Lean implementation satisfies the Lean spec.
theorem transfer_sound (s : State) (from to : Address) (amount : Int) :
    preTransfer from to amount s ->
    (transferSpec from to amount).ensures s (transfer from to amount s) := by
  intro hpre
  have hft : from ≠ to := hpre.2.1
  constructor
  · -- balance[from]
    simp [transfer, update, hft]
  constructor
  · -- balance[to]
    simp [transfer, update]
  constructor
  · -- frame for other addresses
    intro a ha_from ha_to
    simp [transfer, update, ha_from, ha_to]
  · -- totalSupply unchanged
    simp [transfer]

-- Convenience: spec holds when its requires clause holds.
theorem transfer_spec_holds (s : State) (from to : Address) (amount : Int) :
    (transferSpec from to amount).requires s ->
    (transferSpec from to amount).ensures s (transfer from to amount s) := by
  intro hreq
  exact transfer_sound s from to amount hreq

-- Mint precondition.
def preMint (to : Address) (amount : Int) (s : State) : Prop :=
  amount >= 0

-- Mint implementation (Lean-only prototype).
def mint (to : Address) (amount : Int) (s : State) : State :=
  { balance := update s.balance to (s.balance to + amount)
    totalSupply := s.totalSupply + amount }

-- Mint spec in Lean (no DSL).
def mintSpec (to : Address) (amount : Int) : Spec :=
  { requires := preMint to amount
    ensures := fun s s' =>
      s'.balance to = s.balance to + amount ∧
      (forall a, a ≠ to -> s'.balance a = s.balance a) ∧
      s'.totalSupply = s.totalSupply + amount }

-- Proof: the Lean implementation satisfies the Lean spec.
theorem mint_sound (s : State) (to : Address) (amount : Int) :
    preMint to amount s ->
    (mintSpec to amount).ensures s (mint to amount s) := by
  intro _hpre
  constructor
  · -- balance[to]
    simp [mint, update]
  constructor
  · -- frame for other addresses
    intro a ha_to
    simp [mint, update, ha_to]
  · -- totalSupply increases
    simp [mint]

-- Convenience: spec holds when its requires clause holds.
theorem mint_spec_holds (s : State) (to : Address) (amount : Int) :
    (mintSpec to amount).requires s ->
    (mintSpec to amount).ensures s (mint to amount s) := by
  intro hreq
  exact mint_sound s to amount hreq

end DumbContracts
