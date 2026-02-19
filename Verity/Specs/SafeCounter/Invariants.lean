/-
  State invariants for SafeCounter contract.

  SafeCounter adds overflow/underflow protection on top of Counter.
  The key invariant is that the count stays within [0, MAX_UINT256].
-/

import Verity.Specs.Common
import Verity.Stdlib.Math

namespace Verity.Specs.SafeCounter

open Verity
open Verity.Stdlib.Math

/-! ## State Invariants -/

/-- Well-formed state: sender and contract addresses are nonzero -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0

/-- Context preserved: operations don't change sender or contract address -/
abbrev context_preserved := Specs.sameContext

/-- Storage isolation: operations on slot 0 don't affect other slots -/
def storage_isolated (s s' : ContractState) : Prop :=
  ∀ slot : Nat, slot ≠ 0 → s'.storage slot = s.storage slot

/-- Bounds invariant: count is within safe range -/
def count_in_bounds (s : ContractState) : Prop :=
  (s.storage 0 : Nat) ≤ MAX_UINT256

end Verity.Specs.SafeCounter
