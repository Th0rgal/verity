/-
  State invariants for SafeCounter contract.

  SafeCounter adds overflow/underflow protection on top of Counter.
  The key invariant is that the count stays within [0, MAX_UINT256].
-/

import DumbContracts.Core
import DumbContracts.Stdlib.Math

namespace Contracts.SafeCounter.Invariants

open DumbContracts
open DumbContracts.Stdlib.Math

/-! ## State Invariants -/

/-- Well-formed state: sender and contract addresses are non-empty -/
structure WellFormedState (s : ContractState) : Prop where
  sender_nonempty : s.sender ≠ ""
  contract_nonempty : s.thisAddress ≠ ""

/-- Context preserved: operations don't change sender or contract address -/
def context_preserved (s s' : ContractState) : Prop :=
  s'.sender = s.sender ∧
  s'.thisAddress = s.thisAddress ∧
  s'.msgValue = s.msgValue ∧
  s'.blockTimestamp = s.blockTimestamp

/-- Storage isolation: operations on slot 0 don't affect other slots -/
def storage_isolated (s s' : ContractState) : Prop :=
  ∀ slot : Nat, slot ≠ 0 → s'.storage slot = s.storage slot

/-- Bounds invariant: count is within safe range -/
def count_in_bounds (s : ContractState) : Prop :=
  (s.storage 0 : Nat) ≤ MAX_UINT256

end Contracts.SafeCounter.Invariants
