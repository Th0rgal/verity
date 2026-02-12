/-
  Deprecated wrapper: Reentrancy proofs now live in
  Contracts.Reentrancy.Example.
-/

import Contracts.Reentrancy.Example

namespace Contracts.Reentrancy.Proofs

open Contracts.Reentrancy.Example

abbrev vulnerable_attack_exists :=
  Contracts.Reentrancy.Example.VulnerableBank.vulnerable_attack_exists

abbrev withdraw_maintains_supply_UNPROVABLE :=
  Contracts.Reentrancy.Example.VulnerableBank.withdraw_maintains_supply_UNPROVABLE

abbrev withdraw_maintains_supply :=
  Contracts.Reentrancy.Example.SafeBank.withdraw_maintains_supply

abbrev deposit_maintains_supply :=
  Contracts.Reentrancy.Example.SafeBank.deposit_maintains_supply

end Contracts.Reentrancy.Proofs
