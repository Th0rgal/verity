/-
  Deprecated wrapper: Reentrancy proofs now live in
  DumbContracts.Examples.ReentrancyExample.
-/

import DumbContracts.Examples.ReentrancyExample

namespace DumbContracts.Examples.ReentrancyProofs

open DumbContracts.Examples.ReentrancyExample

abbrev vulnerable_attack_exists :=
  DumbContracts.Examples.ReentrancyExample.VulnerableBank.vulnerable_attack_exists

abbrev withdraw_maintains_supply_UNPROVABLE :=
  DumbContracts.Examples.ReentrancyExample.VulnerableBank.withdraw_maintains_supply_UNPROVABLE

abbrev withdraw_maintains_supply :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.withdraw_maintains_supply

abbrev deposit_maintains_supply :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.deposit_maintains_supply

end DumbContracts.Examples.ReentrancyProofs
