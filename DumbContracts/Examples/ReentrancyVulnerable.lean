/-
  Deprecated wrapper: Vulnerable reentrancy example now lives in
  DumbContracts.Examples.ReentrancyExample.

  This file keeps a stable import path while delegating to the newer, fully
  proven example.
-/

import DumbContracts.Examples.ReentrancyExample

namespace DumbContracts.Examples.ReentrancyVulnerable

open DumbContracts.Examples.ReentrancyExample

abbrev reentrancyLock := DumbContracts.Examples.ReentrancyExample.reentrancyLock
abbrev totalSupply := DumbContracts.Examples.ReentrancyExample.totalSupply
abbrev balances := DumbContracts.Examples.ReentrancyExample.balances

abbrev supplyInvariant := DumbContracts.Examples.ReentrancyExample.supplyInvariant

abbrev withdraw :=
  DumbContracts.Examples.ReentrancyExample.VulnerableBank.withdraw

abbrev vulnerable_attack_exists :=
  DumbContracts.Examples.ReentrancyExample.VulnerableBank.vulnerable_attack_exists

abbrev withdraw_does_NOT_maintain_supply :=
  DumbContracts.Examples.ReentrancyExample.VulnerableBank.withdraw_maintains_supply_UNPROVABLE

end DumbContracts.Examples.ReentrancyVulnerable
