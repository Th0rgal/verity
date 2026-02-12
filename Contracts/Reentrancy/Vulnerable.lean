/-
  Deprecated wrapper: Vulnerable reentrancy example now lives in
  Contracts.Reentrancy.Example.

  This file keeps a stable import path while delegating to the newer, fully
  proven example.
-/

import Contracts.Reentrancy.Example

namespace Contracts.Reentrancy.Vulnerable

open Contracts.Reentrancy.Example

abbrev reentrancyLock := Contracts.Reentrancy.Example.reentrancyLock
abbrev totalSupply := Contracts.Reentrancy.Example.totalSupply
abbrev balances := Contracts.Reentrancy.Example.balances

abbrev supplyInvariant := Contracts.Reentrancy.Example.supplyInvariant

abbrev withdraw :=
  Contracts.Reentrancy.Example.VulnerableBank.withdraw

abbrev vulnerable_attack_exists :=
  Contracts.Reentrancy.Example.VulnerableBank.vulnerable_attack_exists

abbrev withdraw_does_NOT_maintain_supply :=
  Contracts.Reentrancy.Example.VulnerableBank.withdraw_maintains_supply_UNPROVABLE

end Contracts.Reentrancy.Vulnerable
