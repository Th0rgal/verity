/-
  Deprecated wrapper: Safe reentrancy example now lives in
  Contracts.Reentrancy.Example.
-/

import Contracts.Reentrancy.Example

namespace Contracts.Reentrancy.Safe

open Contracts.Reentrancy.Example

abbrev reentrancyLock := Contracts.Reentrancy.Example.reentrancyLock
abbrev totalSupply := Contracts.Reentrancy.Example.totalSupply
abbrev balances := Contracts.Reentrancy.Example.balances

abbrev supplyInvariant := Contracts.Reentrancy.Example.supplyInvariant

abbrev withdraw :=
  Contracts.Reentrancy.Example.SafeBank.withdraw

abbrev deposit :=
  Contracts.Reentrancy.Example.SafeBank.deposit

abbrev withdraw_maintains_supply :=
  Contracts.Reentrancy.Example.SafeBank.withdraw_maintains_supply

abbrev deposit_maintains_supply :=
  Contracts.Reentrancy.Example.SafeBank.deposit_maintains_supply

end Contracts.Reentrancy.Safe
