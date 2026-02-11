/-
  Deprecated wrapper: Safe reentrancy example now lives in
  DumbContracts.Examples.ReentrancyExample.
-/

import DumbContracts.Examples.ReentrancyExample

namespace DumbContracts.Examples.ReentrancySafe

open DumbContracts.Examples.ReentrancyExample

abbrev reentrancyLock := DumbContracts.Examples.ReentrancyExample.reentrancyLock
abbrev totalSupply := DumbContracts.Examples.ReentrancyExample.totalSupply
abbrev balances := DumbContracts.Examples.ReentrancyExample.balances

abbrev supplyInvariant := DumbContracts.Examples.ReentrancyExample.supplyInvariant

abbrev withdraw :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.withdraw

abbrev deposit :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.deposit

abbrev withdraw_maintains_supply :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.withdraw_maintains_supply

abbrev deposit_maintains_supply :=
  DumbContracts.Examples.ReentrancyExample.SafeBank.deposit_maintains_supply

end DumbContracts.Examples.ReentrancySafe
