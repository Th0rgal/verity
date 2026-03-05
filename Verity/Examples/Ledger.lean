import Verity.Examples.MacroContracts.Core

namespace Verity.Examples.Ledger

def balances : StorageSlot (Address → Uint256) := ⟨0⟩

abbrev deposit := Verity.Examples.MacroContracts.Ledger.deposit
abbrev withdraw := Verity.Examples.MacroContracts.Ledger.withdraw
abbrev transfer := Verity.Examples.MacroContracts.Ledger.transfer
abbrev getBalance := Verity.Examples.MacroContracts.Ledger.getBalance

end Verity.Examples.Ledger
