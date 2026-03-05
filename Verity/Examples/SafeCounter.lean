import Verity.Examples.MacroContracts.Core

namespace Verity.Examples.SafeCounter

def count : StorageSlot Uint256 := ⟨0⟩

abbrev increment := Verity.Examples.MacroContracts.SafeCounter.increment
abbrev decrement := Verity.Examples.MacroContracts.SafeCounter.decrement
abbrev getCount := Verity.Examples.MacroContracts.SafeCounter.getCount

end Verity.Examples.SafeCounter
