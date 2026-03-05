import Verity.Examples.MacroContracts.Core

namespace Verity.Examples.OwnedCounter

def owner : StorageSlot Address := ⟨0⟩
def count : StorageSlot Uint256 := ⟨1⟩

abbrev increment := Verity.Examples.MacroContracts.OwnedCounter.increment
abbrev decrement := Verity.Examples.MacroContracts.OwnedCounter.decrement
abbrev getCount := Verity.Examples.MacroContracts.OwnedCounter.getCount
abbrev getOwner := Verity.Examples.MacroContracts.OwnedCounter.getOwner
abbrev transferOwnership := Verity.Examples.MacroContracts.OwnedCounter.transferOwnership
abbrev isOwner := Verity.Examples.MacroContracts.OwnedCounter.isOwner
abbrev onlyOwner := Verity.Examples.MacroContracts.OwnedCounter.onlyOwner

def «constructor» (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner

end Verity.Examples.OwnedCounter
