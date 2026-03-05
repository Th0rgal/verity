import Verity.Examples.MacroContracts.Core

namespace Verity.Examples.Owned

def owner : StorageSlot Address := ⟨0⟩

abbrev transferOwnership := Verity.Examples.MacroContracts.Owned.transferOwnership
abbrev getOwner := Verity.Examples.MacroContracts.Owned.getOwner
abbrev isOwner := Verity.Examples.MacroContracts.Owned.isOwner
abbrev onlyOwner := Verity.Examples.MacroContracts.Owned.onlyOwner

def «constructor» (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner

end Verity.Examples.Owned
