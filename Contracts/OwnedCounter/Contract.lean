import Contracts.MacroContracts.Core

namespace Contracts.OwnedCounter

open Verity

def owner : StorageSlot Address := ⟨0⟩
def count : StorageSlot Uint256 := ⟨1⟩

abbrev increment := Contracts.MacroContracts.OwnedCounter.increment
abbrev decrement := Contracts.MacroContracts.OwnedCounter.decrement
abbrev getCount := Contracts.MacroContracts.OwnedCounter.getCount
abbrev getOwner := Contracts.MacroContracts.OwnedCounter.getOwner
abbrev transferOwnership := Contracts.MacroContracts.OwnedCounter.transferOwnership
abbrev isOwner := Contracts.MacroContracts.OwnedCounter.isOwner
abbrev onlyOwner := Contracts.MacroContracts.OwnedCounter.onlyOwner

abbrev «constructor» := Contracts.MacroContracts.OwnedCounter.constructor

end Contracts.OwnedCounter
