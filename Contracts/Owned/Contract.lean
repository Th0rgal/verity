import Contracts.MacroContracts.Core

namespace Contracts.Owned

open Verity

def owner : StorageSlot Address := ⟨0⟩

abbrev transferOwnership := Contracts.MacroContracts.Owned.transferOwnership
abbrev getOwner := Contracts.MacroContracts.Owned.getOwner
abbrev isOwner := Contracts.MacroContracts.Owned.isOwner
abbrev onlyOwner := Contracts.MacroContracts.Owned.onlyOwner

abbrev «constructor» := Contracts.MacroContracts.Owned.constructor

end Contracts.Owned
