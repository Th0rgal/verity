import Contracts.MacroContracts.Tokens

namespace Contracts.SimpleToken

open Verity

def owner : StorageSlot Address := ⟨0⟩
def balances : StorageSlot (Address → Uint256) := ⟨1⟩
def totalSupply : StorageSlot Uint256 := ⟨2⟩

abbrev mint := Contracts.MacroContracts.SimpleToken.mint
abbrev transfer := Contracts.MacroContracts.SimpleToken.transfer
abbrev balanceOf := Contracts.MacroContracts.SimpleToken.balanceOf
abbrev getTotalSupply := Contracts.MacroContracts.SimpleToken.getTotalSupply
abbrev getOwner := Contracts.MacroContracts.SimpleToken.getOwner
abbrev isOwner := Contracts.MacroContracts.SimpleToken.isOwner
abbrev onlyOwner := Contracts.MacroContracts.SimpleToken.onlyOwner

abbrev «constructor» := Contracts.MacroContracts.SimpleToken.constructor

end Contracts.SimpleToken
