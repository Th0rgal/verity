import Verity.Examples.MacroContracts.Tokens

namespace Verity.Examples.SimpleToken

def owner : StorageSlot Address := ⟨0⟩
def balances : StorageSlot (Address → Uint256) := ⟨1⟩
def totalSupply : StorageSlot Uint256 := ⟨2⟩

abbrev mint := Verity.Examples.MacroContracts.SimpleToken.mint
abbrev transfer := Verity.Examples.MacroContracts.SimpleToken.transfer
abbrev balanceOf := Verity.Examples.MacroContracts.SimpleToken.balanceOf
abbrev getTotalSupply := Verity.Examples.MacroContracts.SimpleToken.getTotalSupply
abbrev getOwner := Verity.Examples.MacroContracts.SimpleToken.getOwner
abbrev isOwner := Verity.Examples.MacroContracts.SimpleToken.isOwner
abbrev onlyOwner := Verity.Examples.MacroContracts.SimpleToken.onlyOwner

def «constructor» (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner
  setStorage totalSupply 0

end Verity.Examples.SimpleToken
