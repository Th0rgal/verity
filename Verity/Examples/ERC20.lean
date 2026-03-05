import Verity.Examples.MacroContracts.Tokens

namespace Verity.Examples.ERC20

abbrev owner := Verity.Examples.MacroContracts.ERC20.ownerSlot
abbrev totalSupply := Verity.Examples.MacroContracts.ERC20.totalSupplySlot
abbrev balances := Verity.Examples.MacroContracts.ERC20.balancesSlot
abbrev allowances := Verity.Examples.MacroContracts.ERC20.allowancesSlot
abbrev mint := Verity.Examples.MacroContracts.ERC20.mint
abbrev transfer := Verity.Examples.MacroContracts.ERC20.transfer
abbrev approve := Verity.Examples.MacroContracts.ERC20.approve
abbrev transferFrom := Verity.Examples.MacroContracts.ERC20.transferFrom
abbrev balanceOf := Verity.Examples.MacroContracts.ERC20.balanceOf
abbrev allowanceOf := Verity.Examples.MacroContracts.ERC20.allowanceOf
abbrev getTotalSupply := Verity.Examples.MacroContracts.ERC20.getTotalSupply
abbrev getOwner := Verity.Examples.MacroContracts.ERC20.getOwner
abbrev isOwner := Verity.Examples.MacroContracts.ERC20.isOwner
abbrev onlyOwner := Verity.Examples.MacroContracts.ERC20.onlyOwner

def «constructor» (initialOwner : Address) : Contract Unit := do
  setStorageAddr owner initialOwner
  setStorage totalSupply 0

end Verity.Examples.ERC20
