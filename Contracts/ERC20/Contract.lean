import Contracts.MacroContracts.Tokens

namespace Contracts.ERC20

open Verity

abbrev owner := Contracts.MacroContracts.ERC20.ownerSlot
abbrev totalSupply := Contracts.MacroContracts.ERC20.totalSupplySlot
abbrev balances := Contracts.MacroContracts.ERC20.balancesSlot
abbrev allowances := Contracts.MacroContracts.ERC20.allowancesSlot
abbrev mint := Contracts.MacroContracts.ERC20.mint
abbrev transfer := Contracts.MacroContracts.ERC20.transfer
abbrev approve := Contracts.MacroContracts.ERC20.approve
abbrev transferFrom := Contracts.MacroContracts.ERC20.transferFrom
abbrev balanceOf := Contracts.MacroContracts.ERC20.balanceOf
abbrev allowanceOf := Contracts.MacroContracts.ERC20.allowanceOf
abbrev getTotalSupply := Contracts.MacroContracts.ERC20.getTotalSupply
abbrev getOwner := Contracts.MacroContracts.ERC20.getOwner
abbrev isOwner := Contracts.MacroContracts.ERC20.isOwner
abbrev onlyOwner := Contracts.MacroContracts.ERC20.onlyOwner

abbrev «constructor» := Contracts.MacroContracts.ERC20.constructor

end Contracts.ERC20
