import Contracts.Common

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-!
A minimal ERC4626-style vault example with 1:1 asset/share accounting.

This is intentionally conservative: deposits mint shares equal to assets and
withdrawals burn shares 1:1. That keeps the example mechanically tractable
while still exercising the canonical vault surface and share-accounting proofs.
-/
verity_contract Vault where
  storage
    totalAssetsSlot : Uint256 := slot 0
    totalSupplySlot : Uint256 := slot 1
    shareBalancesSlot : Address → Uint256 := slot 2

  constructor () := do
    setStorage totalAssetsSlot 0
    setStorage totalSupplySlot 0

  function deposit (assets : Uint256) : Unit := do
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    let newShares ← requireSomeUint (safeAdd currentShares assets) "Share balance overflow"
    let currentAssets ← getStorage totalAssetsSlot
    let newAssets ← requireSomeUint (safeAdd currentAssets assets) "Total assets overflow"
    let currentSupply ← getStorage totalSupplySlot
    let newSupply ← requireSomeUint (safeAdd currentSupply assets) "Total supply overflow"
    setMapping shareBalancesSlot sender newShares
    setStorage totalAssetsSlot newAssets
    setStorage totalSupplySlot newSupply

  function withdraw (shares : Uint256) : Unit := do
    let sender ← msgSender
    let currentShares ← getMapping shareBalancesSlot sender
    require (currentShares >= shares) "Insufficient shares"
    let currentAssets ← getStorage totalAssetsSlot
    require (currentAssets >= shares) "Insufficient assets"
    let currentSupply ← getStorage totalSupplySlot
    require (currentSupply >= shares) "Insufficient supply"
    setMapping shareBalancesSlot sender (sub currentShares shares)
    setStorage totalAssetsSlot (sub currentAssets shares)
    setStorage totalSupplySlot (sub currentSupply shares)

  function balanceOf (addr : Address) : Uint256 := do
    let currentShares ← getMapping shareBalancesSlot addr
    return currentShares

  function totalAssets () : Uint256 := do
    let currentAssets ← getStorage totalAssetsSlot
    return currentAssets

  function totalSupply () : Uint256 := do
    let currentSupply ← getStorage totalSupplySlot
    return currentSupply

namespace Vault

abbrev getTotalAssets : Contract Uint256 := totalAssets
abbrev getTotalSupply : Contract Uint256 := totalSupply

end Vault

end Contracts
