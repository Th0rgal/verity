import Contracts.Common

namespace Contracts.Smoke

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract SelfBalanceSmoke where
  storage

  function currentBalance () : Uint256 := do
    let bal ← Verity.selfBalance
    return bal

  function balancePlus (delta : Uint256) : Uint256 := do
    let bal ← selfBalance
    return (add bal delta)

example :
    (SelfBalanceSmoke.currentBalance.run { Verity.defaultState with selfBalance := 123 }).getValue? =
      some 123 := by
  decide

example :
    (SelfBalanceSmoke.balancePlus 7 |>.run { Verity.defaultState with selfBalance := 123 }).getValue? =
      some 130 := by
  decide

end Contracts.Smoke
