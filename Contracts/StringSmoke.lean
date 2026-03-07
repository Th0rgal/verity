import Contracts.Common
import Compiler.CheckContract

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract StringSmoke where
  storage
    sentinel : Uint256 := slot 0

  function echoString (message : String) : String := do
    returnBytes message

/--
error: storage field cannot be String; use Uint256 encoding
-/
#guard_msgs in
verity_contract StringStorageUnsupported where
  storage
    label : String := slot 0

  function echoString () : Unit := do
    pure ()
end StringStorageUnsupported

#check_contract StringSmoke

end Contracts
