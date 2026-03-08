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

def echoStringExecutableRoundTrips : Bool :=
  match StringSmoke.echoString "hello" Verity.defaultState with
  | .success message state =>
      message = "hello" && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoStringExecutableRoundTrips = true := by decide

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
