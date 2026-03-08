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

  function echoStringAfterUint (_tag : Uint256, message : String) : String := do
    returnBytes message

  function echoStringBeforeUint (message : String, _tag : Uint256) : String := do
    returnBytes message

  function echoSecondString (_prefix : String, message : String) : String := do
    returnBytes message

def echoStringExecutableRoundTrips : Bool :=
  match StringSmoke.echoString "hello" Verity.defaultState with
  | .success message state =>
      message == "hello" && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : echoStringExecutableRoundTrips = true := by decide

def mixedStringExecutableRoundTrips : Bool :=
  match StringSmoke.echoStringAfterUint 7 "hello" Verity.defaultState,
      StringSmoke.echoStringBeforeUint "hello" 9 Verity.defaultState,
      StringSmoke.echoSecondString "ignored" "hello" Verity.defaultState with
  | .success after stateAfter, .success before stateBefore, .success second stateSecond =>
      after == "hello" &&
      before == "hello" &&
      second == "hello" &&
      stateAfter.sender == Verity.defaultState.sender &&
      stateBefore.sender == Verity.defaultState.sender &&
      stateSecond.sender == Verity.defaultState.sender
  | _, _, _ => false

example : mixedStringExecutableRoundTrips = true := by decide

/--
error: storage field cannot be String; use Uint256 encoding
-/
#guard_msgs in
verity_contract StringStorageUnsupported where
  storage
    label : String := slot 0

  function echoString () : Unit := do
    pure ()

/--
error: equality is currently supported only for Bool and word-like values (Uint256, Uint8, Address, Bytes32); got Verity.Macro.ValueType.string and Verity.Macro.ValueType.string
-/
#guard_msgs in
verity_contract StringEqUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function same (lhs : String, rhs : String) : Bool := do
    return (lhs == rhs)

/--
error: logical operator requires Bool, got Verity.Macro.ValueType.string
-/
#guard_msgs in
verity_contract StringLogicalUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function choose (flag : String) : Uint256 := do
    if flag && true then
      return 1
    else
      return 0

/--
error: equality is currently supported only for Bool and word-like values (Uint256, Uint8, Address, Bytes32); got Verity.Macro.ValueType.string and Verity.Macro.ValueType.string
-/
#guard_msgs in
verity_contract StringImmutableEqUnsupported where
  storage
    sentinel : Uint256 := slot 0

  immutables
    bad : Bool := (lhs == rhs)

  constructor (lhs : String, rhs : String) := do
    pure ()

  function same () : Bool := do
    return bad

#check_contract StringSmoke

end Contracts
