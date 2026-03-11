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

verity_contract StringEqSmoke where
  storage
    sentinel : Uint256 := slot 0

  function same (lhs : String, rhs : String) : Bool := do
    return (lhs == rhs)

  function different (lhs : String, rhs : String) : Bool := do
    return (lhs != rhs)

  function choose (lhs : String, rhs : String) : Uint256 := do
    if lhs == rhs then
      return 1
    else
      return 0

def stringEqExecutableMatches : Bool :=
  match StringEqSmoke.same "hello" "hello" Verity.defaultState,
      StringEqSmoke.same "hello" "world" Verity.defaultState,
      StringEqSmoke.different "hello" "world" Verity.defaultState,
      StringEqSmoke.choose "same" "same" Verity.defaultState,
      StringEqSmoke.choose "same" "diff" Verity.defaultState with
  | .success eq1 _, .success eq2 _, .success ne _, .success pick1 _, .success pick2 _ =>
      eq1 && (!eq2) && ne && pick1 == 1 && pick2 == 0
  | _, _, _, _, _ => false

example : stringEqExecutableMatches = true := by decide

def stringEqModelUsesDynamicBytesEq : Bool :=
  match StringEqSmoke.same_modelBody with
  | [Compiler.CompilationModel.Stmt.return
      (Compiler.CompilationModel.Expr.dynamicBytesEq "lhs" "rhs")] => true
  | _ => false

example : stringEqModelUsesDynamicBytesEq = true := by decide

def stringEqBranchModelUsesDynamicBytesEq : Bool :=
  match StringEqSmoke.choose_modelBody with
  | [Compiler.CompilationModel.Stmt.ite
      (Compiler.CompilationModel.Expr.dynamicBytesEq "lhs" "rhs")
      [Compiler.CompilationModel.Stmt.return (Compiler.CompilationModel.Expr.literal 1)]
      [Compiler.CompilationModel.Stmt.return (Compiler.CompilationModel.Expr.literal 0)]] => true
  | _ => false

example : stringEqBranchModelUsesDynamicBytesEq = true := by decide

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
error: local binding 'alias' currently cannot bind dynamic values (Verity.Macro.ValueType.string) to local variables on the compilation-model path; use the parameter directly
-/
#guard_msgs in
verity_contract StringLocalAliasUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function same (lhs : String, rhs : String) : Bool := do
    let alias := lhs
    return (alias == rhs)

/--
error: local binding 'alias' currently cannot bind dynamic values (Verity.Macro.ValueType.bytes) to local variables on the compilation-model path; use the parameter directly
-/
#guard_msgs in
verity_contract BytesLocalAliasUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function same (lhs : Bytes, rhs : Bytes) : Bool := do
    let alias := lhs
    return (alias == rhs)

#check_contract StringSmoke
#check_contract StringEqSmoke

end Contracts
