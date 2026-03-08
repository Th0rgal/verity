import Contracts.Common
import Compiler.CheckContract

namespace Contracts

open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract StringErrorSmoke where
  storage
    sentinel : Uint256 := slot 0

  errors
    error BadMessage(String)
    error TaggedMessage(Uint256, String)
    error SecondMessage(String, String)

  function checkMessage (ok : Bool, _message : String) : Unit := do
    requireError ok BadMessage(_message)

  function checkTaggedMessage (tag : Uint256, _message : String) : Unit := do
    requireError (tag == 1) TaggedMessage(tag, _message)

  function checkSecondMessage (ok : Bool, _prefix : String, _message : String) : Unit := do
    requireError ok SecondMessage(_prefix, _message)

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
        if (c :: cs).take n.length == n then true
        else go cs
    go h

def checkMessageModelUsesStringError : Bool :=
  match StringErrorSmoke.spec.errors with
  | [ { name := "BadMessage", params := [Compiler.CompilationModel.ParamType.string] }
    , { name := "TaggedMessage", params := [Compiler.CompilationModel.ParamType.uint256, Compiler.CompilationModel.ParamType.string] }
    , { name := "SecondMessage", params := [Compiler.CompilationModel.ParamType.string, Compiler.CompilationModel.ParamType.string] } ] =>
      true
  | _ => false

example : checkMessageModelUsesStringError = true := by decide

def checkTaggedMessageModelUsesTaggedStringError : Bool :=
  match StringErrorSmoke.spec.errors.find? (fun err => err.name == "TaggedMessage") with
  | some { params := [Compiler.CompilationModel.ParamType.uint256, Compiler.CompilationModel.ParamType.string], .. } =>
      true
  | _ => false

example : checkTaggedMessageModelUsesTaggedStringError = true := by decide

def checkMessageExecutableBranchesOnCondition : Bool :=
  match StringErrorSmoke.checkMessage true "ok" Verity.defaultState,
      StringErrorSmoke.checkMessage false "boom" Verity.defaultState with
  | .success () successState, .revert msg revertState =>
      msg == "BadMessage" &&
      successState.sender == Verity.defaultState.sender &&
      revertState.sender == Verity.defaultState.sender
  | _, _ => false

example : checkMessageExecutableBranchesOnCondition = true := by decide

def checkTaggedMessageExecutableBranchesOnCondition : Bool :=
  match StringErrorSmoke.checkTaggedMessage 1 "ok" Verity.defaultState,
      StringErrorSmoke.checkTaggedMessage 7 "boom" Verity.defaultState with
  | .success () successState, .revert msg revertState =>
      msg == "TaggedMessage" &&
      successState.sender == Verity.defaultState.sender &&
      revertState.sender == Verity.defaultState.sender
  | _, _ => false

example : checkTaggedMessageExecutableBranchesOnCondition = true := by decide

def checkSecondMessageExecutableBranchesOnCondition : Bool :=
  match StringErrorSmoke.checkSecondMessage true "ignored" "ok" Verity.defaultState,
      StringErrorSmoke.checkSecondMessage false "ignored" "boom" Verity.defaultState with
  | .success () successState, .revert msg revertState =>
      msg == "SecondMessage" &&
      successState.sender == Verity.defaultState.sender &&
      revertState.sender == Verity.defaultState.sender
  | _, _ => false

example : checkSecondMessageExecutableBranchesOnCondition = true := by decide

#check_contract StringErrorSmoke

end Contracts
