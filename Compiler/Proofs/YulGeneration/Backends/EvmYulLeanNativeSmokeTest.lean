import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import EvmYul.Yul.Interpreter

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler.Yul

private def runNativeProgram (stmts : List YulStmt) : Option EvmYul.Yul.State :=
  match lowerStmtsNative stmts with
  | .error _ => none
  | .ok lowered =>
      let initial : EvmYul.Yul.State := Inhabited.default
      match EvmYul.Yul.exec 64 (.Block lowered) none initial with
      | .error _ => none
      | .ok state => some state

private def varIs (name : String) (value : Nat) (state : EvmYul.Yul.State) : Bool :=
  match state with
  | .Ok _ store =>
      match store.lookup name with
      | some got => got == EvmYul.UInt256.ofNat value
      | none => false
  | _ => false

private def lowersAddAsPrim : Bool :=
  match lowerExprNative (.call "add" [.lit 1, .lit 2]) with
  | .Call (.inl op) args =>
      op == (EvmYul.Operation.ADD : EvmYul.Operation .Yul) && args.length == 2
  | _ => false

private def lowersHelperAsUserFunction : Bool :=
  match lowerExprNative (.call "helper" [.lit 1]) with
  | .Call (.inr name) args => name == "helper" && args.length == 1
  | _ => false

example : lowersAddAsPrim = true := by
  native_decide

example : lowersHelperAsUserFunction = true := by
  native_decide

example :
    (match runNativeProgram [
      .let_ "x" (.call "add" [.lit 40, .lit 2])
    ] with
    | some state => varIs "x" 42 state
    | none => false) = true := by
  native_decide

example :
    (match lowerRuntimeContractNative [
      .funcDef "inc" ["x"] ["r"] [
        .let_ "r" (.call "add" [.ident "x", .lit 1])
      ],
      .letMany ["y"] (.call "inc" [.lit 41])
    ] with
    | .ok contract =>
        contract.functions.lookup "inc" |>.isSome
    | .error _ => false) = true := by
  native_decide

end Compiler.Proofs.YulGeneration.Backends
