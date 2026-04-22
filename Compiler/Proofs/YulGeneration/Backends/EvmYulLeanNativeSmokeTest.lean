import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness
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

private def sampleTx : Compiler.Proofs.YulGeneration.YulTransaction :=
  { sender := 0xCAFE
    msgValue := 7
    thisAddress := 0x1234
    functionSelector := 0x01020304
    args := [41] }

private def zeroStorage : Nat → Nat := fun _ => 0

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

example :
    (match Native.interpretRuntimeNative 128 [
      .funcDef "inc" ["x"] ["r"] [
        .let_ "r" (.call "add" [.ident "x", .lit 1])
      ],
      .expr (.call "sstore" [.lit 7, .call "inc" [.lit 41]])
    ] sampleTx zeroStorage [7] with
    | .ok result => result.success && result.finalStorage 7 == 42
    | .error _ => false) = true := by
  native_decide

example :
    (match Native.interpretRuntimeNative 128
      [.expr (.call "sstore" [.lit 7, .lit 99])]
      sampleTx zeroStorage [7] with
    | .ok result => result.success && result.finalStorage 7 == 99
    | .error _ => false) = true := by
  native_decide

example :
    Native.byteArrayWord
      (ByteArray.ofFn fun i : Fin 32 =>
        if i.1 = 31 then UInt8.ofNat 210 else UInt8.ofNat 0)
      0 = 210 := by
  native_decide

example :
    Native.projectLogEntry
      { address := StateBridge.natToAddress sampleTx.thisAddress
        topics := #[EvmYul.UInt256.ofNat 7]
        data :=
          ByteArray.ofFn fun i : Fin 32 =>
            if i.1 = 31 then UInt8.ofNat 55 else UInt8.ofNat 0 } =
      [7, 55] := by
  native_decide

example :
    (let state : EvmYul.Yul.State :=
      .Ok
        { (StateBridge.toSharedState
            (Compiler.Proofs.YulGeneration.YulState.initial sampleTx zeroStorage) []) with
          H_return :=
            ByteArray.ofFn fun i : Fin 32 =>
              if i.1 = 31 then UInt8.ofNat 99 else UInt8.ofNat 0 }
        ∅
     Native.projectHaltReturn state (EvmYul.UInt256.ofNat 1)) = some 99 := by
  native_decide

example :
    (match Native.interpretRuntimeNative 128 [
      .let_ "v" (.call "callvalue" []),
      .expr (.call "sstore" [.lit 8, .ident "v"])
    ] sampleTx zeroStorage [8] with
    | .ok result => result.success && result.finalStorage 8 == sampleTx.msgValue
    | .error _ => false) = true := by
  native_decide

example :
    (match Native.interpretRuntimeNative 128 []
      sampleTx zeroStorage [] [[1, 2, 3]] with
    | .ok result => result.success && result.events == [[1, 2, 3]]
    | .error _ => false) = true := by
  native_decide

end Compiler.Proofs.YulGeneration.Backends
