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
    blockTimestamp := 12345
    blockNumber := 678
    chainId := 31337
    blobBaseFee := 19
    functionSelector := 0x01020304
    args := [41] }

private def zeroStorage : Nat → Nat := fun _ => 0

private def nativeStoresBuiltin (builtin : String) (slot expected : Nat) : Bool :=
  match Native.interpretRuntimeNative 128 [
    .let_ "v" (.call builtin []),
    .expr (.call "sstore" [.lit slot, .ident "v"])
  ] sampleTx zeroStorage [slot] with
  | .ok result => result.success && result.finalStorage slot == expected
  | .error _ => false

private def dispatchSmokeContract : Compiler.IRContract :=
  { name := "NativeDispatchSmoke"
    deploy := []
    functions := [
      { name := "left"
        selector := 0x11111111
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 11, .lit 101])
        ] },
      { name := "right"
        selector := 0x22222222
        params := []
        ret := .unit
        body := [
          .expr (.call "sstore" [.lit 11, .lit 202])
        ] }
    ]
    usesMapping := false }

private partial def nativeStmtContainsSwitch : EvmYul.Yul.Ast.Stmt → Bool
  | .Switch _ _ _ => true
  | .Block stmts => stmts.any nativeStmtContainsSwitch
  | .If _ body => body.any nativeStmtContainsSwitch
  | .For _ post body =>
      post.any nativeStmtContainsSwitch || body.any nativeStmtContainsSwitch
  | _ => false

private partial def nativeStmtSwitchCaseLabels : EvmYul.Yul.Ast.Stmt → List Nat
  | .Switch _ cases defaultBody =>
      cases.map (fun (label, _) => StateBridge.uint256ToNat label) ++
        defaultBody.foldl (fun acc stmt => acc ++ nativeStmtSwitchCaseLabels stmt) []
  | .Block stmts =>
      stmts.foldl (fun acc stmt => acc ++ nativeStmtSwitchCaseLabels stmt) []
  | .If _ body =>
      body.foldl (fun acc stmt => acc ++ nativeStmtSwitchCaseLabels stmt) []
  | .For _ post body =>
      post.foldl (fun acc stmt => acc ++ nativeStmtSwitchCaseLabels stmt) [] ++
        body.foldl (fun acc stmt => acc ++ nativeStmtSwitchCaseLabels stmt) []
  | _ => []

private partial def nativeStmtContainsSstore (slot value : Nat) : EvmYul.Yul.Ast.Stmt → Bool
  | .ExprStmtCall (.Call (.inl op) [.Lit gotSlot, .Lit gotValue]) =>
      op == (EvmYul.Operation.SSTORE : EvmYul.Operation .Yul) &&
        StateBridge.uint256ToNat gotSlot == slot &&
        StateBridge.uint256ToNat gotValue == value
  | .Block stmts =>
      stmts.any (nativeStmtContainsSstore slot value)
  | .If _ body =>
      body.any (nativeStmtContainsSstore slot value)
  | .Switch _ cases defaultBody =>
      cases.any (fun (_, body) => body.any (nativeStmtContainsSstore slot value)) ||
        defaultBody.any (nativeStmtContainsSstore slot value)
  | .For _ post body =>
      post.any (nativeStmtContainsSstore slot value) ||
        body.any (nativeStmtContainsSstore slot value)
  | _ => false

private partial def nativeStmtSwitchCaseStores
    (label slot value : Nat) : EvmYul.Yul.Ast.Stmt → Bool
  | .Switch _ cases defaultBody =>
      cases.any (fun (gotLabel, body) =>
        StateBridge.uint256ToNat gotLabel == label &&
          body.any (nativeStmtContainsSstore slot value)) ||
        defaultBody.any (nativeStmtSwitchCaseStores label slot value)
  | .Block stmts =>
      stmts.any (nativeStmtSwitchCaseStores label slot value)
  | .If _ body =>
      body.any (nativeStmtSwitchCaseStores label slot value)
  | .For _ post body =>
      post.any (nativeStmtSwitchCaseStores label slot value) ||
        body.any (nativeStmtSwitchCaseStores label slot value)
  | _ => false

private def emittedDispatchLowersToNativeSwitch : Bool :=
  match lowerRuntimeContractNative (Compiler.emitYul dispatchSmokeContract).runtimeCode with
  | .ok contract =>
      nativeStmtContainsSwitch contract.dispatcher &&
        (contract.functions.lookup "left").isNone &&
        (contract.functions.lookup "right").isNone
  | .error _ => false

private def duplicateNativeHelperFailsClosed : Bool :=
  match lowerRuntimeContractNative [
    .funcDef "dup" [] [] [],
    .funcDef "dup" [] [] []
  ] with
  | .ok _ => false
  | .error _ => true

private def emittedDispatchLowersNativeSelectorCases : Bool :=
  match lowerRuntimeContractNative (Compiler.emitYul dispatchSmokeContract).runtimeCode with
  | .ok contract =>
      let labels := nativeStmtSwitchCaseLabels contract.dispatcher
      labels.contains 0x11111111 && labels.contains 0x22222222
  | .error _ => false

private def emittedDispatchNativeSelectorCaseBodies : Bool :=
  match lowerRuntimeContractNative (Compiler.emitYul dispatchSmokeContract).runtimeCode with
  | .ok contract =>
      nativeStmtSwitchCaseStores 0x11111111 11 101 contract.dispatcher &&
        nativeStmtSwitchCaseStores 0x22222222 11 202 contract.dispatcher
  | .error _ => false

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
    nativeStoresBuiltin "callvalue" 8 sampleTx.msgValue = true := by
  native_decide

example :
    nativeStoresBuiltin "timestamp" 9 sampleTx.blockTimestamp = true := by
  native_decide

example :
    nativeStoresBuiltin "number" 10 sampleTx.blockNumber = true := by
  native_decide

example :
    nativeStoresBuiltin "chainid" 15 1 = true := by
  native_decide

example :
    nativeStoresBuiltin "blobbasefee" 16 1 = true := by
  native_decide

example :
    nativeStoresBuiltin "caller" 12 sampleTx.sender = true := by
  native_decide

example :
    nativeStoresBuiltin "address" 13 sampleTx.thisAddress = true := by
  native_decide

example :
    nativeStoresBuiltin "calldatasize" 14 36 = true := by
  native_decide

example :
    emittedDispatchLowersToNativeSwitch = true := by
  native_decide

example :
    emittedDispatchLowersNativeSelectorCases = true := by
  native_decide

example :
    emittedDispatchNativeSelectorCaseBodies = true := by
  native_decide

example :
    duplicateNativeHelperFailsClosed = true := by
  native_decide

example :
    (match Native.interpretRuntimeNative 128 []
      sampleTx zeroStorage [] [[1, 2, 3]] with
    | .ok result => result.success && result.events == [[1, 2, 3]]
    | .error _ => false) = true := by
  native_decide

end Compiler.Proofs.YulGeneration.Backends
