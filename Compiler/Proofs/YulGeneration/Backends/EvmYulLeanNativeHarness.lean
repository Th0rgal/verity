import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics
import Compiler.Codegen
import EvmYul.Yul.Interpreter

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge

/-!
Executable native EVMYulLean runtime harness for #1737.

This module deliberately sits beside the historical adapter.  The adapter is
part of the existing proof/report dependency graph; importing the state bridge
there would create a cycle through the reference oracle.  Keeping the native
harness separate lets tests and future proofs run `EvmYul.Yul.callDispatcher`
directly without disturbing the current verified backend path.
-/

/-- Build a native EVMYulLean state for a generated runtime contract.

The bridge starts from the flat Verity `YulState` projection, then installs the
lowered `YulContract` both in the execution environment and in the current
account. Runtime entrypoints are mutable by default (`perm := true`);
static-call-specific harnesses can override this later when #1737 widens to
external-call semantics.
-/
def initialState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    EvmYul.Yul.State :=
  let verityState := YulState.initial tx storage
  let shared := toSharedState verityState observableSlots
  let addr := natToAddress tx.thisAddress
  let account : EvmYul.Account .Yul :=
    match shared.accountMap.find? addr with
    | some acc => { acc with code := contract }
    | none =>
        { nonce := ⟨0⟩
          balance := ⟨0⟩
          storage := projectStorage storage observableSlots
          code := contract
          tstorage := Batteries.RBMap.empty }
  let shared' : EvmYul.SharedState .Yul :=
    { shared with
      accountMap := shared.accountMap.insert addr account
      executionEnv :=
        { shared.executionEnv with
          code := contract
          perm := true } }
  .Ok shared' ∅

/-! ## Native Environment Support Boundary -/

partial def yulExprUsesBuiltinExceptFunctions
    (builtin : String)
    (functionNames : List String) :
    YulExpr → Bool
  | .call func args =>
      ((func == builtin) && !functionNames.contains func) ||
        args.any (yulExprUsesBuiltinExceptFunctions builtin functionNames)
  | _ => false

partial def yulExprCalledFunctions : YulExpr → List String
  | .call func args => func :: args.flatMap yulExprCalledFunctions
  | _ => []

mutual
  partial def yulStmtUsesBuiltinExceptFunctions
      (builtin : String)
      (functionNames : List String) :
      YulStmt → Bool
    | .let_ _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .letMany _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .assign _ value => yulExprUsesBuiltinExceptFunctions builtin functionNames value
    | .expr e => yulExprUsesBuiltinExceptFunctions builtin functionNames e
    | .if_ cond body =>
        yulExprUsesBuiltinExceptFunctions builtin functionNames cond ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .for_ init cond post body =>
        yulStmtsUseBuiltinExceptFunctions builtin functionNames init ||
          yulExprUsesBuiltinExceptFunctions builtin functionNames cond ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames post ||
          yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .switch discr cases defaultBody =>
        yulExprUsesBuiltinExceptFunctions builtin functionNames discr ||
          cases.any (fun (_, body) =>
            yulStmtsUseBuiltinExceptFunctions builtin functionNames body) ||
          defaultBody.any (yulStmtsUseBuiltinExceptFunctions builtin functionNames)
    | .block stmts => yulStmtsUseBuiltinExceptFunctions builtin functionNames stmts
    | .funcDef _ _ _ body =>
        yulStmtsUseBuiltinExceptFunctions builtin functionNames body
    | .comment _ | .leave => false

  partial def yulStmtsUseBuiltinExceptFunctions
      (builtin : String)
      (functionNames : List String)
      (stmts : List YulStmt) :
      Bool :=
    stmts.any (yulStmtUsesBuiltinExceptFunctions builtin functionNames)
end

mutual
  partial def yulStmtCalledFunctions : YulStmt → List String
    | .let_ _ value => yulExprCalledFunctions value
    | .letMany _ value => yulExprCalledFunctions value
    | .assign _ value => yulExprCalledFunctions value
    | .expr e => yulExprCalledFunctions e
    | .if_ cond body => yulExprCalledFunctions cond ++ yulStmtsCalledFunctions body
    | .for_ init cond post body =>
        yulStmtsCalledFunctions init ++
          yulExprCalledFunctions cond ++
          yulStmtsCalledFunctions post ++
          yulStmtsCalledFunctions body
    | .switch discr cases defaultBody =>
        yulExprCalledFunctions discr ++
          cases.flatMap (fun entry => yulStmtsCalledFunctions entry.2) ++
          (defaultBody.map yulStmtsCalledFunctions).getD []
    | .block stmts => yulStmtsCalledFunctions stmts
    | .funcDef _ _ _ body => yulStmtsCalledFunctions body
    | .comment _ | .leave => []

  partial def yulStmtsCalledFunctions (stmts : List YulStmt) : List String :=
    stmts.flatMap yulStmtCalledFunctions
end

def yulFunctionBodies (runtimeCode : List YulStmt) : List (String × List YulStmt) :=
  runtimeCode.filterMap fun
    | .funcDef name _ _ body => some (name, body)
    | _ => none

def selectorExprMatchesGeneratedDispatcher : YulExpr → Bool
  | .call "shr" [.lit shift, .call "calldataload" [.lit 0]] =>
      shift == Compiler.Constants.selectorShift
  | _ => false

@[simp] theorem selectorExprMatchesGeneratedDispatcher_selectorExpr :
    selectorExprMatchesGeneratedDispatcher
      Compiler.Proofs.YulGeneration.selectorExpr = true := by
  simp [selectorExprMatchesGeneratedDispatcher,
    Compiler.Proofs.YulGeneration.selectorExpr]

def selectedSwitchBody
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt)) :
    List YulStmt :=
  match cases.find? (fun entry => entry.1 == selector) with
  | some (_, body) => body
  | none => defaultBody.getD []

@[simp] theorem selectedSwitchBody_hit
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt))
    (body : List YulStmt)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (selector, body)) :
    selectedSwitchBody selector cases defaultBody = body := by
  unfold selectedSwitchBody
  rw [hFind]

@[simp] theorem selectedSwitchBody_miss
    (selector : Nat)
    (cases : List (Nat × List YulStmt))
    (defaultBody : Option (List YulStmt))
    (hFind : cases.find? (fun entry => entry.1 == selector) = none) :
    selectedSwitchBody selector cases defaultBody = defaultBody.getD [] := by
  unfold selectedSwitchBody
  rw [hFind]

def nativeDispatchSelector (tx : YulTransaction) : Nat :=
  tx.functionSelector % Compiler.Constants.selectorModulus

@[simp] theorem nativeDispatchSelector_of_selector_lt
    (tx : YulTransaction)
    (hSelector : tx.functionSelector < Compiler.Constants.selectorModulus) :
    nativeDispatchSelector tx = tx.functionSelector := by
  simp [nativeDispatchSelector, Nat.mod_eq_of_lt hSelector]

partial def yulStmtsUseBuiltinWithCalledFunctions
    (fuel : Nat)
    (builtin : String)
    (functionBodies : List (String × List YulStmt))
    (stmts : List YulStmt) :
    Bool :=
  yulStmtsUseBuiltinExceptFunctions builtin (functionBodies.map Prod.fst) stmts ||
    match fuel with
    | 0 => false
    | fuel' + 1 =>
        (yulStmtsCalledFunctions stmts).any fun name =>
          match functionBodies.find? (fun entry => entry.1 == name) with
          | some (_, body) =>
              yulStmtsUseBuiltinWithCalledFunctions fuel' builtin functionBodies body
          | none => false

mutual
  partial def yulStmtUsesBuiltinOnNativeRuntimePath
      (builtin : String)
      (selector : Nat)
      (functionBodies : List (String × List YulStmt)) :
      YulStmt → Bool
    | .funcDef _ _ _ _ => false
    | .block [
        .let_ "__has_selector" _,
        .if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) _,
        .if_ (YulExpr.ident "__has_selector") [
          .switch discr cases defaultBody
        ]
      ] =>
        if selectorExprMatchesGeneratedDispatcher discr then
          yulExprUsesBuiltinExceptFunctions builtin (functionBodies.map Prod.fst) discr ||
            yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
              builtin functionBodies (selectedSwitchBody selector cases defaultBody)
        else
          yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
            builtin functionBodies [
              .block [
                .let_ "__has_selector" (.lit 0),
                .if_ (YulExpr.call "iszero" [YulExpr.ident "__has_selector"]) [],
                .if_ (YulExpr.ident "__has_selector") [
                  .switch discr cases defaultBody
                ]
              ]
            ]
    | .block stmts =>
        yulStmtsUseBuiltinOnNativeRuntimePath builtin selector functionBodies stmts
    | stmt =>
        yulStmtsUseBuiltinWithCalledFunctions (functionBodies.length + 1)
          builtin functionBodies [stmt]

  partial def yulStmtsUseBuiltinOnNativeRuntimePath
      (builtin : String)
      (selector : Nat)
      (functionBodies : List (String × List YulStmt))
      (stmts : List YulStmt) :
      Bool :=
    stmts.any (yulStmtUsesBuiltinOnNativeRuntimePath builtin selector functionBodies)
end

def nativeRuntimePathUsesBuiltin
    (builtin : String)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  yulStmtsUseBuiltinOnNativeRuntimePath builtin (nativeDispatchSelector tx)
    (yulFunctionBodies runtimeCode) runtimeCode

def nativeBlobBaseFeeRepresentable (fee : Nat) : Bool :=
  fee == EvmYul.MIN_BASE_FEE_PER_BLOB_GAS

def nativeChainIdRepresentable (chainId : Nat) : Bool :=
  chainId == EvmYul.chainId

def unsupportedNativeBlobBaseFeeError : AdapterError :=
  "native EVMYulLean blobbasefee requires representable blobBaseFee; \
  current bridge supports only EVMYulLean minimum blob gas price"

def unsupportedNativeChainIdError : AdapterError :=
  "native EVMYulLean chainid requires representable chainId; \
  current bridge supports only EVMYulLean global chain id"

def validateNativeRuntimeEnvironment
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Except AdapterError Unit :=
  if nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx &&
      !nativeChainIdRepresentable tx.chainId then
    .error unsupportedNativeChainIdError
  else if nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx &&
      !nativeBlobBaseFeeRepresentable tx.blobBaseFee then
    .error unsupportedNativeBlobBaseFeeError
  else
    .ok ()

@[simp] theorem nativeChainIdRepresentable_global :
    nativeChainIdRepresentable EvmYul.chainId = true := by
  simp [nativeChainIdRepresentable]

@[simp] theorem nativeBlobBaseFeeRepresentable_minimum :
    nativeBlobBaseFeeRepresentable EvmYul.MIN_BASE_FEE_PER_BLOB_GAS = true := by
  simp [nativeBlobBaseFeeRepresentable]

@[simp] theorem validateNativeRuntimeEnvironment_noChainId_noBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hNoBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hNoBlobBaseFee]

@[simp] theorem validateNativeRuntimeEnvironment_representableBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hBlobBaseFee]

@[simp] theorem validateNativeRuntimeEnvironment_representableEnvironment
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hChainId : nativeChainIdRepresentable tx.chainId = true)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hChainId, hBlobBaseFee]

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedChainId
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hUsesChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = true)
    (hChainId : nativeChainIdRepresentable tx.chainId = false) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeChainIdError := by
  simp [validateNativeRuntimeEnvironment, hUsesChainId, hChainId]

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hUsesBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = true)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = false) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeBlobBaseFeeError := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hUsesBlobBaseFee, hBlobBaseFee]

@[simp] theorem initialState_installsExecutionContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.code =
      contract ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.perm =
      true := by
  simp [initialState, EvmYul.Yul.State.sharedState]

@[simp] theorem initialState_installsCurrentAccountContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    ((initialState contract tx storage observableSlots).sharedState.accountMap.find?
        (natToAddress tx.thisAddress)).map (fun account => account.code) =
      some contract := by
  simp only [initialState, EvmYul.Yul.State.sharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  split <;> simp

@[simp] theorem initialState_transactionEnvironment
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.source =
      natToAddress tx.sender ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.sender =
      natToAddress tx.sender ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.codeOwner =
      natToAddress tx.thisAddress ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.timestamp =
      tx.blockTimestamp ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.number =
      tx.blockNumber ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata =
      calldataToByteArray tx.functionSelector tx.args := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_source
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.source =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_sender
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.sender =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_codeOwner
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.codeOwner =
      natToAddress tx.thisAddress := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_weiValue
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockTimestamp
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.timestamp =
      tx.blockTimestamp := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockNumber
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.number =
      tx.blockNumber := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldata
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata =
      calldataToByteArray tx.functionSelector tx.args := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldataSize
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata.size =
      4 + tx.args.length * 32 := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    calldataToByteArray_size]

private theorem byteArray_get?_append_left
    {a b : ByteArray} {i : Nat} (h : i < a.size) :
    (a ++ b).get? i = a.get? i := by
  unfold ByteArray.get?
  split
  · apply congrArg some
    have hEq : (a ++ b)[i] = a[i] := ByteArray.get_append_left h
    convert hEq using 1
  · exact False.elim (by
      rename_i hAppend
      exact hAppend (by
        rw [ByteArray.size_append]
        exact Nat.lt_of_lt_of_le h (Nat.le_add_right a.size b.size)))

/-- Reading the first ABI word from offset zero preserves every source byte
    already present in the first 32-byte window. This isolates the non-opaque
    part of EVMYulLean's `ByteArray.readBytes`; padding may still come from
    `ffi.ByteArray.zeroes`, but the dispatcher selector only depends on bytes
    0 through 3. -/
theorem readBytes_zero_get?_of_lt_source
    (source : ByteArray)
    (i : Nat)
    (hi : i < source.size)
    (hi32 : i < 32) :
    (ByteArray.readBytes source 0 32).get? i = source.get? i := by
  unfold ByteArray.readBytes
  have hsmall : (decide (0 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  have hiData : i < source.data.size := by
    simpa using hi
  have hCopySize : i < (source.copySlice 0 ByteArray.empty 0 32).size := by
    simp [ByteArray.size, ByteArray.data_copySlice]
    exact ⟨hi32, hiData⟩
  calc
    (source.copySlice 0 ByteArray.empty 0 32 ++
          ffi.ByteArray.zeroes
            { toBitVec := ↑32 -
              ↑(source.copySlice 0 ByteArray.empty 0 32).size }).get? i
        = (source.copySlice 0 ByteArray.empty 0 32).get? i :=
          byteArray_get?_append_left hCopySize
    _ = source.get? i := by
      unfold ByteArray.get?
      split
      · simp [ByteArray.get]
      · contradiction

@[simp] theorem initialState_calldataReadWord_selectorByte0
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 0 =
      some (UInt8.ofNat (tx.functionSelector / 2^24 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte1
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 1 =
      some (UInt8.ofNat (tx.functionSelector / 2^16 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte2
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 2 =
      some (UInt8.ofNat (tx.functionSelector / 2^8 % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

@[simp] theorem initialState_calldataReadWord_selectorByte3
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        0 32).get? 3 =
      some (UInt8.ofNat (tx.functionSelector % 256)) := by
  rw [readBytes_zero_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    simp [calldataToByteArray_size]
    omega
  · norm_num

private theorem byteArray_data_toList_get?_of_get?
    (ba : ByteArray)
    (i : Nat)
    (b : UInt8)
    (h : ba.get? i = some b) :
    ba.data.toList[i]? = some b := by
  unfold ByteArray.get? at h
  split at h
  · cases h
    rw [Array.getElem?_toList]
    simp [ByteArray.get]
  · contradiction

private theorem list_reverse_eq_drop4_reverse_append_four
    {α : Type}
    (xs : List α)
    (b0 b1 b2 b3 : α)
    (h0 : xs[0]? = some b0)
    (h1 : xs[1]? = some b1)
    (h2 : xs[2]? = some b2)
    (h3 : xs[3]? = some b3) :
    xs.reverse = (xs.drop 4).reverse ++ [b3, b2, b1, b0] := by
  cases xs with
  | nil => simp at h0
  | cons x0 xs =>
      simp at h0
      subst x0
      cases xs with
      | nil => simp at h1
      | cons x1 xs =>
          simp at h1
          subst x1
          cases xs with
          | nil => simp at h2
          | cons x2 xs =>
              simp at h2
              subst x2
              cases xs with
              | nil => simp at h3
              | cons x3 xs =>
                  simp at h3
                  subst x3
                  simp

/-- The decoded native calldata word has the four ABI selector bytes at the
    high end of EVMYulLean's little-endian `fromBytes'` input. Proving the
    selector value itself still needs the opaque `readBytes` result length. -/
theorem initialState_calldataReadWord_selectorPrefix
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    let bytes := ByteArray.readBytes
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata 0 32
    bytes.data.toList.reverse =
      (bytes.data.toList.drop 4).reverse ++
        [UInt8.ofNat (tx.functionSelector % 256),
         UInt8.ofNat (tx.functionSelector / 2^8 % 256),
         UInt8.ofNat (tx.functionSelector / 2^16 % 256),
         UInt8.ofNat (tx.functionSelector / 2^24 % 256)] := by
  intro bytes
  apply list_reverse_eq_drop4_reverse_append_four
  · exact byteArray_data_toList_get?_of_get? bytes 0 _
      (initialState_calldataReadWord_selectorByte0 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 1 _
      (initialState_calldataReadWord_selectorByte1 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 2 _
      (initialState_calldataReadWord_selectorByte2 contract tx storage observableSlots)
  · exact byteArray_data_toList_get?_of_get? bytes 3 _
      (initialState_calldataReadWord_selectorByte3 contract tx storage observableSlots)

/-- Recompose the four ABI selector bytes into the normalized 32-bit
    dispatcher selector. This isolates the remaining native byte-decoding proof:
    once `calldataload(0) >>> 224` is reduced to the four high calldata bytes,
    this theorem closes the arithmetic side against the interpreter oracle. -/
theorem selectorBytesAsNat (selector : Nat) :
    (selector / 2^24 % 256) * 2^24 +
      (selector / 2^16 % 256) * 2^16 +
      (selector / 2^8 % 256) * 2^8 +
      (selector % 256) =
    selector % Compiler.Constants.selectorModulus := by
  have hb0 : selector / 2^24 % 256 =
      (selector % 2^32) / 2^24 := by
    omega
  have hb1 : selector / 2^16 % 256 =
      ((selector % 2^32) % 2^24) / 2^16 := by
    omega
  have hb2 : selector / 2^8 % 256 =
      (((selector % 2^32) % 2^24) % 2^16) / 2^8 := by
    omega
  have hb3 : selector % 256 =
      ((((selector % 2^32) % 2^24) % 2^16) % 2^8) := by
    omega
  rw [hb0, hb1, hb2, hb3]
  have h1 := Nat.div_add_mod (selector % 2^32) (2^24)
  have h2 := Nat.div_add_mod ((selector % 2^32) % 2^24) (2^16)
  have h3 := Nat.div_add_mod (((selector % 2^32) % 2^24) % 2^16) (2^8)
  simp [Compiler.Constants.selectorModulus]
  omega

private theorem fromBytes'_append (xs ys : List UInt8) :
    EvmYul.fromBytes' (xs ++ ys) =
      EvmYul.fromBytes' xs + 2^(8 * xs.length) * EvmYul.fromBytes' ys := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      simp only [List.cons_append, EvmYul.fromBytes']
      rw [ih]
      rw [show 8 * (x :: xs).length = 8 + 8 * xs.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [Nat.pow_add]
      ring

private theorem fromBytes'_lt (xs : List UInt8) :
    EvmYul.fromBytes' xs < 2^(8 * xs.length) := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      unfold EvmYul.fromBytes'
      have hx : x.toFin.val < 2^8 := by
        have := x.toFin.isLt
        norm_num at this ⊢
        exact this
      simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
      have _ :=
        Nat.add_le_of_le_sub
          (Nat.one_le_pow _ _ (by decide))
          (Nat.le_sub_one_of_lt ih)
      linarith

private theorem uint256_ofNat_eq_mk
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.ofNat value = ⟨⟨value, hvalue⟩⟩ := by
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simp [Nat.mod_eq_of_lt hvalue]

private theorem uint256_eq_of_toNat_eq
    (a b : EvmYul.UInt256)
    (h : a.toNat = b.toNat) :
    a = b := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  apply congrArg EvmYul.UInt256.mk
  apply Fin.ext
  simpa [EvmYul.UInt256.toNat] using h

private theorem uint256_ofNat_toNat_of_lt
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    (EvmYul.UInt256.ofNat value).toNat = value := by
  change (Fin.ofNat EvmYul.UInt256.size value).val = value
  simp [Fin.ofNat]
  exact Nat.mod_eq_of_lt hvalue

private theorem uint256_shiftRight_224_mk_toNat
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight ⟨⟨value, hvalue⟩⟩
        ⟨⟨Compiler.Constants.selectorShift,
          by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size]⟩⟩) =
      value / 2^Compiler.Constants.selectorShift := by
  have hshift : Compiler.Constants.selectorShift < 256 := by
    norm_num [Compiler.Constants.selectorShift]
  have hg : ¬ 256 ≤
      (⟨⟨Compiler.Constants.selectorShift,
        by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size]⟩⟩ :
          EvmYul.UInt256).val := by
    change ¬ 256 ≤ Compiler.Constants.selectorShift
    exact Nat.not_le_of_lt hshift
  simp [EvmYul.UInt256.shiftRight, EvmYul.UInt256.toNat, hg,
    Nat.shiftRight_eq_div_pow]

theorem uint256_shiftRight_224_ofNat_toNat
    (value : Nat)
    (hvalue : value < EvmYul.UInt256.size) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.UInt256.ofNat value)
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      value / 2^Compiler.Constants.selectorShift := by
  rw [uint256_ofNat_eq_mk value hvalue]
  rw [uint256_ofNat_eq_mk Compiler.Constants.selectorShift
    (by norm_num [Compiler.Constants.selectorShift, EvmYul.UInt256.size])]
  exact uint256_shiftRight_224_mk_toNat value hvalue

private theorem fromBytes'_four
    (b0 b1 b2 b3 : UInt8) :
    EvmYul.fromBytes' [b3, b2, b1, b0] =
      b3.toFin.val + 2^8 * b2.toFin.val +
        2^16 * b1.toFin.val + 2^24 * b0.toFin.val := by
  simp [EvmYul.fromBytes']
  omega

private theorem fromBytes'_tail4_shift
    (b0 b1 b2 b3 : UInt8)
    (tail : List UInt8)
    (hlen : tail.length = 28) :
    EvmYul.fromBytes' (tail.reverse ++ [b3, b2, b1, b0]) / 2^224 =
      b0.toFin.val * 2^24 +
        b1.toFin.val * 2^16 +
        b2.toFin.val * 2^8 +
        b3.toFin.val := by
  rw [fromBytes'_append]
  have htailLen : tail.reverse.length = 28 := by
    simp [hlen]
  have htailBound : EvmYul.fromBytes' tail.reverse < 2^224 := by
    have h := fromBytes'_lt tail.reverse
    simpa [htailLen] using h
  rw [fromBytes'_four]
  rw [htailLen]
  norm_num
  omega

/-- Once the EVMYulLean calldata word has been reduced to a 32-byte big-endian
    list whose first four bytes are the ABI selector, shifting the corresponding
    `fromBytes'` value right by 224 yields the normalized dispatcher selector.
    The remaining native selector proof only has to connect
    `ByteArray.readBytes`/`State.calldataload` to this list shape. -/
theorem fromBytes'_selectorPrefix_shift
    (selector : Nat)
    (tail : List UInt8)
    (hlen : tail.length = 28) :
    EvmYul.fromBytes'
        (tail.reverse ++
          [UInt8.ofNat (selector % 256),
           UInt8.ofNat (selector / 2^8 % 256),
           UInt8.ofNat (selector / 2^16 % 256),
           UInt8.ofNat (selector / 2^24 % 256)]) / 2^224 =
      selector % Compiler.Constants.selectorModulus := by
  rw [fromBytes'_tail4_shift
    (UInt8.ofNat (selector / 2^24 % 256))
    (UInt8.ofNat (selector / 2^16 % 256))
    (UInt8.ofNat (selector / 2^8 % 256))
    (UInt8.ofNat (selector % 256))
    tail hlen]
  norm_num [UInt8.ofNat, UInt8.size]
  have h0 : OfNat.ofNat (selector / 16777216 % 256) % 256 =
      selector / 16777216 % 256 := by
    change (selector / 16777216 % 256) % 256 = selector / 16777216 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h1 : OfNat.ofNat (selector / 65536 % 256) % 256 =
      selector / 65536 % 256 := by
    change (selector / 65536 % 256) % 256 = selector / 65536 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h2 : OfNat.ofNat (selector / 256 % 256) % 256 =
      selector / 256 % 256 := by
    change (selector / 256 % 256) % 256 = selector / 256 % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  have h3 : OfNat.ofNat (selector % 256) % 256 =
      selector % 256 := by
    change (selector % 256) % 256 = selector % 256
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
  rw [h0, h1, h2, h3]
  simpa [Compiler.Constants.selectorModulus] using selectorBytesAsNat selector

private theorem usize_sub_toNat_of_le_32 (n : Nat) (hn : n ≤ 32) :
    ((OfNat.ofNat 32 : USize) - (OfNat.ofNat n : USize)).toNat = 32 - n := by
  rw [USize.toNat_sub]
  rw [USize.toNat_ofNat, USize.toNat_ofNat]
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits]
    have hnMod : n % 4294967296 = n := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hnMod]
    omega
  · rw [hbits]
    have hnMod : n % 18446744073709551616 = n := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hnMod]
    omega

theorem readBytes_zero_32_size (source : ByteArray) :
    (ByteArray.readBytes source 0 32).size = 32 := by
  unfold ByteArray.readBytes
  have hsmall : (decide (0 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

/-- Native selector decoding agrees with the interpreter selector by reducing
    EVMYulLean `calldataload(0) >>> 224` to the four ABI selector bytes in
    the initial bridged calldata. -/
theorem initialState_selectorExpr_native_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (initialState contract tx storage observableSlots).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      tx.functionSelector % Compiler.Constants.selectorModulus := by
  let bytes := ByteArray.readBytes
    (initialState contract tx storage observableSlots).toState.executionEnv.calldata 0 32
  have hprefix :=
    initialState_calldataReadWord_selectorPrefix contract tx storage observableSlots
  have hlen : bytes.data.toList.length = 32 := by
    have hsize := readBytes_zero_32_size
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata
    simpa [bytes, ByteArray.size] using hsize
  have htailLen : (bytes.data.toList.drop 4).length = 28 := by
    simp [hlen]
  unfold EvmYul.State.calldataload EvmYul.uInt256OfByteArray
  rw [show (EvmYul.UInt256.ofNat 0).toNat = 0 by
    change (Fin.ofNat EvmYul.UInt256.size 0).val = 0
    simp]
  rw [uint256_shiftRight_224_ofNat_toNat]
  · rw [show (ByteArray.readBytes
          (initialState contract tx storage observableSlots).toState.executionEnv.calldata
          0 32).data.toList.reverse =
        bytes.data.toList.reverse by rfl]
    rw [hprefix]
    exact fromBytes'_selectorPrefix_shift tx.functionSelector
      (bytes.data.toList.drop 4) htailLen
  · have hlt := fromBytes'_lt bytes.data.toList.reverse
    have hrevLen : bytes.data.toList.reverse.length = 32 := by
      simp [hlen]
    simpa [hrevLen, EvmYul.UInt256.size] using hlt

theorem initialState_selectorExpr_native_value_of_readBytes_size
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (_hReadBytesSize :
      ∀ source : ByteArray, (ByteArray.readBytes source 0 32).size = 32) :
    EvmYul.UInt256.toNat
      (EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (initialState contract tx storage observableSlots).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
      tx.functionSelector % Compiler.Constants.selectorModulus :=
  initialState_selectorExpr_native_value contract tx storage observableSlots

/-- The native lowerer maps the generated dispatcher selector expression to
    EVMYulLean's primitive `SHR(CALLDATALOAD(0), 224)` shape. -/
theorem lowerExprNative_selectorExpr :
    Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr =
      .Call (.inl (EvmYul.Operation.SHR : EvmYul.Operation .Yul))
        [.Lit (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift),
         .Call (.inl (EvmYul.Operation.CALLDATALOAD : EvmYul.Operation .Yul))
          [.Lit (EvmYul.UInt256.ofNat 0)]] := by
  rw [show Compiler.Proofs.YulGeneration.selectorExpr =
      YulExpr.call "shr"
        [YulExpr.lit Compiler.Constants.selectorShift,
         YulExpr.call "calldataload" [YulExpr.lit 0]] by rfl]
  rw [Backends.lowerExprNative_call_runtimePrimOp "shr" _
    (EvmYul.Operation.SHR : EvmYul.Operation .Yul) (by rfl)]
  change EvmYul.Yul.Ast.Expr.Call (Sum.inl EvmYul.Operation.SHR)
      [Backends.lowerExprNative (YulExpr.lit Compiler.Constants.selectorShift),
       Backends.lowerExprNative (YulExpr.call "calldataload" [YulExpr.lit 0])] = _
  rw [Backends.lowerExprNative_call_runtimePrimOp "calldataload" _
    (EvmYul.Operation.CALLDATALOAD : EvmYul.Operation .Yul) (by rfl)]
  simp [Backends.lowerExprNative]

@[simp] theorem step_calldataload_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATALOAD none
        (.Ok shared store) [offset] =
      .ok (.Ok shared store,
        some (EvmYul.State.calldataload shared.toState offset)) := by
  rfl

@[simp] theorem step_shr_ok
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SHR none state [shift, value] =
      .ok (state, some (EvmYul.UInt256.shiftRight value shift)) := by
  rfl

@[simp] theorem step_eq_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.EQ none state [left, right] =
      .ok (state, some (EvmYul.UInt256.eq left right)) := by
  rfl

@[simp] theorem step_iszero_ok
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ISZERO none state [value] =
      .ok (state, some (EvmYul.UInt256.isZero value)) := by
  rfl

@[simp] theorem step_and_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.AND none state [left, right] =
      .ok (state, some (EvmYul.UInt256.land left right)) := by
  rfl

@[simp] theorem primCall_calldataload_ok
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) (.Ok shared store)
        EvmYul.Operation.CALLDATALOAD [offset] =
      .ok (.Ok shared store,
        [EvmYul.State.calldataload shared.toState offset]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_shr_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SHR [shift, value] =
      .ok (state, [EvmYul.UInt256.shiftRight value shift]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_eq_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.EQ [left, right] =
      .ok (state, [EvmYul.UInt256.eq left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_iszero_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ISZERO [value] =
      .ok (state, [EvmYul.UInt256.isZero value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_and_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.AND [left, right] =
      .ok (state, [EvmYul.UInt256.land left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

/-- Native evaluation of the lowered generated selector expression peels to
    exactly EVMYulLean `calldataload(0)` followed by `shr(224, ...)`. -/
theorem eval_lowerExprNative_selectorExpr_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload shared.toState (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) := by
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', Compiler.Constants.selectorShift]

theorem eval_lowerExprNative_selectorExpr_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus)) := by
  rw [eval_lowerExprNative_selectorExpr_ok]
  have hv :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    apply uint256_eq_of_toNat_eq
    rw [show EvmYul.UInt256.toNat
        (EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload
            (EvmYul.SharedState.toState
              (initialState contract tx storage observableSlots).sharedState)
            (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) =
        tx.functionSelector % Compiler.Constants.selectorModulus by
      simpa [EvmYul.Yul.State.toState] using
        initialState_selectorExpr_native_value contract tx storage observableSlots]
    rw [uint256_ofNat_toNat_of_lt]
    have hmod :
        tx.functionSelector % Compiler.Constants.selectorModulus <
          Compiler.Constants.selectorModulus := by
      exact Nat.mod_lt _ (by norm_num [Compiler.Constants.selectorModulus])
    have hsel :
        Compiler.Constants.selectorModulus < EvmYul.UInt256.size := by
      norm_num [Compiler.Constants.selectorModulus, EvmYul.UInt256.size]
    exact Nat.lt_trans hmod hsel
  rw [hv]

/-- If the head statement of a native block finishes normally, execution
    continues with the remaining block statements at the same decremented fuel. -/
theorem exec_block_cons_ok
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next final : EvmYul.Yul.State)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next)
    (hTail : EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next = .ok final) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .ok final := by
  simp [EvmYul.Yul.exec, hHead, hTail]

/-- Native `if` reduction for a zero guard. -/
theorem exec_if_eval_zero
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (hEval :
      EvmYul.Yul.eval fuel' cond codeOverride state =
        .ok (next, (⟨0⟩ : EvmYul.Literal))) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .ok next := by
  simp [EvmYul.Yul.exec, hEval]

/-- Native `if` reduction for a nonzero guard. -/
theorem exec_if_eval_nonzero
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next final : EvmYul.Yul.State)
    (value : EvmYul.Literal)
    (hEval : EvmYul.Yul.eval fuel' cond codeOverride state = .ok (next, value))
    (hNe : value ≠ (⟨0⟩ : EvmYul.Literal))
    (hBody : EvmYul.Yul.exec fuel' (.Block body) codeOverride next = .ok final) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .ok final := by
  simp [EvmYul.Yul.exec, hEval, hNe, hBody]

/-- Native evaluation of the lazy lowered switch guard peels to the exact
    EVMYulLean `AND(ISZERO(matched), EQ(discr, tag))` value.

This is the next bridge after selector evaluation: selected-case execution can
now reason from concrete discriminator and matched-temporary bindings instead
of re-opening nested primitive-call evaluation. -/
theorem eval_nativeSwitchGuardedMatch_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state,
      EvmYul.UInt256.land
        (EvmYul.UInt256.isZero state[matchedName]!)
        (EvmYul.UInt256.eq state[discrName]! (EvmYul.UInt256.ofNat tag))) := by
  simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
    EvmYul.Yul.cons', EvmYul.Yul.head']

/-- The selected lowered switch case has a nonzero guard while no previous case
    has marked the switch matched and the discriminator equals the case tag. -/
theorem eval_nativeSwitchGuardedMatch_hit_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched, hDiscr]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero]
  decide

/-- Bitwise `and` with a zero left operand stays zero for native UInt256 words. -/
private theorem uint256_land_zero_left (value : EvmYul.UInt256) :
    EvmYul.UInt256.land (EvmYul.UInt256.ofNat 0) value =
      EvmYul.UInt256.ofNat 0 := by
  cases value with
  | mk raw =>
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change (0 &&& (raw : Nat)) % EvmYul.UInt256.size = 0
    simp [Nat.zero_and]

/-- Once the lazy lowered switch matched flag is set, later case guards evaluate
    to zero independently of the discriminator value. -/
theorem eval_nativeSwitchGuardedMatch_matched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched]
  rw [show EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 1) =
      EvmYul.UInt256.ofNat 0 by decide]
  rw [uint256_land_zero_left]

/-- Native `if` execution for the selected lowered switch case.  This packages
    guard evaluation with the existing nonzero-`if` reduction so the remaining
    case-chain proof can focus on matching/freshness invariants. -/
theorem exec_if_nativeSwitchGuardedMatch_hit
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody : EvmYul.Yul.exec 8 (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok final := by
  exact exec_if_eval_nonzero 8 _ body codeOverride state state final
    (EvmYul.UInt256.ofNat 1)
    (eval_nativeSwitchGuardedMatch_hit_ok state codeOverride discrName matchedName tag
      hMatched hDiscr)
    (by decide)
    hBody

/-- Native `if` execution skips a later lowered switch case after an earlier case
    has set the matched flag. -/
theorem exec_if_nativeSwitchGuardedMatch_matched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  exact exec_if_eval_zero 8 _ body codeOverride state state
    (eval_nativeSwitchGuardedMatch_matched_ok state codeOverride discrName matchedName tag
      hMatched)

@[simp] theorem initialState_unbridgedEnvironmentDefaults
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.baseFeePerGas =
      0 ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.blobGasUsed =
      (0 : UInt64) ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.excessBlobGas =
      (0 : UInt64) ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.blobVersionedHashes =
      [] ∧
    EvmYul.State.chainId
        (initialState contract tx storage observableSlots).sharedState.toState =
      EvmYul.UInt256.ofNat EvmYul.chainId := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader, EvmYul.State.chainId]

/-- Project the account storage for the current contract back to Verity's
    `Nat → Nat` storage view. -/
def projectStorageFromState (tx : YulTransaction) (state : EvmYul.Yul.State) :
    Nat → Nat :=
  extractStorage state.sharedState (natToAddress tx.thisAddress)

/-- Projecting final native storage reads the current contract account storage
    entry for the requested slot. -/
@[simp] theorem projectStorageFromState_accountStorageSlot
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (value : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = some value) :
    projectStorageFromState tx state slot = uint256ToNat value := by
  simp [projectStorageFromState, extractStorage, hAccount, hSlot]

/-- Projecting final native storage defaults to zero when the current contract
    account has no native storage entry for the requested slot. -/
@[simp] theorem projectStorageFromState_missingAccountStorageSlot
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = none) :
    projectStorageFromState tx state slot = 0 := by
  simp [projectStorageFromState, extractStorage, hAccount, hSlot]

/-- Projecting final native storage defaults to zero when the current contract
    account is absent from the native account map. -/
@[simp] theorem projectStorageFromState_missingAccount
    (tx : YulTransaction)
    (state : EvmYul.Yul.State)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        none) :
    projectStorageFromState tx state slot = 0 := by
  simp [projectStorageFromState, extractStorage, hAccount]

/-- Native initial-state storage materialization agrees with Verity storage on
    every explicit observable slot. Slots and values are interpreted in the
    EVM word domain, so the result is modulo `UInt256.size`. -/
theorem initialState_observableStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) slot =
      storage slot % EvmYul.UInt256.size := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  simp only at *
  have h := storageLookup_projectStorage storage observableSlots slot hSlot hRange
  unfold storageLookup at h
  generalize hfind : Batteries.RBMap.find? (projectStorage storage observableSlots)
      (natToUInt256 slot) = found at h ⊢
  cases found <;>
    simpa [uint256ToNat, EvmYul.UInt256.toNat] using h

/-- Native initial-state storage materialization defaults omitted observable
    pre-state slots to zero. The in-range hypotheses rule out modular aliasing
    through the EVM word key used by the finite native storage map. -/
theorem initialState_omittedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) slot = 0 := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  simp only
  have h := foldl_insert_find_not_mem storage observableSlots slot hNotSlot
    hRange hSlotRange (Batteries.RBMap.empty : EvmYul.Storage)
  have hNone :
      (projectStorage storage observableSlots).find? (natToUInt256 slot) = none := by
    simpa [projectStorage] using h
  rw [hNone]

/-- Decode one 32-byte big-endian word from an EVMYulLean byte array. -/
def byteArrayWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => (acc * 256 + ((bytes.get? (offset + i)).getD 0).toNat) %
      Compiler.Constants.evmModulus)
    0

/-- Decode the word-granular payload used by Verity's proof-side log model. -/
def byteArrayLogWords (bytes : ByteArray) : List Nat :=
  (List.range (bytes.size / 32)).map (fun i => byteArrayWord bytes (i * 32))

/-- Project native EVMYulLean logs to the current Verity observable event shape:
    topics followed by word-aligned log data. -/
def projectLogEntry (entry : EvmYul.LogEntry) : List Nat :=
  entry.topics.toList.map uint256ToNat ++ byteArrayLogWords entry.data

def projectLogsFromState (state : EvmYul.Yul.State) : List (List Nat) :=
  state.sharedState.substate.logSeries.toList.map projectLogEntry

@[simp] theorem projectLogEntry_topicsAndWordData
    (entry : EvmYul.LogEntry) :
    projectLogEntry entry =
      entry.topics.toList.map uint256ToNat ++ byteArrayLogWords entry.data := by
  rfl

@[simp] theorem projectLogsFromState_logSeries
    (state : EvmYul.Yul.State) :
    projectLogsFromState state =
      state.sharedState.substate.logSeries.toList.map projectLogEntry := by
  rfl

/-- Project a native Yul halt produced by `return`/`stop` to Verity's single-word
    return observable. EVMYulLean represents `stop` as `YulHalt _ 0`; `return`
    goes through `H_return`, matching the proof oracle's 32-byte return case. -/
def projectHaltReturn (state : EvmYul.Yul.State) (haltValue : EvmYul.Yul.Ast.Literal) :
    Option Nat :=
  if haltValue = ⟨0⟩ then
    none
  else if state.sharedState.H_return.size = 32 then
    some (byteArrayWord state.sharedState.H_return 0)
  else
    some 0

@[simp] theorem projectHaltReturn_stop
    (state : EvmYul.Yul.State) :
    projectHaltReturn state ⟨0⟩ = none := by
  simp [projectHaltReturn]

@[simp] theorem projectHaltReturn_32ByteReturn
    (state : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hHalt : haltValue ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size = 32) :
    projectHaltReturn state haltValue =
      some (byteArrayWord state.sharedState.H_return 0) := by
  simp [projectHaltReturn, hHalt, hSize]

/-- Until wider returndata support lands, a non-`stop` halt with a native return
    buffer whose size is not exactly one ABI word projects to the conservative
    single-word fallback used by the current proof-side observable model. -/
@[simp] theorem projectHaltReturn_non32ByteReturn
    (state : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hHalt : haltValue ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size ≠ 32) :
    projectHaltReturn state haltValue = some 0 := by
  simp [projectHaltReturn, hHalt, hSize]

/-- The dispatcher-block execution that `EvmYul.Yul.callDispatcher` performs
    after its initial fuel check and empty-argument call-frame setup.

Keeping this expression named lets the native/interpreter bridge target
statement execution of the lowered dispatcher body directly, instead of
re-opening the full `callDispatcher` wrapper at each EndToEnd proof site. -/
def callDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] []
      [initial.executionEnv.code.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  match EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState with
  | .error err => .error err
  | .ok finalState =>
      let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
      .ok (restored, List.map finalState.lookup! dispatcherDef.rets)

/-- Dispatcher-block execution specialized to the lowered contract dispatcher
    rather than the state-installed dispatcher lookup.

For states built by `initialState`, this is definitionally the next proof
target after `callDispatcherBlockResult`: native execution of the lowered
contract's dispatcher statement. -/
def contractDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  match EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState with
  | .error err => .error err
  | .ok finalState =>
      let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
      .ok (restored, List.map finalState.lookup! dispatcherDef.rets)

/-- Raw native execution of the lowered contract dispatcher block, before the
    `callDispatcher`-style state restoration and return-list projection. -/
def contractDispatcherExecResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    Except EvmYul.Yul.Exception EvmYul.Yul.State :=
  let dispatcherDef :=
    EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
  let callState := EvmYul.Yul.State.mkOk (initial.initcall dispatcherDef.params [])
  EvmYul.Yul.exec fuel' (.Block dispatcherDef.body) (some contract) callState

/-- The projected dispatcher-block result is just raw lowered-dispatcher
    execution followed by the same restoration/projection used by
    `callDispatcher`. -/
theorem contractDispatcherBlockResult_eq_execResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    contractDispatcherBlockResult fuel' contract initial =
      let dispatcherDef :=
        EvmYul.Yul.Ast.FunctionDefinition.Def [] [] [contract.dispatcher]
      match contractDispatcherExecResult fuel' contract initial with
      | .error err => .error err
      | .ok finalState =>
          let restored := finalState.reviveJump.overwrite? initial |>.setStore initial
          .ok (restored, List.map finalState.lookup! dispatcherDef.rets) := by
  simp [contractDispatcherBlockResult, contractDispatcherExecResult]

/-- `initialState` installs the lowered contract as the execution contract, so
    the dispatcher-block target can be rewritten to the lowered contract's own
    dispatcher. -/
theorem callDispatcherBlockResult_initialState_eq_contractDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat) :
    callDispatcherBlockResult fuel' contract
        (initialState contract tx storage observableSlots) =
      contractDispatcherBlockResult fuel' contract
        (initialState contract tx storage observableSlots) := by
  have hcode :
      (initialState contract tx storage observableSlots).executionEnv.code =
        contract := by
    simp [initialState, EvmYul.Yul.State.executionEnv]
  simp [callDispatcherBlockResult, contractDispatcherBlockResult, hcode]

@[simp] theorem callDispatcher_zero
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    EvmYul.Yul.callDispatcher 0 (some contract) initial =
      .error EvmYul.Yul.Exception.OutOfFuel := by
  simp [EvmYul.Yul.callDispatcher]

/-- `callDispatcher` is exactly execution of the installed dispatcher block
    once fuel and call-frame setup have been peeled away. -/
theorem callDispatcher_succ_eq_callDispatcherBlockResult
    (fuel' : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (initial : EvmYul.Yul.State) :
    EvmYul.Yul.callDispatcher (Nat.succ fuel') (some contract) initial =
      callDispatcherBlockResult fuel' contract initial := by
  simp [EvmYul.Yul.callDispatcher, callDispatcherBlockResult]
  cases
    EvmYul.Yul.exec fuel'
      (.Block
        (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
          [initial.executionEnv.code.dispatcher]).body)
      (some contract)
      (EvmYul.Yul.State.mkOk
        (initial.initcall
          (EvmYul.Yul.Ast.FunctionDefinition.Def [] []
            [initial.executionEnv.code.dispatcher]).params [])) <;> rfl

/-- Convert a native `callDispatcher` result to the current Verity observable
    result shape. Reverts and hard native errors conservatively roll storage
    back to the supplied initial storage function. -/
def projectResult
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    YulResult :=
  match result with
  | .ok (state, values) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := values.head?.map uint256ToNat
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := initialEvents ++ projectLogsFromState state }
  | .error (.YulHalt state value) =>
      let finalStorage := projectStorageFromState tx state
      { success := true
        returnValue := projectHaltReturn state value
        finalStorage := finalStorage
        finalMappings := Compiler.Proofs.storageAsMappings finalStorage
        events := initialEvents ++ projectLogsFromState state }
  | .error _ =>
      { success := false
        returnValue := none
        finalStorage := initialStorage
        finalMappings := Compiler.Proofs.storageAsMappings initialStorage
        events := initialEvents }

@[simp] theorem projectResult_ok
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    projectResult tx initialStorage initialEvents (.ok (state, values)) =
    { success := true
      returnValue := values.head?.map uint256ToNat
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  rfl

@[simp] theorem projectResult_yulHalt
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := projectHaltReturn state value
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  rfl

@[simp] theorem projectResult_ok_events
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents (.ok (state, values))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_ok_success
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).success = true := by
  rfl

@[simp] theorem projectResult_ok_returnValue
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).returnValue =
      values.head?.map uint256ToNat := by
  rfl

@[simp] theorem projectResult_ok_finalMappings
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_ok_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (value : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = some value) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage slot = uint256ToNat value := by
  simp [projectResult, projectStorageFromState_accountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_ok_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage slot = 0 := by
  simp [projectResult, projectStorageFromState_missingAccount, hAccount]

@[simp] theorem projectResult_ok_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = none) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage slot = 0 := by
  simp [projectResult, projectStorageFromState_missingAccountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_yulHalt_events
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_yulHalt_success
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).success = true := by
  rfl

@[simp] theorem projectResult_yulHalt_returnValue
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).returnValue =
      projectHaltReturn state value := by
  rfl

@[simp] theorem projectResult_yulHalt_finalMappings
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_yulHalt_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (slotValue : EvmYul.UInt256)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = some slotValue) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage slot =
        uint256ToNat slotValue := by
  simp [projectResult, projectStorageFromState_accountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_yulHalt_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage slot = 0 := by
  simp [projectResult, projectStorageFromState_missingAccount, hAccount]

@[simp] theorem projectResult_yulHalt_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (account : EvmYul.Account .Yul)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        some account)
    (hSlot : account.storage.find? (natToUInt256 slot) = none) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage slot = 0 := by
  simp [projectResult, projectStorageFromState_missingAccountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_stop
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state ⟨0⟩)) =
    { success := true
      returnValue := none
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult]

@[simp] theorem projectResult_32ByteReturn
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (hHalt : value ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size = 32) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := some (byteArrayWord state.sharedState.H_return 0)
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult, hHalt, hSize]

@[simp] theorem projectResult_non32ByteReturn
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (hHalt : value ≠ ⟨0⟩)
    (hSize : state.sharedState.H_return.size ≠ 32) :
    projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value)) =
    { success := true
      returnValue := some 0
      finalStorage := projectStorageFromState tx state
      finalMappings :=
        Compiler.Proofs.storageAsMappings (projectStorageFromState tx state)
      events := initialEvents ++ projectLogsFromState state } := by
  simp [projectResult, hHalt, hSize]

@[simp] theorem projectResult_revert
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert) =
    { success := false
      returnValue := none
      finalStorage := initialStorage
      finalMappings := Compiler.Proofs.storageAsMappings initialStorage
      events := initialEvents } := by
  rfl

@[simp] theorem projectResult_revert_events
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).events =
      initialEvents := by
  rfl

@[simp] theorem projectResult_revert_success
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).success = false := by
  rfl

@[simp] theorem projectResult_revert_returnValue
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).returnValue = none := by
  rfl

@[simp] theorem projectResult_revert_finalMappings
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalMappings =
      Compiler.Proofs.storageAsMappings initialStorage := by
  rfl

@[simp] theorem projectResult_revert_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (slot : Nat) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalStorage slot =
      initialStorage slot := by
  rfl

@[simp] theorem projectResult_hardError
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    projectResult tx initialStorage initialEvents (.error err) =
    { success := false
      returnValue := none
      finalStorage := initialStorage
      finalMappings := Compiler.Proofs.storageAsMappings initialStorage
      events := initialEvents } := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_success
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).success = false := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_returnValue
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).returnValue = none := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (slot : Nat)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).finalStorage slot =
      initialStorage slot := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_finalMappings
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).finalMappings =
      Compiler.Proofs.storageAsMappings initialStorage := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_hardError_events
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).events =
      initialEvents := by
  cases err with
  | YulHalt state value =>
      exact False.elim (hNotHalt state value rfl)
  | InvalidArguments => rfl
  | NotEncodableRLP => rfl
  | InvalidInstruction => rfl
  | OutOfFuel => rfl
  | StaticModeViolation => rfl
  | MissingContract s => rfl
  | MissingContractFunction s => rfl
  | InvalidExpression => rfl
  | YulEXTCODESIZENotImplemented => rfl
  | Revert => rfl

@[simp] theorem projectResult_finalMappings
    (tx : YulTransaction)
    (initialStorage : Nat → Nat)
    (initialEvents : List (List Nat))
    (result :
      Except EvmYul.Yul.Exception
        (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal)) :
    (projectResult tx initialStorage initialEvents result).finalMappings =
      Compiler.Proofs.storageAsMappings
        (projectResult tx initialStorage initialEvents result).finalStorage := by
  cases result with
  | ok value =>
      cases value with
      | mk state values => rfl
  | error err =>
      cases err <;> rfl

/-- Lower and execute Verity runtime Yul through EVMYulLean's native
    dispatcher. -/
def interpretRuntimeNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (events : List (List Nat) := []) :
    Except AdapterError YulResult := do
  let contract ← lowerRuntimeContractNative runtimeCode
  validateNativeRuntimeEnvironment runtimeCode tx
  let initial := initialState contract tx storage observableSlots
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage events result)

@[simp] theorem interpretRuntimeNative_loweringError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (err : AdapterError)
    (hLower : lowerRuntimeContractNative runtimeCode = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, hLower]
  rfl

@[simp] theorem interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (EvmYul.Yul.callDispatcher fuel (some contract)
          (initialState contract tx storage observableSlots))) := by
  rw [interpretRuntimeNative, hLower, hEnv]
  rfl

@[simp] theorem interpretRuntimeNative_environmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : Nat → Nat)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (err : AdapterError)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, hLower, hEnv]
  rfl

/-- Native EVMYulLean execution target for emitted IR-contract runtime Yul.

This is the executable target that #1737 will promote into the public theorem
path once the state/result bridge lemmas are proved. It intentionally returns
`Except AdapterError YulResult` today because native lowering can still fail
closed for duplicate helper definitions or unsupported runtime shapes.

The observable slot set is explicit because the native state bridge only
materializes pre-state storage for the listed slots. Passing `[]` is valid for
storage-free smoke tests, but storage-reading callers must provide every slot
they intend the native EVMYulLean state to observe.
-/
def interpretIRRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    Except AdapterError YulResult :=
  interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
    (YulTransaction.ofIR tx) state.storage observableSlots state.events

@[simp] theorem interpretIRRuntimeNative_eq_interpretRuntimeNative
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      interpretRuntimeNative fuel (Compiler.emitYul contract).runtimeCode
        (YulTransaction.ofIR tx) state.storage observableSlots state.events := by
  rfl

@[simp] theorem interpretIRRuntimeNative_loweringError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (err : AdapterError)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      .error err) :
    interpretIRRuntimeNative fuel contract tx state observableSlots = .error err := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative, hLower]
  rfl

@[simp] theorem interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative fuel irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (EvmYul.Yul.callDispatcher fuel (some nativeContract)
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            observableSlots))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative, hLower, hEnv]
  rfl

end Compiler.Proofs.YulGeneration.Backends.Native
