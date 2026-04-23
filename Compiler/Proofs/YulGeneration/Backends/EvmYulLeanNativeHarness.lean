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

partial def yulExprUsesBuiltin (builtin : String) : YulExpr → Bool
  | .call func args => func == builtin || args.any (yulExprUsesBuiltin builtin)
  | _ => false

partial def yulExprCalledFunctions : YulExpr → List String
  | .call func args => func :: args.flatMap yulExprCalledFunctions
  | _ => []

mutual
  partial def yulStmtUsesBuiltin (builtin : String) : YulStmt → Bool
    | .let_ _ value => yulExprUsesBuiltin builtin value
    | .letMany _ value => yulExprUsesBuiltin builtin value
    | .assign _ value => yulExprUsesBuiltin builtin value
    | .expr e => yulExprUsesBuiltin builtin e
    | .if_ cond body =>
        yulExprUsesBuiltin builtin cond || yulStmtsUseBuiltin builtin body
    | .for_ init cond post body =>
        yulStmtsUseBuiltin builtin init ||
          yulExprUsesBuiltin builtin cond ||
          yulStmtsUseBuiltin builtin post ||
          yulStmtsUseBuiltin builtin body
    | .switch discr cases defaultBody =>
        yulExprUsesBuiltin builtin discr ||
          cases.any (fun (_, body) => yulStmtsUseBuiltin builtin body) ||
          defaultBody.any (yulStmtsUseBuiltin builtin)
    | .block stmts => yulStmtsUseBuiltin builtin stmts
    | .funcDef _ _ _ body => yulStmtsUseBuiltin builtin body
    | .comment _ | .leave => false

  partial def yulStmtsUseBuiltin (builtin : String) (stmts : List YulStmt) : Bool :=
    stmts.any (yulStmtUsesBuiltin builtin)
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
  yulStmtsUseBuiltin builtin stmts ||
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
          yulExprUsesBuiltin builtin discr ||
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
