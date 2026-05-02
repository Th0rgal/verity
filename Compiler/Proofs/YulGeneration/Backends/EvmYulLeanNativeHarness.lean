import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanAdapter
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanStateBridge
import Compiler.Proofs.YulGeneration.ReferenceOracle.Semantics
import Compiler.Codegen
import EvmYul.Yul.Interpreter
import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration (IRStorageWord IRStorageSlot)

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
    (storage : IRStorageSlot → IRStorageWord)
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

/-! ## Native Storage Materialization -/

partial def yulExprLiteralStorageReadSlots : YulExpr → List Nat
  | .call "sload" [.lit slot] => [slot]
  | .call _ args => args.flatMap yulExprLiteralStorageReadSlots
  | _ => []

mutual
  partial def yulStmtLiteralStorageReadSlots : YulStmt → List Nat
    | .let_ _ value => yulExprLiteralStorageReadSlots value
    | .letMany _ value => yulExprLiteralStorageReadSlots value
    | .assign _ value => yulExprLiteralStorageReadSlots value
    | .expr e => yulExprLiteralStorageReadSlots e
    | .if_ cond body =>
        yulExprLiteralStorageReadSlots cond ++ yulStmtsLiteralStorageReadSlots body
    | .for_ init cond post body =>
        yulStmtsLiteralStorageReadSlots init ++
          yulExprLiteralStorageReadSlots cond ++
          yulStmtsLiteralStorageReadSlots post ++
          yulStmtsLiteralStorageReadSlots body
    | .switch discr cases defaultBody =>
        yulExprLiteralStorageReadSlots discr ++
          cases.flatMap (fun entry => yulStmtsLiteralStorageReadSlots entry.2) ++
          (defaultBody.map yulStmtsLiteralStorageReadSlots).getD []
    | .block stmts => yulStmtsLiteralStorageReadSlots stmts
    | .funcDef _ _ _ body => yulStmtsLiteralStorageReadSlots body
    | .comment _ | .leave => []

  partial def yulStmtsLiteralStorageReadSlots (stmts : List YulStmt) : List Nat :=
    stmts.flatMap yulStmtLiteralStorageReadSlots
end

def materializedStorageSlots
    (runtimeCode : List YulStmt)
    (observableSlots : List Nat) :
    List Nat :=
  -- Slot zero is the common simple-storage getter slot and is harmless to
  -- materialize twice; keeping it explicit avoids depending on the opaque
  -- partial literal-read collector for baseline storage projection facts.
  0 :: yulStmtsLiteralStorageReadSlots runtimeCode ++ observableSlots

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

/-! ## Generated Native Runtime Fragment -/

mutual
  partial def yulStmtContainsFuncDef : YulStmt → Bool
    | .funcDef _ _ _ _ => true
    | .if_ _ body => yulStmtsContainFuncDef body
    | .for_ init _ post body =>
        yulStmtsContainFuncDef init ||
          yulStmtsContainFuncDef post ||
          yulStmtsContainFuncDef body
    | .switch _ cases defaultBody =>
        cases.any (fun entry => yulStmtsContainFuncDef entry.2) ||
          defaultBody.any yulStmtsContainFuncDef
    | .block stmts => yulStmtsContainFuncDef stmts
    | .comment _ | .let_ _ _ | .letMany _ _ | .assign _ _ | .expr _ | .leave => false

  partial def yulStmtsContainFuncDef (stmts : List YulStmt) : Bool :=
    stmts.any yulStmtContainsFuncDef
end

def yulRuntimeTopLevelFunctionNames (runtimeCode : List YulStmt) : List String :=
  runtimeCode.filterMap fun
    | .funcDef name _ _ _ => some name
    | _ => none

def yulRuntimeDispatcherStmts (runtimeCode : List YulStmt) : List YulStmt :=
  runtimeCode.filter fun
    | .funcDef _ _ _ _ => false
    | _ => true

def stringListHasDuplicate : List String → Bool
  | [] => false
  | name :: rest => rest.contains name || stringListHasDuplicate rest

def generatedRuntimeFunctionNamesUnique (runtimeCode : List YulStmt) : Bool :=
  !stringListHasDuplicate (yulRuntimeTopLevelFunctionNames runtimeCode)

def generatedRuntimeDispatcherHasNoFuncDefs (runtimeCode : List YulStmt) : Bool :=
  !yulStmtsContainFuncDef (yulRuntimeDispatcherStmts runtimeCode)

def generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs
    (runtimeCode : List YulStmt) :
    Bool :=
  (yulFunctionBodies runtimeCode).all fun entry => !yulStmtsContainFuncDef entry.2

/-- Executable characterization for the generated runtime shape that the
    native EVMYulLean lowering path currently accepts: top-level `funcDef`
    statements are helpers, dispatcher statements contain no nested function
    definitions, helper names are unique, and helper bodies themselves contain
    no nested function definitions. -/
def generatedRuntimeNativeFragment (runtimeCode : List YulStmt) : Bool :=
  generatedRuntimeFunctionNamesUnique runtimeCode &&
    generatedRuntimeDispatcherHasNoFuncDefs runtimeCode &&
    generatedRuntimeFunctionBodiesHaveNoNestedFuncDefs runtimeCode

def unsupportedGeneratedRuntimeNativeFragmentError : AdapterError :=
  "native EVMYulLean generated runtime fragment check failed"

def validateGeneratedRuntimeNativeFragment
    (runtimeCode : List YulStmt) :
    Except AdapterError Unit :=
  if generatedRuntimeNativeFragment runtimeCode then
    .ok ()
  else
    .error unsupportedGeneratedRuntimeNativeFragmentError

@[simp] theorem validateGeneratedRuntimeNativeFragment_ok
    (runtimeCode : List YulStmt)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true) :
    validateGeneratedRuntimeNativeFragment runtimeCode = .ok () := by
  simp [validateGeneratedRuntimeNativeFragment, hFragment]

@[simp] theorem validateGeneratedRuntimeNativeFragment_error
    (runtimeCode : List YulStmt)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = false) :
    validateGeneratedRuntimeNativeFragment runtimeCode =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  simp [validateGeneratedRuntimeNativeFragment, hFragment]

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

def unsupportedNativeHeaderBuiltinNames : List String :=
  ["coinbase", "difficulty", "prevrandao", "gaslimit", "basefee", "gasprice"]

def nativeRuntimePathUsesAnyBuiltin
    (builtins : List String)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  builtins.any fun builtin => nativeRuntimePathUsesBuiltin builtin runtimeCode tx

def nativeRuntimePathUsesUnsupportedHeaderBuiltin
    (runtimeCode : List YulStmt)
    (tx : YulTransaction) :
    Bool :=
  nativeRuntimePathUsesAnyBuiltin unsupportedNativeHeaderBuiltinNames runtimeCode tx

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

def unsupportedNativeHeaderBuiltinError : AdapterError :=
  "native EVMYulLean selected runtime path uses a header builtin that is not \
  represented in Verity's YulTransaction bridge"

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
  else if nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx then
    .error unsupportedNativeHeaderBuiltinError
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
    (hNoBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = false)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hNoBlobBaseFee, hNoHeader]

@[simp] theorem validateNativeRuntimeEnvironment_representableBlobBaseFee
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hBlobBaseFee, hNoHeader]

@[simp] theorem validateNativeRuntimeEnvironment_representableEnvironment
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hChainId : nativeChainIdRepresentable tx.chainId = true)
    (hBlobBaseFee :
      nativeBlobBaseFeeRepresentable tx.blobBaseFee = true)
    (hNoHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = false) :
    validateNativeRuntimeEnvironment runtimeCode tx = .ok () := by
  simp [validateNativeRuntimeEnvironment, hChainId, hBlobBaseFee, hNoHeader]

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

@[simp] theorem validateNativeRuntimeEnvironment_unsupportedHeaderBuiltin
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (hNoChainId : nativeRuntimePathUsesBuiltin "chainid" runtimeCode tx = false)
    (hNoBlobBaseFee : nativeRuntimePathUsesBuiltin "blobbasefee" runtimeCode tx = false)
    (hUsesHeader :
      nativeRuntimePathUsesUnsupportedHeaderBuiltin runtimeCode tx = true) :
    validateNativeRuntimeEnvironment runtimeCode tx =
      .error unsupportedNativeHeaderBuiltinError := by
  simp [validateNativeRuntimeEnvironment, hNoChainId, hNoBlobBaseFee, hUsesHeader]

@[simp] theorem initialState_installsExecutionContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.code =
      contract ∧
    (initialState contract tx storage observableSlots).sharedState.executionEnv.perm =
      true := by
  simp [initialState, EvmYul.Yul.State.sharedState]

@[simp] theorem initialState_installsCurrentAccountContract
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.source =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_sender
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.sender =
      natToAddress tx.sender := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_codeOwner
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.codeOwner =
      natToAddress tx.thisAddress := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_weiValue
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.weiValue =
      natToUInt256 tx.msgValue := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockTimestamp
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.timestamp =
      tx.blockTimestamp := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_blockNumber
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.header.number =
      tx.blockNumber := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldata
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    (initialState contract tx storage observableSlots).sharedState.executionEnv.calldata =
      calldataToByteArray tx.functionSelector tx.args := by
  simp [initialState, EvmYul.Yul.State.sharedState, YulState.initial, toSharedState,
    mkBlockHeader]

@[simp] theorem initialState_calldataSize
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
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

/-- Reading the ABI word at calldata offset four preserves each source byte
    already present in that 32-byte argument window. This is the native
    `calldataload(4)` byte-level counterpart of
    `readBytes_zero_get?_of_lt_source`. -/
theorem readBytes_offset4_get?_of_lt_source
    (source : ByteArray)
    (i : Nat)
    (hi : 4 + i < source.size)
    (hi32 : i < 32) :
    (ByteArray.readBytes source 4 32).get? i = source.get? (4 + i) := by
  unfold ByteArray.readBytes
  have hsmall : (decide (4 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  have hiData : 4 + i < source.data.size := by
    simpa using hi
  have hCopySize : i < (source.copySlice 4 ByteArray.empty 0 32).size := by
    simp [ByteArray.size, ByteArray.data_copySlice]
    omega
  calc
    (source.copySlice 4 ByteArray.empty 0 32 ++
          ffi.ByteArray.zeroes
            { toBitVec := ↑32 -
              ↑(source.copySlice 4 ByteArray.empty 0 32).size }).get? i
        = (source.copySlice 4 ByteArray.empty 0 32).get? i :=
          byteArray_get?_append_left hCopySize
    _ = source.get? (4 + i) := by
      unfold ByteArray.get?
      split
      · simp [ByteArray.get]
      · contradiction

@[simp] theorem initialState_calldataReadWord_selectorByte0
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
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

/-- Native initial calldata exposes the first ABI argument word at offset four,
    byte-for-byte, before EVMYulLean recomposes it into a `UInt256`. -/
theorem initialState_calldataReadWord_arg0Byte
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (i : Nat)
    (hi : i < 32) :
    (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        4 32).get? i =
      some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
  rw [readBytes_offset4_get?_of_lt_source]
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    rw [hArgs]
    exact calldataToByteArray_arg0Byte tx.functionSelector arg rest i hi
  · rw [show
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata =
          calldataToByteArray tx.functionSelector tx.args by
          simp [initialState, EvmYul.Yul.State.toState, YulState.initial,
            toSharedState, mkBlockHeader]]
    rw [hArgs]
    simp [calldataToByteArray_size]
    omega
  · exact hi

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
    (storage : IRStorageSlot → IRStorageWord)
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

private theorem div_pow_succ_byte (arg i : Nat) :
    arg / 2 ^ (8 * (i + 1)) = arg / 256 / 2 ^ (8 * i) := by
  rw [Nat.mul_add, Nat.pow_add]
  norm_num
  rw [Nat.div_div_eq_div_mul]
  ring_nf

private theorem mod_byte_decomp (arg m : Nat) (hm : 0 < m) :
    arg % (256 * m) = arg % 256 + 256 * ((arg / 256) % m) := by
  have hdecomp : arg = 256 * (arg / 256) + arg % 256 := by
    exact (Nat.div_add_mod arg 256).symm
  have hr : arg % 256 < 256 := Nat.mod_lt arg (by norm_num)
  have hsmall : arg % 256 < 256 * m := by nlinarith
  have hqm : (arg / 256) % m < m := Nat.mod_lt _ hm
  have hlt : 256 * ((arg / 256) % m) + arg % 256 < 256 * m := by nlinarith
  conv_lhs => rw [hdecomp]
  rw [Nat.add_mod]
  rw [Nat.mul_mod_mul_left]
  rw [Nat.mod_eq_of_lt hsmall]
  rw [Nat.mod_eq_of_lt hlt]
  ring

private theorem fromBytes'_of_le_bytes (n arg : Nat) :
    EvmYul.fromBytes'
      (List.ofFn fun i : Fin n => UInt8.ofNat (arg / 2 ^ (8 * i.1) % 256)) =
      arg % 2 ^ (8 * n) := by
  induction n generalizing arg with
  | zero =>
      simp [EvmYul.fromBytes']
      omega
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [EvmYul.fromBytes']
      have htail :
          (List.ofFn fun i : Fin n =>
              UInt8.ofNat (arg / 2 ^ (8 * (i.succ.1)) % 256)) =
          (List.ofFn fun i : Fin n =>
              UInt8.ofNat (arg / 256 / 2 ^ (8 * i.1) % 256)) := by
        apply List.ext_getElem <;> simp [div_pow_succ_byte]
      rw [htail]
      rw [ih (arg / 256)]
      simp [UInt8.ofNat, UInt8.size]
      have hpow : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
        rw [Nat.mul_add, Nat.pow_add]
        norm_num
        ring
      rw [hpow]
      have hbyte : OfNat.ofNat (arg % 256) % 256 = arg % 256 := by
        change (arg % 256) % 256 = arg % 256
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))
      rw [mod_byte_decomp arg (2 ^ (8 * n)) (by positivity)]
      rw [hbyte]

private theorem fromBytes'_argWordBytes (arg : Nat) :
    EvmYul.fromBytes'
      ((List.ofFn fun i : Fin 32 =>
        UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)).reverse) =
      arg % EvmYul.UInt256.size := by
  simpa [List.ofFn_succ, EvmYul.UInt256.size] using fromBytes'_of_le_bytes 32 arg

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

theorem readBytes_offset4_32_size (source : ByteArray) :
    (ByteArray.readBytes source 4 32).size = 32 := by
  unfold ByteArray.readBytes
  have hsmall : (decide (4 < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    norm_num
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

theorem readWithPadding_32_size (source : ByteArray) (addr : Nat) :
    (source.readWithPadding addr 32).size = 32 := by
  unfold ByteArray.readWithPadding
  have hsmall : ¬ 32 ≥ 2 ^ 64 := by norm_num
  simp only [hsmall, ↓reduceIte]
  rw [ByteArray.size_append]
  have hReadLe :
      (source.readWithoutPadding addr 32).size ≤ 32 := by
    unfold ByteArray.readWithoutPadding
    split
    · simp
    · simp [ByteArray.size_extract]
      omega
  have hReadLeData :
      (source.readWithoutPadding addr 32).data.size ≤ 32 := by
    simpa [ByteArray.size] using hReadLe
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · exact hReadLeData

private theorem byteArray_append_zeroes0 (source : ByteArray) :
    source ++ ffi.ByteArray.zeroes (OfNat.ofNat 0) = source := by
  apply ByteArray.ext
  simp [ByteArray.data_append, ffi.ByteArray.zeroes]

private theorem byteArray_extract_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.extract 0 32 = source := by
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.size] at hSize ⊢
  rw [hSize]
  simp

private theorem byteArray_readWithPadding_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.readWithPadding 0 32 = source := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  have hsmall : ¬ 32 ≥ 2 ^ 64 := by norm_num
  simp only [hsmall, ↓reduceIte]
  have haddr : ¬ 0 ≥ source.size := by omega
  simp only [haddr, ↓reduceIte]
  have hmin : min 32 source.size = 32 := by omega
  simp only [hmin]
  rw [byteArray_extract_zero_32_eq_of_size source hSize]
  apply ByteArray.ext
  have hDataSize : source.data.size = 32 := by
    simpa [ByteArray.size] using hSize
  simp [ByteArray.data_append, ByteArray.size, ffi.ByteArray.zeroes]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · omega

private theorem byteArray_write_empty_zero_32_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    source.write 0 ByteArray.empty 0 32 = source := by
  unfold ByteArray.write
  simp only [Nat.reduceEqDiff, ↓reduceIte]
  have hSourceAddr : ¬ 0 ≥ source.size := by omega
  simp only [hSourceAddr, ↓reduceIte]
  have hPractical : min 32 (source.size - 0) = 32 := by omega
  have hEnd : min ByteArray.empty.size (0 + 32) = 0 := by simp
  have hDestPadding : 0 - ByteArray.empty.size = 0 := by simp
  simp only [hPractical, hEnd, hDestPadding]
  apply ByteArray.ext
  simp [ByteArray.data_copySlice, ByteArray.size, ffi.ByteArray.zeroes] at hSize ⊢
  exact Or.inr (by omega)

/-- A full-word memory write to empty memory at offset zero is returned
    byte-for-byte by `readWithPadding 0 32`. This is the byte-array core of the
    native `mstore(0, x); return(0, 32)` exact-return proof. -/
theorem byteArray_write_empty_zero_32_readWithPadding_eq_of_size
    (source : ByteArray)
    (hSize : source.size = 32) :
    (source.write 0 ByteArray.empty 0 32).readWithPadding 0 32 = source := by
  rw [byteArray_write_empty_zero_32_eq_of_size source hSize]
  exact byteArray_readWithPadding_zero_32_eq_of_size source hSize

elab "apply_evmyul_toBytes_uint256_length_le" : tactic => do
  let theoremName :=
    Name.str
      (Name.str
        (Name.num
          (Name.str (Name.str (Name.str .anonymous "_private") "EvmYul") "UInt256")
          0)
        "EvmYul")
      "toBytes'_UInt256_le"
  let goals ← (← getMainGoal).apply (mkConst theoremName)
  replaceMainGoal goals

private theorem toBytesBigEndian_uint256_length_le
    {n : Nat} (h : n < EvmYul.UInt256.size) :
    (EvmYul.toBytesBigEndian n).length ≤ 32 := by
  unfold EvmYul.toBytesBigEndian
  simp
  apply_evmyul_toBytes_uint256_length_le
  exact h

private theorem list_toByteArray_loop_size (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).size = acc.size + bytes.length := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, Nat.add_assoc]
      omega

private theorem list_toByteArray_loop_data_toList (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).data.toList = acc.data.toList ++ bytes := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, List.append_assoc]

private theorem list_toByteArray_size (bytes : List UInt8) :
    bytes.toByteArray.size = bytes.length := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_size]
  simp

private theorem list_toByteArray_data_toList (bytes : List UInt8) :
    bytes.toByteArray.data.toList = bytes := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_data_toList]
  simp

theorem uint256_toByteArray_size (value : EvmYul.UInt256) :
    value.toByteArray.size = 32 := by
  have hBytesSize :
      (EvmYul.toBytesBigEndian value.toNat).toByteArray.data.size =
        (EvmYul.toBytesBigEndian value.toNat).length := by
    simpa [ByteArray.size] using
      list_toByteArray_size (EvmYul.toBytesBigEndian value.toNat)
  have hLen : (EvmYul.toBytesBigEndian value.toNat).length ≤ 32 :=
    toBytesBigEndian_uint256_length_le (n := value.toNat) value.val.isLt
  unfold EvmYul.UInt256.toByteArray BE
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [hBytesSize]
  rw [usize_sub_toNat_of_le_32]
  · omega
  · exact hLen

theorem initialState_calldataReadWord_arg0Bytes
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let bytes := ByteArray.readBytes
      (initialState contract tx storage observableSlots).toState.executionEnv.calldata 4 32
    bytes.data.toList =
      List.ofFn (fun i : Fin 32 =>
        UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)) := by
  intro bytes
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 32
  · have hleft : bytes.data.toList[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      exact byteArray_data_toList_get?_of_get? bytes i _
        (by
          dsimp [bytes]
          exact initialState_calldataReadWord_arg0Byte contract tx storage
            observableSlots arg rest hArgs i hi)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? =
        some (UInt8.ofNat (arg / 2 ^ ((31 - i) * 8) % 256)) := by
      rw [List.getElem?_ofFn]
      simp only [hi, ↓reduceDIte]
    rw [hleft, hright]
  · have hleft : bytes.data.toList[i]? = none := by
      have hlen : bytes.data.toList.length = 32 := by
        have hsize := readBytes_offset4_32_size
          (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        simpa [bytes, ByteArray.size] using hsize
      exact List.getElem?_eq_none (by omega)
    have hright :
        (List.ofFn (fun i : Fin 32 =>
          UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)))[i]? = none := by
      exact List.getElem?_eq_none (by simp; omega)
    rw [hleft, hright]

/-- Native `calldataload(4)` decodes the first aligned ABI argument word from
    the bridged calldata exactly as a `UInt256`, i.e. modulo the EVM word size. -/
theorem initialState_calldataload4_arg0_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.UInt256.toNat
      (EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat 4)) =
      arg % EvmYul.UInt256.size := by
  let bytes := ByteArray.readBytes
    (initialState contract tx storage observableSlots).toState.executionEnv.calldata 4 32
  have hbytes :=
    initialState_calldataReadWord_arg0Bytes contract tx storage observableSlots
      arg rest hArgs
  unfold EvmYul.State.calldataload EvmYul.uInt256OfByteArray
  rw [show (EvmYul.UInt256.ofNat 4).toNat = 4 by
    change (Fin.ofNat EvmYul.UInt256.size 4).val = 4
    simp [Fin.ofNat]
    norm_num [EvmYul.UInt256.size]]
  rw [show
      (ByteArray.readBytes
        (initialState contract tx storage observableSlots).toState.executionEnv.calldata
        4 32).data.toList =
        bytes.data.toList by rfl]
  rw [hbytes]
  change EvmYul.UInt256.toNat
      (EvmYul.UInt256.ofNat
        (EvmYul.fromBytes'
          ((List.ofFn fun i : Fin 32 =>
            UInt8.ofNat (arg / 2 ^ ((31 - i.1) * 8) % 256)).reverse))) =
    arg % EvmYul.UInt256.size
  rw [fromBytes'_argWordBytes arg]
  exact uint256_ofNat_toNat_of_lt (arg % EvmYul.UInt256.size)
    (Nat.mod_lt _ (by norm_num [EvmYul.UInt256.size]))

/-- Native `calldataload(4)` decodes the first aligned ABI argument as the
    exact EVM word used by the state bridge. -/
theorem initialState_calldataload4_arg0_word
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.State.calldataload
        (initialState contract tx storage observableSlots).toState
        (EvmYul.UInt256.ofNat 4) =
      natToUInt256 arg := by
  apply uint256_eq_of_toNat_eq
  rw [initialState_calldataload4_arg0_value contract tx storage
    observableSlots arg rest hArgs]
  change arg % EvmYul.UInt256.size =
    (Fin.ofNat EvmYul.UInt256.size arg).val
  simp [Fin.ofNat]

/-- Native selector decoding agrees with the interpreter selector by reducing
    EVMYulLean `calldataload(0) >>> 224` to the four ABI selector bytes in
    the initial bridged calldata. -/
theorem initialState_selectorExpr_native_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
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

theorem initialState_selectorExpr_native_uint256
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
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

@[simp] theorem step_add_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ADD none state [left, right] =
      .ok (state, some (EvmYul.UInt256.add left right)) := by
  rfl

@[simp] theorem step_sub_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SUB none state [left, right] =
      .ok (state, some (EvmYul.UInt256.sub left right)) := by
  rfl

@[simp] theorem step_mul_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MUL none state [left, right] =
      .ok (state, some (EvmYul.UInt256.mul left right)) := by
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

@[simp] theorem step_lt_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LT none state [left, right] =
      .ok (state, some (EvmYul.UInt256.lt left right)) := by
  rfl

@[simp] theorem step_calldatasize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATASIZE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.calldata.size)) := by
  rfl

@[simp] theorem step_callvalue_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLVALUE none state [] =
      .ok (state, some state.executionEnv.weiValue) := by
  rfl

@[simp] theorem step_address_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ADDRESS none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val)) := by
  rfl

@[simp] theorem step_balance_ok
    (state : EvmYul.Yul.State)
    (account : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.BALANCE none state [account] =
      let (state', value) := state.toState.balance account
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_origin_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.ORIGIN none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.sender.val)) := by
  rfl

@[simp] theorem step_caller_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLER none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.source.val)) := by
  rfl

@[simp] theorem step_timestamp_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TIMESTAMP none state [] =
      .ok (state, some state.toState.timeStamp) := by
  rfl

@[simp] theorem step_number_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.NUMBER none state [] =
      .ok (state, some state.toState.number) := by
  rfl

@[simp] theorem step_chainid_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CHAINID none state [] =
      .ok (state, some state.toState.chainId) := by
  rfl

@[simp] theorem step_blobbasefee_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.BLOBBASEFEE none state [] =
      .ok (state, some state.executionEnv.getBlobGasprice) := by
  rfl

@[simp] theorem step_gasprice_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GASPRICE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.executionEnv.gasPrice)) := by
  rfl

@[simp] theorem step_coinbase_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.COINBASE none state [] =
      .ok (state, some (EvmYul.UInt256.ofNat state.toState.coinBase.val)) := by
  rfl

@[simp] theorem step_gaslimit_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GASLIMIT none state [] =
      .ok (state, some state.toState.gasLimit) := by
  rfl

@[simp] theorem step_selfbalance_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SELFBALANCE none state [] =
      .ok (state, some state.toState.selfbalance) := by
  rfl

@[simp] theorem step_and_ok
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.AND none state [left, right] =
      .ok (state, some (EvmYul.UInt256.land left right)) := by
  rfl

@[simp] theorem step_mstore_ok
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE none state [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore offset value),
        none) := by
  rfl

@[simp] theorem step_mstore8_ok
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSTORE8 none state [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore8 offset value),
        none) := by
  rfl

@[simp] theorem step_sload_ok
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SLOAD none state [slot] =
      let (state', value) := state.toState.sload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_mload_ok
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MLOAD none state [offset] =
      let (value, machineState') := state.toSharedState.toMachineState.mload offset
      .ok (state.setMachineState machineState', some value) := by
  rfl

@[simp] theorem step_keccak256_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.KECCAK256 none state [offset, size] =
      let (value, machineState') := state.toMachineState.keccak256 offset size
      .ok (state.setMachineState machineState', some value) := by
  rfl

@[simp] theorem step_log0_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG0 none state [offset, size] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[] state.toSharedState), none) := by
  rfl

@[simp] theorem step_log1_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG1 none state
        [offset, size, topic0] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0] state.toSharedState), none) := by
  rfl

@[simp] theorem step_log2_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG2 none state
        [offset, size, topic0, topic1] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_log3_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG3 none state
        [offset, size, topic0, topic1, topic2] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_log4_ok
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 topic3 : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.LOG4 none state
        [offset, size, topic0, topic1, topic2, topic3] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2, topic3]
          state.toSharedState), none) := by
  rfl

@[simp] theorem step_sstore_ok
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.SSTORE none state [slot, value] =
      .ok (state.setState (state.toState.sstore slot value), none) := by
  rfl

@[simp] theorem step_tload_ok
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TLOAD none state [slot] =
      let (state', value) := state.toState.tload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        some value) := by
  rfl

@[simp] theorem step_tstore_ok
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.TSTORE none state [slot, value] =
      .ok (state.setState (state.toState.tstore slot value), none) := by
  rfl

@[simp] theorem step_msize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.MSIZE none state [] =
      .ok (state, some (state.toMachineState.msize)) := by
  rfl

@[simp] theorem step_gas_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.GAS none state [] =
      .ok (state, some (state.toMachineState.gas)) := by
  rfl

@[simp] theorem step_returndatasize_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATASIZE none state [] =
      .ok (state, some (state.toMachineState.returndatasize)) := by
  rfl

@[simp] theorem step_calldatacopy_ok
    (state : EvmYul.Yul.State)
    (mstart datastart size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.CALLDATACOPY none state
        [mstart, datastart, size] =
      .ok (state.setSharedState
        (state.toSharedState.calldatacopy mstart datastart size), none) := by
  rfl

@[simp] theorem step_returndatacopy_ok
    (state : EvmYul.Yul.State)
    (mstart rstart size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURNDATACOPY none state
        [mstart, rstart, size] =
      .ok (state.setMachineState
        (state.toSharedState.toMachineState.returndatacopy mstart rstart size),
        none) := by
  rfl

@[simp] theorem step_pop_ok
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.POP none state [value] =
      .ok (state, none) := by
  rfl

@[simp] theorem step_stop_ok
    (state : EvmYul.Yul.State) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.STOP none state [] =
      .error (EvmYul.Yul.Exception.YulHalt state ⟨0⟩) := by
  rfl

@[simp] theorem step_return_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.RETURN none state [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
          state [offset, size] with
      | .error e => .error e
      | .ok (s, value) =>
          .error (EvmYul.Yul.Exception.YulHalt s (value.getD ⟨1⟩)) := by
  rfl

@[simp] theorem step_revert_ok
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.step (τ := .Yul) EvmYul.Operation.REVERT none state [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
          state [offset, size] with
      | .error e => .error e
      | .ok (_, _) => .error EvmYul.Yul.Exception.Revert := by
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

/-- Native primitive execution of `calldataload(4)` on initial bridged calldata
    returns the first aligned ABI argument word. This packages the byte-level
    calldata decode through EVMYulLean's actual `CALLDATALOAD` primitive
    relation, in the shape needed by the generated `store(uint256)` body. -/
theorem primCall_calldataload4_initialState_arg0_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (initialState contract tx storage observableSlots,
        [natToUInt256 arg]) := by
  have hWord :=
    initialState_calldataload4_arg0_word contract tx storage
      observableSlots arg rest hArgs
  unfold initialState at hWord ⊢
  rw [primCall_calldataload_ok]
  simpa [hWord]

/-- Native primitive execution of `calldataload(4)` is independent of the
    current Yul local-variable store. This is the selected-body shape needed
    after the lowered dispatcher has inserted its switch temporaries. -/
theorem primCall_calldataload4_initialState_arg0_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState store,
        [natToUInt256 arg]) := by
  have hWord :=
    initialState_calldataload4_arg0_word contract tx storage
      observableSlots arg rest hArgs
  rw [primCall_calldataload_ok]
  simpa [EvmYul.Yul.State.toState] using hWord

/-- Native primitive execution of `calldataload(4)` for an IR transaction
    already converted to the native Yul transaction surface. This is the
    dispatcher-selected setter shape: the lowered switch has installed local
    temporaries, but calldata still decodes the first aligned ABI argument
    exactly through EVMYulLean's `CALLDATALOAD` primitive. -/
theorem primCall_calldataload4_initialState_ofIR_arg0_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots).sharedState store)
        EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4] =
      .ok (.Ok (initialState contract (YulTransaction.ofIR tx) storage
            observableSlots).sharedState store,
        [natToUInt256 arg]) := by
  exact
    primCall_calldataload4_initialState_arg0_ok_withStore
      fuel contract (YulTransaction.ofIR tx) storage observableSlots store arg
      rest (by simpa using hArgs)

@[simp] theorem primCall_shr_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SHR [shift, value] =
      .ok (state, [EvmYul.UInt256.shiftRight value shift]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_add_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADD [left, right] =
      .ok (state, [EvmYul.UInt256.add left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_sub_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SUB [left, right] =
      .ok (state, [EvmYul.UInt256.sub left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_mul_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MUL [left, right] =
      .ok (state, [EvmYul.UInt256.mul left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_div_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.DIV [left, right] =
      .ok (state, [EvmYul.UInt256.div left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_mod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MOD [left, right] =
      .ok (state, [EvmYul.UInt256.mod left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_sdiv_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SDIV [left, right] =
      .ok (state, [EvmYul.UInt256.sdiv left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_smod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SMOD [left, right] =
      .ok (state, [EvmYul.UInt256.smod left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_addmod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right modulus : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADDMOD [left, right, modulus] =
      .ok (state, [EvmYul.UInt256.addMod left right modulus]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_mulmod_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right modulus : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MULMOD [left, right, modulus] =
      .ok (state, [EvmYul.UInt256.mulMod left right modulus]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_exp_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.EXP [left, right] =
      .ok (state, [EvmYul.UInt256.exp left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_signextend_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (byteIdx value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SIGNEXTEND [byteIdx, value] =
      .ok (state, [EvmYul.UInt256.signextend byteIdx value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

/-- Native primitive execution of the generated dispatcher selector core:
    `calldataload(0)` reads the ABI selector word and `shr(224, ...)` decodes
    the normalized 32-bit selector used by the lowered native switch. -/
theorem primCall_calldataload0_then_shr224_initialState_selector_ok
    (loadFuel shrFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (loadFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 0]
      match values with
      | [selectorWord] =>
          EvmYul.Yul.primCall (shrFuel + 1) state' EvmYul.Operation.SHR
            [EvmYul.UInt256.ofNat Compiler.Constants.selectorShift,
              selectorWord]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .ok (initialState contract tx storage observableSlots,
        [EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus)]) := by
  have hInit :
      initialState contract tx storage observableSlots =
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State) := by
    simp [initialState, EvmYul.Yul.State.sharedState]
  rw [hInit]
  rw [primCall_calldataload_ok]
  change EvmYul.Yul.primCall (shrFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState ∅)
      EvmYul.Operation.SHR
        [EvmYul.UInt256.ofNat Compiler.Constants.selectorShift,
        EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (initialState contract tx storage observableSlots).sharedState ∅).toState
          (EvmYul.UInt256.ofNat 0)] =
    .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
      [EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus)])
  rw [primCall_shr_ok]
  rw [show
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.Yul.State.Ok
            (initialState contract tx storage observableSlots).sharedState ∅).toState
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) by
    simpa [initialState, EvmYul.Yul.State.toState] using
      initialState_selectorExpr_native_uint256 contract tx storage observableSlots]

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

@[simp] theorem primCall_lt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LT [left, right] =
      .ok (state, [EvmYul.UInt256.lt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GT [left, right] =
      .ok (state, [EvmYul.UInt256.gt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_slt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SLT [left, right] =
      .ok (state, [EvmYul.UInt256.slt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_sgt_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SGT [left, right] =
      .ok (state, [EvmYul.UInt256.sgt left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_calldatasize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLDATASIZE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.calldata.size]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_callvalue_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLVALUE [] =
      .ok (state, [state.executionEnv.weiValue]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_address_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ADDRESS [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.codeOwner.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_balance_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (account : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BALANCE [account] =
      let (state', value) := state.toState.balance account
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_origin_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.ORIGIN [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.sender.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_caller_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLER [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.source.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_timestamp_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TIMESTAMP [] =
      .ok (state, [state.toState.timeStamp]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_number_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.NUMBER [] =
      .ok (state, [state.toState.number]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_chainid_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CHAINID [] =
      .ok (state, [state.toState.chainId]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_blobbasefee_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BLOBBASEFEE [] =
      .ok (state, [state.executionEnv.getBlobGasprice]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gasprice_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GASPRICE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.executionEnv.gasPrice]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_coinbase_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.COINBASE [] =
      .ok (state, [EvmYul.UInt256.ofNat state.toState.coinBase.val]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gaslimit_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.GASLIMIT [] =
      .ok (state, [state.toState.gasLimit]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_selfbalance_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SELFBALANCE [] =
      .ok (state, [state.toState.selfbalance]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_and_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.AND [left, right] =
      .ok (state, [EvmYul.UInt256.land left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_or_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.OR [left, right] =
      .ok (state, [EvmYul.UInt256.lor left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_xor_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (left right : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.XOR [left, right] =
      .ok (state, [EvmYul.UInt256.xor left right]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_not_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.NOT [value] =
      .ok (state, [EvmYul.UInt256.lnot value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_shl_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SHL [shift, value] =
      .ok (state, [EvmYul.UInt256.shiftLeft value shift]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_byte_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (index value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.BYTE [index, value] =
      .ok (state, [EvmYul.UInt256.byteAt index value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_sar_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (shift value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SAR [shift, value] =
      .ok (state, [EvmYul.UInt256.sar shift value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall] <;> rfl

@[simp] theorem primCall_mstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore offset value),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_mstore8_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MSTORE8 [offset, value] =
      .ok (state.setMachineState (state.toMachineState.mstore8 offset value),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_sload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SLOAD [slot] =
      let (state', value) := state.toState.sload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_mload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.MLOAD [offset] =
      let (value, machineState') := state.toSharedState.toMachineState.mload offset
      .ok (state.setMachineState machineState', [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_keccak256_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.KECCAK256 [offset, size] =
      let (value, machineState') := state.toMachineState.keccak256 offset size
      .ok (state.setMachineState machineState', [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_log0_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG0 [offset, size] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[] state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log1_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG1 [offset, size, topic0] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0] state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log2_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG2 [offset, size, topic0, topic1] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log3_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG3 [offset, size, topic0, topic1, topic2] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_log4_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size topic0 topic1 topic2 topic3 : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.LOG4 [offset, size, topic0, topic1, topic2, topic3] =
      .ok (state.setSharedState
        (EvmYul.SharedState.logOp offset size #[topic0, topic1, topic2, topic3]
          state.toSharedState), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_sstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.SSTORE [slot, value] =
      .ok (state.setState (state.toState.sstore slot value), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_tload_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TLOAD [slot] =
      let (state', value) := state.toState.tload slot
      .ok (state.setSharedState { state.toSharedState with toState := state' },
        [value]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_tstore_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (slot value : EvmYul.UInt256)
    (hPerm : state.executionEnv.perm = true) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.TSTORE [slot, value] =
      .ok (state.setState (state.toState.tstore slot value), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall, hPerm]

@[simp] theorem primCall_msize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.MSIZE [] =
      .ok (state, [state.toMachineState.msize]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_gas_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.GAS [] =
      .ok (state, [state.toMachineState.gas]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_returndatasize_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.RETURNDATASIZE [] =
      .ok (state, [state.toMachineState.returndatasize]) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_calldatacopy_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (mstart datastart size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.CALLDATACOPY [mstart, datastart, size] =
      .ok (state.setSharedState
        (state.toSharedState.calldatacopy mstart datastart size), []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_returndatacopy_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (mstart rstart size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.RETURNDATACOPY [mstart, rstart, size] =
      .ok (state.setMachineState
        (state.toSharedState.toMachineState.returndatacopy mstart rstart size),
        []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_pop_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.POP [value] =
      .ok (state, []) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_stop_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.primCall (fuel + 1) state EvmYul.Operation.STOP [] =
      .error (EvmYul.Yul.Exception.YulHalt state ⟨0⟩) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]

@[simp] theorem primCall_return_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.RETURN [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
          state [offset, size] with
      | .error e => .error e
      | .ok (s, value) =>
          .error (EvmYul.Yul.Exception.YulHalt s (value.getD ⟨1⟩)) := by
  cases fuel <;> simp [EvmYul.Yul.primCall]
  all_goals
    cases EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
      state [offset, size] <;> rfl

@[simp] theorem primCall_revert_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (offset size : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1) state
        EvmYul.Operation.REVERT [offset, size] =
      match EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
          state [offset, size] with
      | .error e => .error e
      | .ok (_, _) => .error EvmYul.Yul.Exception.Revert := by
  cases fuel <;> simp [EvmYul.Yul.primCall]
  all_goals
    cases EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
      state [offset, size] <;> rfl

def nativeRevertZeroZeroStmt : EvmYul.Yul.Ast.Stmt :=
  .ExprStmtCall
    (.Call (Sum.inl (EvmYul.Operation.REVERT : EvmYul.Operation .Yul))
      [.Lit (EvmYul.UInt256.ofNat 0), .Lit (EvmYul.UInt256.ofNat 0)])

/-- The compiler's proof-side `revert(0, 0)` default lowers to the concrete
    native statement used by the selector-miss execution lemma. -/
theorem lowerStmtsNative_revert_zero_zero :
    Backends.lowerStmtsNative
      [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])] =
      .ok [nativeRevertZeroZeroStmt] := by
  simp [Backends.lowerStmtsNative, Backends.lowerStmtsNativeWithSwitchIds,
    nativeRevertZeroZeroStmt, Backends.lowerExprNative,
    Backends.lookupRuntimePrimOp]
  rfl

/-- Native execution of the generated selector-miss body `revert(0, 0)`.
    This is the concrete primitive halt used by the dispatcher default path. -/
theorem exec_revert_zero_zero_error
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.exec (fuel + 6)
      nativeRevertZeroZeroStmt codeOverride state =
      .error EvmYul.Yul.Exception.Revert := by
  cases fuel <;>
    simp [nativeRevertZeroZeroStmt, EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
      EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall, EvmYul.Yul.reverse',
      EvmYul.Yul.cons', EvmYul.Yul.multifill',
      EvmYul.Yul.binaryMachineStateOp]

theorem exec_expr_prim_ok
    (fuel : Nat)
    (state next : EvmYul.Yul.State)
    (op : EvmYul.Operation .Yul)
    (args : List EvmYul.Yul.Ast.Expr)
    (values : List EvmYul.Yul.Ast.Literal)
    (hEval :
      EvmYul.Yul.evalArgs fuel args.reverse none state =
        .ok (state, values.reverse))
    (hPrim :
      EvmYul.Yul.primCall fuel state op values = .ok (next, [])) :
    EvmYul.Yul.exec (fuel + 1)
        (.ExprStmtCall (.Call (Sum.inl op) args)) none state =
      .ok next := by
  simp [EvmYul.Yul.exec]
  rw [hEval]
  simp [EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall, hPrim,
    EvmYul.Yul.multifill']
  cases next <;> rfl

theorem exec_let_prim_one_ok
    (fuel : Nat)
    (state next : EvmYul.Yul.State)
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (args : List EvmYul.Yul.Ast.Expr)
    (values : List EvmYul.Yul.Ast.Literal)
    (value : EvmYul.Yul.Ast.Literal)
    (hEval :
      EvmYul.Yul.evalArgs fuel args.reverse none state =
        .ok (state, values.reverse))
    (hPrim :
      EvmYul.Yul.primCall fuel state op values = .ok (next, [value])) :
    EvmYul.Yul.exec (fuel + 1)
        (.Let [name] (some (.Call (Sum.inl op) args))) none state =
      .ok (next.insert name value) := by
  simp [EvmYul.Yul.exec]
  rw [hEval]
  simp [EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall, hPrim,
    EvmYul.Yul.multifill']
  cases next <;> rfl

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
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus)) := by
  rw [eval_lowerExprNative_selectorExpr_ok]
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  rw [hv]

/-- Native evaluation of the lowered `iszero(lt(calldatasize(), 4))` Yul
    expression — the `__has_selector` initializer that `buildSwitch` emits —
    reduces to the concrete `UInt256` predicate `isZero(lt(ofNat cd_size, 4))`,
    where `cd_size` is the calldata byte size in the current execution
    environment. This is the eval-side primitive needed to chain
    `let __has_selector := …` through `exec_let_prim_one_ok` in the
    selector-miss/hit dispatcher proof. -/
theorem eval_lowerExprNative_iszero_lt_calldatasize_4_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero"
            [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]]))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- For any natural `n` representable as a `UInt256` and at least `4`, the
    EVMYulLean primitive `LT(ofNat n, 4)` evaluates to the canonical zero word.
    This is the closed-form predicate fact needed to specialise
    `eval_lowerExprNative_iszero_lt_calldatasize_4_ok` to the dispatcher's
    initial state, where calldata size is `4 + tx.args.length * 32`. -/
private theorem uint256_lt_ofNat_4_eq_zero_of_ge
    (n : Nat) (hLe : 4 ≤ n) (hSize : n < EvmYul.UInt256.size) :
    EvmYul.UInt256.lt (EvmYul.UInt256.ofNat n) (EvmYul.UInt256.ofNat 4) =
      EvmYul.UInt256.ofNat 0 := by
  have hN : (EvmYul.UInt256.ofNat n).val.val = n := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hSize]
  have h4 : (EvmYul.UInt256.ofNat 4).val.val = 4 := by
    unfold EvmYul.UInt256.ofNat
    decide
  have hNotLt : ¬ ((EvmYul.UInt256.ofNat n : EvmYul.UInt256) <
      (EvmYul.UInt256.ofNat 4 : EvmYul.UInt256)) := by
    intro hLt
    have hh : (EvmYul.UInt256.ofNat n).val.val <
        (EvmYul.UInt256.ofNat 4).val.val := hLt
    rw [hN, h4] at hh
    omega
  simp [EvmYul.UInt256.lt, hNotLt]

/-- The canonical zero `UInt256` is its own `isZero`-predecessor in the sense
    that `ISZERO 0 = 1`. -/
private theorem uint256_isZero_ofNat_zero :
    EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0) = EvmYul.UInt256.ofNat 1 := by
  decide

/-- Specialisation of
    `eval_lowerExprNative_iszero_lt_calldatasize_4_ok` to the dispatcher's
    initial bridged state. Because `calldata.size = 4 + tx.args.length * 32`
    and the no-wrap hypothesis keeps that within the `UInt256` range, the
    `__has_selector` initializer reduces to the concrete value `1`. This is
    the eval-side primitive that lets the selector-hit path of the dispatcher
    fire (and the selector-miss path is then ruled out by `iszero(1) = 0`). -/
theorem eval_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero"
            [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]]))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        EvmYul.UInt256.ofNat 1) := by
  rw [eval_lowerExprNative_iszero_lt_calldatasize_4_ok,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- Native evaluation of the lowered `callvalue()` Yul expression.
    The EVMYulLean primitive `CALLVALUE` is a zero-argument execution-env op
    that returns the current execution environment's `weiValue`. Closes the
    eval-side seam for callvalue-guard reasoning on dispatcher inner blocks. -/
theorem eval_lowerExprNative_callvalue_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 5
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store, shared.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- Specialisation of `eval_lowerExprNative_callvalue_ok` to the dispatcher's
    initial bridged state: the result is the literal `natToUInt256 tx.msgValue`
    via `initialState_weiValue`. -/
theorem eval_lowerExprNative_callvalue_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.eval 5
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        natToUInt256 tx.msgValue) := by
  rw [eval_lowerExprNative_callvalue_ok, initialState_weiValue]

/-- Fuel-parametric form of `eval_lowerExprNative_callvalue_ok`. -/
theorem eval_lowerExprNative_callvalue_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval (fuel + 5)
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store, shared.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- Native evaluation of the lowered `lt(calldatasize(), k)` Yul expression
    (the inner argument-length revert guard `if lt(calldatasize(), K) {…}` that
    `dispatchBody` emits before each function-arg-length-checked body). At any
    fuel `≥ fuel + 7`, the eval reduces to the concrete `UInt256` predicate
    `LT(ofNat cd_size, ofNat k)`, where `cd_size` is the calldata byte size in
    the current execution environment. Closes the eval-side seam for
    lt-calldatasize-guard reasoning on dispatcher hit-case body inner blocks. -/
theorem eval_lowerExprNative_lt_calldatasize_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (k : Nat) :
    EvmYul.Yul.eval (fuel + 8)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit k]))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.lt
          (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
          (EvmYul.UInt256.ofNat k)) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- Native evaluation of the lowered `sload(lit slot)` Yul expression. At any
    fuel `≥ fuel + 6`, the eval reduces to the closed-form pair returned by
    EVMYulLean's `SLOAD` primitive: the new `SharedState` carries the
    storage-access-tracked `toState`, and the value is the raw
    `State.sload` result word. Closes the eval-side seam for sload reasoning
    on dispatcher hit-case body inner blocks (specifically the
    `mstore(0, sload(0))` outer expression in the `retrieve()` getter
    body). -/
theorem eval_lowerExprNative_sload_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (slot : Nat) :
    EvmYul.Yul.eval (fuel + 6)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]))
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat slot)
      .ok (.Ok { shared with toState := state' } store, value) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

/-- State-generic native `exec` of the `mstore(memOffset, sload(slot))`
    expression statement that the generated `retrieve()` body uses to
    materialise the slot-zero word into memory before `return(0,32)`.
    The exec threads the closed-form sload→mstore state effect: storage
    is read with access-tracking via `SharedState.sload`, and memory is
    updated with `MachineState.mstore` of the resulting value at the
    given offset. The Yul `VarStore` is unchanged. -/
theorem exec_lowerExprNative_mstore_lit_sload_lit_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset slot : Nat) :
    EvmYul.Yul.exec (fuel + 8)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit memOffset,
             Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]])))
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat slot)
      let shared' : EvmYul.SharedState .Yul := { shared with toState := state' }
      .ok (.Ok { shared' with
                 toMachineState :=
                   shared'.toMachineState.mstore
                     (EvmYul.UInt256.ofNat memOffset) value }
            store) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState]

/-- State-generic native `exec` of the `return(memOffset, memSize)` expression
    statement that the generated `retrieve()` body uses to surface the
    materialised slot-zero word as the call's return data. EVMYulLean models
    `RETURN` as a Yul halt carrying the post-`evmReturn` machine state; the
    halt literal is the canonical nonzero marker `⟨1⟩` produced by
    `binaryMachineStateOp`, while the actual returned bytes live in the
    state's `H_return` buffer. The Yul `VarStore` is unchanged. -/
theorem exec_lowerExprNative_return_lit_lit_error_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset memSize : Nat) :
    EvmYul.Yul.exec (fuel + 6)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit memOffset, Yul.YulExpr.lit memSize])))
        codeOverride (.Ok shared store) =
      .error (EvmYul.Yul.Exception.YulHalt
        (.Ok { shared with
               toMachineState :=
                 shared.toMachineState.evmReturn
                   (EvmYul.UInt256.ofNat memOffset)
                   (EvmYul.UInt256.ofNat memSize) }
          store)
        ⟨1⟩) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.binaryMachineStateOp, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.toMachineState, EvmYul.Yul.multifill']

/-- Singleton-block form of `exec_lowerExprNative_return_lit_lit_error_fuel`.
    A block whose only statement is `return(memOffset, memSize)` exec-errors
    with the same closed-form `YulHalt` as the bare statement, plus one
    extra unit of fuel for the `Block` cons step. This lets compositional
    proofs that need to peel an outer block via `exec_block_cons_tail_error`
    discharge the singleton-tail obligation directly. -/
theorem exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset memSize : Nat) :
    EvmYul.Yul.exec (fuel + 7)
        (.Block [.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit memOffset, Yul.YulExpr.lit memSize]))])
        codeOverride (.Ok shared store) =
      .error (EvmYul.Yul.Exception.YulHalt
        (.Ok { shared with
               toMachineState :=
                 shared.toMachineState.evmReturn
                   (EvmYul.UInt256.ofNat memOffset)
                   (EvmYul.UInt256.ofNat memSize) }
          store)
        ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 6)) _ codeOverride _ = _
  have hHead := exec_lowerExprNative_return_lit_lit_error_fuel
    fuel shared store codeOverride memOffset memSize
  simp [EvmYul.Yul.exec, hHead]

/-- State-generic native `exec` of the `let __has_selector := iszero(lt(
    calldatasize(), 4))` statement that `buildSwitch` emits at the head of a
    dispatcher inner-block: at any fuel `≥ 11`, the let assigns
    `name ↦ isZero(lt(ofNat cd_size, 4))` to the variable store, where
    `cd_size = shared.executionEnv.calldata.size`. The closed-form numeric
    evaluation of `isZero(lt(_, _))` is then performed by the initial-state
    specialization below. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier) :
    EvmYul.Yul.exec 11
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        codeOverride (.Ok shared store) =
      .ok ((.Ok shared store : EvmYul.Yul.State).insert name
        (EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4)))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.executionEnv]

/-- Specialisation of `exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok`
    to the dispatcher's initial bridged state. With the no-wrap hypothesis on
    `4 + tx.args.length * 32`, the `__has_selector` variable receives the
    closed-form word `UInt256.ofNat 1`. This is the exec-side primitive the
    dispatcher proof needs immediately after the dispatcher inner-block is
    pinned to its `let / if / if` shape: it lets the selector-miss `If` guard
    fail and the selector-hit `If` guard fire. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (name : EvmYul.Identifier)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec 11
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
            EvmYul.Yul.State).insert name (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- Fuel-parametric form of
    `exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok`. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        codeOverride (.Ok shared store) =
      .ok ((.Ok shared store : EvmYul.Yul.State).insert name
        (EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4)))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.executionEnv]

/-- Fuel-parametric form of
    `exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok`. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (name : EvmYul.Identifier)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
            EvmYul.Yul.State).insert name (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok_fuel,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- State-generic native `eval` of the lowered selector-miss guard
    `iszero(__has_selector)`: when the named variable is bound to
    `UInt256.ofNat 1` in the variable store, the guard evaluates to
    the canonical zero `UInt256` literal. This is the eval primitive that
    feeds `exec_if_eval_zero` to skip the selector-miss `revert(0,0)` body. -/
theorem eval_lowerExprNative_iszero_ident_one_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 8
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident name]))
        codeOverride state =
      .ok (state, EvmYul.UInt256.ofNat 0) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', hVal]
  decide

/-- Fuel-parametric form of `eval_lowerExprNative_iszero_ident_one_ok`. -/
theorem eval_lowerExprNative_iszero_ident_one_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 8)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident name]))
        codeOverride state =
      .ok (state, EvmYul.UInt256.ofNat 0) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', hVal]
  decide

theorem exec_let_lowerExprNative_selectorExpr_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec 11
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

theorem exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

/-- Store-parametric form of `exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel`.
    The lowered selector eval reads only calldata from the shared state, so
    the `let __discr := selectorExpr` step is invariant under any preceding
    native-side varstore. Lets us chain the dispatcher prefix's discriminator
    binding on a state that already carries `__has_selector := 1` (left by
    the buildSwitch wrapper). -/
theorem exec_let_lowerExprNative_selectorExpr_initialState_store_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

@[simp] theorem exec_let_lit_ok
    (fuel' : Nat)
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel')
        (.Let [name] (some (.Lit value))) codeOverride state =
      .ok (state.insert name value) := by
  simp [EvmYul.Yul.exec]

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

/-- Tail-generic peel of a native block whose head statement finishes
    normally: the whole block exec at `succ fuel'` equals the residual block
    exec on the post-head state at the same fuel `fuel'`, regardless of how
    that residual exec finally evaluates. Useful when the rest of the proof
    stays open (e.g. when the next peel is a chained equation rather than a
    closed `.ok final`). -/
theorem exec_block_cons_ok_eq
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next := by
  simp [EvmYul.Yul.exec, hHead]

/-- If the head statement of a native block halts or errors, the whole block
    halts or errors immediately. -/
theorem exec_block_cons_error
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hHead]

/-- If the head statement of a native block finishes normally but the tail
    halts or errors, the whole block halts or errors after the head update. -/
theorem exec_block_cons_tail_error
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next)
    (hTail : EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hHead, hTail]

/-- Execute an appended native block when the left block consumes exactly its
    statement-count fuel prefix and the right block runs at the remaining fuel.

This matches EVMYulLean's block interpreter: every cons step decrements the fuel
available to both the head statement and the tail block. -/
theorem exec_block_append_ok
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state middle final : EvmYul.Yul.State)
    (hLeft : EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state = .ok middle)
    (hRight : EvmYul.Yul.exec (fuel + k) (.Block right) codeOverride middle = .ok final) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right)) codeOverride state = .ok final := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft hRight ⊢
      cases remaining with
      | zero =>
          have hLeft0 : EvmYul.Yul.exec 0 (.Block []) codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeft0
      | succ remaining' =>
          have hLeftS : EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
              codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
          cases hLeftS
          simpa [hFuel] using hRight
  | cons stmt rest ih =>
      have hFuel : fuel + (stmt :: rest).length + k =
          fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' : EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
          (.Block (stmt :: rest)) codeOverride state = .ok middle := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead : EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state =
        head at hLeft'
      cases head with
      | error err => simp at hLeft'
      | ok next =>
          simp at hLeft'
          have hTail : EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
              codeOverride next = .ok middle := hLeft'
          have hRest : EvmYul.Yul.exec (fuel + rest.length + k)
              (.Block (rest ++ right)) codeOverride next = .ok final :=
            ih fuel next hTail hRight
          have hBlock := exec_block_cons_ok (fuel + rest.length + k)
            stmt (rest ++ right) codeOverride state next final hHead hRest
          have hGoalFuel : fuel + rest.length + k + 1 =
              fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hBlock

/-- Execute an appended native block when the left block finishes normally and
    the right block halts or errors at the remaining fuel. -/
theorem exec_block_append_error
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state middle : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hLeft :
      EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state =
        .ok middle)
    (hRight :
      EvmYul.Yul.exec (fuel + k) (.Block right) codeOverride middle =
        .error err) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right))
      codeOverride state = .error err := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft hRight ⊢
      cases remaining with
      | zero =>
          have hLeft0 :
              EvmYul.Yul.exec 0 (.Block []) codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeft0
      | succ remaining' =>
          have hLeftS :
              EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
                codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
          cases hLeftS
          simpa [hFuel] using hRight
  | cons stmt rest ih =>
      have hFuel :
          fuel + (stmt :: rest).length + k = fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' :
          EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
            (.Block (stmt :: rest)) codeOverride state = .ok middle := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead :
        EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state = head
        at hLeft'
      cases head with
      | error err' =>
          simp at hLeft'
      | ok next =>
          simp at hLeft'
          have hTail :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
                codeOverride next = .ok middle := hLeft'
          have hRest :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block (rest ++ right))
                codeOverride next = .error err :=
            ih fuel next hTail hRight
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_tail_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state next err hHead hRest)

/-- If an appended block's left prefix halts or errors, the full appended block
    halts or errors before reaching the right suffix. -/
theorem exec_block_append_prefix_error
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hLeft :
      EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right))
      codeOverride state = .error err := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft ⊢
      cases remaining with
      | zero =>
          simpa [hFuel, EvmYul.Yul.exec] using hLeft
      | succ remaining' =>
          have hLeftS :
              EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
                codeOverride state = .error err := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
  | cons stmt rest ih =>
      have hFuel :
          fuel + (stmt :: rest).length + k = fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' :
          EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
            (.Block (stmt :: rest)) codeOverride state = .error err := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead :
        EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state = head
        at hLeft'
      cases head with
      | error err' =>
          simp at hLeft'
          subst err'
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state err hHead)
      | ok next =>
          simp at hLeft'
          have hTail :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
                codeOverride next = .error err := hLeft'
          have hRest :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block (rest ++ right))
                codeOverride next = .error err :=
            ih fuel next hTail
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_tail_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state next err hHead hRest)

theorem exec_block_nil_ok
    (fuel' : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block []) codeOverride state =
      .ok state := by
  simp [EvmYul.Yul.exec]

def nativeSwitchPrefixStmts
    (discrName matchedName : EvmYul.Identifier) :
    List EvmYul.Yul.Ast.Stmt :=
  [.Let [discrName]
    (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)),
   .Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]

def nativeSwitchInitialOkState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.State :=
  .Ok (initialState contract tx storage observableSlots).sharedState ∅

def nativeSwitchPrefixFinalState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.State :=
  ((nativeSwitchInitialOkState contract tx storage observableSlots).insert discrName
    (EvmYul.UInt256.ofNat
      (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
    matchedName (EvmYul.UInt256.ofNat 0)

/-- The generated dispatcher switch prefix initializes the discriminator temp
    from native calldata selector evaluation, then clears the lazy matched flag.

This packages the first two statements emitted by `lowerNativeSwitchBlock` for
the generated dispatcher case and leaves the remaining case-chain proof with a
state whose native switch temporaries are aligned to the interpreter oracle. -/
theorem exec_nativeSwitchPrefix_selector_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec 12
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName) := by
  let initState : EvmYul.Yul.State :=
    nativeSwitchInitialOkState contract tx storage observableSlots
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec 12
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  rw [nativeSwitchPrefixStmts]
  apply exec_block_cons_ok 11
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_ok
      contract tx storage observableSlots discrName
  · apply exec_block_cons_ok 10
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp
      simp [matchedState]
    · simp [EvmYul.Yul.exec]

theorem exec_nativeSwitchPrefix_selector_initialState_ok_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName) := by
  let initState : EvmYul.Yul.State :=
    nativeSwitchInitialOkState contract tx storage observableSlots
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  have hFuel : fuel + 12 = Nat.succ (fuel + 11) := by omega
  rw [hFuel]
  rw [nativeSwitchPrefixStmts]
  apply exec_block_cons_ok (fuel + 11)
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel
      fuel contract tx storage observableSlots discrName
  · have hFuelTail : fuel + 11 = Nat.succ (fuel + 10) := by omega
    rw [hFuelTail]
    apply exec_block_cons_ok (fuel + 10)
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp [matchedState]
    · simp [EvmYul.Yul.exec]

/-- Store-parametric form of `exec_nativeSwitchPrefix_selector_initialState_ok_fuel`.
    The two prefix Lets only depend on calldata (read-only via the shared
    state), so they are invariant under any preceding native varstore. Lifts
    the dispatcher prefix execution to a state already carrying additional
    bindings (e.g. the buildSwitch wrapper's `__has_selector := 1`). -/
theorem exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .ok (((.Ok (initialState contract tx storage observableSlots).sharedState store
            : EvmYul.Yul.State).insert discrName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          matchedName (EvmYul.UInt256.ofNat 0)) := by
  let initState : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  have hFuel : fuel + 12 = Nat.succ (fuel + 11) := by omega
  rw [hFuel, nativeSwitchPrefixStmts]
  apply exec_block_cons_ok (fuel + 11)
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_store_ok_fuel
      fuel contract tx storage observableSlots store discrName
  · have hFuelTail : fuel + 11 = Nat.succ (fuel + 10) := by omega
    rw [hFuelTail]
    apply exec_block_cons_ok (fuel + 10)
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp [matchedState]
    · simp [EvmYul.Yul.exec]

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

/-- Native `if` reduction for a nonzero guard when the body halts or errors. -/
theorem exec_if_eval_nonzero_error
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (value : EvmYul.Literal)
    (err : EvmYul.Yul.Exception)
    (hEval : EvmYul.Yul.eval fuel' cond codeOverride state = .ok (next, value))
    (hNe : value ≠ (⟨0⟩ : EvmYul.Literal))
    (hBody : EvmYul.Yul.exec fuel' (.Block body) codeOverride next = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hEval, hNe, hBody]

/-- Native `if` execution skips the lowered selector-miss revert guard
    `if iszero(<name>) { … }` whenever the named variable is bound to
    `UInt256.ofNat 1` — i.e., when the dispatcher's `let __has_selector :=
    iszero(lt(calldatasize(), 4))` step has bound the variable to one
    (which `exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok`
    establishes for any tx satisfying the calldata-size no-wrap bound).
    This is the per-statement no-op for the dispatcher's `If1` step that
    lets the selector-hit `If2` body fire on the same incoming state. -/
theorem exec_if_lowerExprNative_iszero_ident_one_skip
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 9
        (.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident name]))
          body)
        codeOverride state =
      .ok state :=
  exec_if_eval_zero 8 _ body codeOverride state state
    (eval_lowerExprNative_iszero_ident_one_ok state codeOverride name hVal)

/-- Native `if` execution skips the lowered `callvalue()` revert guard
    `if callvalue() { … }` whenever the current `executionEnv.weiValue` is
    the canonical zero literal — i.e., when the transaction's `msgValue` is
    `0`. This is the per-statement no-op for the dispatcher's hit-case
    body callvalue guard, mirroring `exec_if_lowerExprNative_iszero_ident_one_skip`
    for the selector-miss case. -/
theorem exec_if_lowerExprNative_callvalue_skip_zero_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal)) :
    EvmYul.Yul.exec (fuel + 6)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" [])) body)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store) := by
  refine exec_if_eval_zero (fuel + 5) _ body codeOverride
    (.Ok shared store) (.Ok shared store) ?_
  rw [eval_lowerExprNative_callvalue_ok_fuel, hWei]

/-- General-`k` form of `uint256_lt_ofNat_4_eq_zero_of_ge`: when `k ≤ n` and
    both fit in `UInt256`, the EVMYulLean primitive `LT(ofNat n, ofNat k)`
    evaluates to the canonical zero word. Used to discharge the
    lt-calldatasize-guard on the body's inner argument-length revert. -/
private theorem uint256_lt_ofNat_eq_zero_of_ge
    (n k : Nat) (hLe : k ≤ n)
    (hSize : n < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size) :
    EvmYul.UInt256.lt (EvmYul.UInt256.ofNat n) (EvmYul.UInt256.ofNat k) =
      EvmYul.UInt256.ofNat 0 := by
  have hN : (EvmYul.UInt256.ofNat n).val.val = n := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hSize]
  have hK : (EvmYul.UInt256.ofNat k).val.val = k := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hKSize]
  have hNotLt : ¬ ((EvmYul.UInt256.ofNat n : EvmYul.UInt256) <
      (EvmYul.UInt256.ofNat k : EvmYul.UInt256)) := by
    intro hLt
    have hh : (EvmYul.UInt256.ofNat n).val.val <
        (EvmYul.UInt256.ofNat k).val.val := hLt
    rw [hN, hK] at hh
    omega
  simp [EvmYul.UInt256.lt, hNotLt]

/-- Native `if` execution skips the lowered `if lt(calldatasize(), k) { … }`
    revert guard whenever the current calldata is at least `k` bytes — i.e.,
    when the caller has supplied enough calldata for the function's selector
    plus its declared arguments. This is the per-statement no-op for the
    dispatcher's hit-case body inner argument-length guard, mirroring
    `exec_if_lowerExprNative_callvalue_skip_zero_fuel` for the callvalue
    guard. -/
theorem exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
                (Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [],
                   Yul.YulExpr.lit k]))
          body)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store) := by
  refine exec_if_eval_zero (fuel + 8) _ body codeOverride
    (.Ok shared store) (.Ok shared store) ?_
  rw [eval_lowerExprNative_lt_calldatasize_ok_fuel,
      uint256_lt_ofNat_eq_zero_of_ge _ _ hGe hSize hKSize]
  rfl

/-- Fuel-parametric form of `exec_if_lowerExprNative_iszero_ident_one_skip`. -/
theorem exec_if_lowerExprNative_iszero_ident_one_skip_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
        (.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident name]))
          body)
        codeOverride state =
      .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_lowerExprNative_iszero_ident_one_ok_fuel fuel state codeOverride name hVal))

/-- Lookup of a freshly inserted name in the empty-store `nativeSwitchInitialOkState`
    is the inserted value; mediates between the post-`Let` post state produced
    by the selector-binding lemma and the `hVal` premise consumed by the
    `If1`-skip lemma. -/
private theorem nativeSwitchInitialOkState_insert_lookup_self
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
        name value)[name]! = value := by
  simp [nativeSwitchInitialOkState, EvmYul.Yul.State.insert,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem,
    EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

/-- Fuel-parametric native `If` reduction for the lowered selector-hit guard
    `if __has_selector { … }`: when the named variable is bound to
    `UInt256.ofNat 1`, the lowered `Var name` condition evaluates non-zero so
    the if-statement reduces to executing its body block at strictly smaller
    fuel on the same incoming state. This is the dispatcher's `If2`-take
    counterpart of the `If1`-skip lemma. -/
theorem exec_if_lowerExprNative_ident_one_take_fuel
    (fuel : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 2)
        (.If (Backends.lowerExprNative (Yul.YulExpr.ident name)) body)
        codeOverride state =
      EvmYul.Yul.exec (fuel + 1) (.Block body) codeOverride state := by
  have hNe : (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ ⟨0⟩ := by decide
  simp [EvmYul.Yul.exec, Backends.lowerExprNative, EvmYul.Yul.eval, hVal, hNe]

/-- Native singleton-block exec equals the inner statement exec at decremented
    fuel: the trailing `Block []` peel always succeeds at positive fuel and
    returns the head-statement result unchanged, so for any positive outer
    fuel the singleton-block is the inner statement. -/
theorem exec_block_singleton_eq
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + 2) (.Block [stmt]) codeOverride state =
      EvmYul.Yul.exec (fuel + 1) stmt codeOverride state := by
  cases h : EvmYul.Yul.exec (fuel + 1) stmt codeOverride state with
  | error e => simp [EvmYul.Yul.exec, h]
  | ok s' => simp [EvmYul.Yul.exec, h]

/-- Native dispatcher inner-block chain peel of `Let` + `If1`-skip on
    `nativeSwitchInitialOkState`: under the calldata no-wrap bound, the
    selector-binding `Let` runs to `__has_selector ↦ 1` and the selector-miss
    `If1` body is statically skipped, so the outer block exec equals the
    residual `Block tail` exec at strictly smaller fuel on the post-`Let`
    state. Composes the existing `Let` and `If1`-skip fuel lemmas through
    `nativeSwitchInitialOkState_insert_lookup_self`. -/
theorem exec_block_letSelector_if1Skip_initialState_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (selectorName : EvmYul.Identifier) (if1Body tail : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          tail))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          selectorName (EvmYul.UInt256.ofNat 1)) := by
  simp only [nativeSwitchInitialOkState]
  have hLet := exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok_fuel
    fuel contract tx storage observableSlots selectorName hNoWrap
  have hLookup := nativeSwitchInitialOkState_insert_lookup_self
    contract tx storage observableSlots selectorName (EvmYul.UInt256.ofNat 1)
  simp only [nativeSwitchInitialOkState] at hLookup
  have hIfRaw := exec_if_lowerExprNative_iszero_ident_one_skip_fuel
    (fuel + 1) if1Body (some contract) _ selectorName hLookup
  have hFuelEq : (fuel + 1) + 9 = fuel + 10 := by omega
  rw [hFuelEq] at hIfRaw
  rw [show fuel + 12 = (fuel + 11).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hLet,
      show fuel + 11 = (fuel + 10).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hIfRaw]

/-- Native dispatcher full inner-block 3-statement peel on
    `nativeSwitchInitialOkState`: under the calldata no-wrap bound, the
    selector-binding `Let` runs, the selector-miss `If1` is statically
    skipped, and the selector-hit `If2` is taken, leaving the residual
    `Block if2Body` exec at strictly smaller fuel on the post-`Let` state.
    Composes `exec_block_letSelector_if1Skip_initialState_fuel` with the
    `exec_block_singleton_eq` and `exec_if_lowerExprNative_ident_one_take_fuel`
    lemmas through `nativeSwitchInitialOkState_insert_lookup_self`. -/
theorem exec_block_letSelector_if1Skip_if2Take_initialState_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (selectorName : EvmYul.Identifier)
    (if1Body if2Body : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          [.If (Backends.lowerExprNative
              (Yul.YulExpr.ident selectorName)) if2Body]))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + 8) (.Block if2Body) (some contract)
        ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          selectorName (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_block_letSelector_if1Skip_initialState_fuel fuel contract tx storage
        observableSlots selectorName if1Body
        [.If (Backends.lowerExprNative (Yul.YulExpr.ident selectorName)) if2Body]
        hNoWrap]
  have hLookup := nativeSwitchInitialOkState_insert_lookup_self
    contract tx storage observableSlots selectorName (EvmYul.UInt256.ofNat 1)
  rw [show fuel + 10 = (fuel + 8) + 2 from rfl,
      exec_block_singleton_eq (fuel + 8) _ (some contract) _,
      show fuel + 8 + 1 = (fuel + 7) + 2 from rfl,
      exec_if_lowerExprNative_ident_one_take_fuel (fuel + 7) if2Body
        (some contract) _ selectorName hLookup,
      show fuel + 7 + 1 = fuel + 8 from rfl]

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

/-- Fuel-parametric form of `eval_nativeSwitchGuardedMatch_ok`, for use under
    recursively executed generated switch blocks. -/
theorem eval_nativeSwitchGuardedMatch_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.eval (fuel + 8)
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
  cases fuel <;>
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

/-- An unmatched lowered switch case has a zero guard while no previous case has
    matched and the discriminator differs from the case tag. -/
theorem eval_nativeSwitchGuardedMatch_miss_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero, hDiscr]
  decide

/-- Fuel-parametric non-selected lowered switch case guard reduction. -/
theorem eval_nativeSwitchGuardedMatch_miss_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero, hDiscr]
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

/-- Fuel-parametric form of `eval_nativeSwitchGuardedMatch_matched_ok`. -/
theorem eval_nativeSwitchGuardedMatch_matched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched]
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

/-- Native `if` execution skips a non-selected lowered switch case while no
    previous case has matched. -/
theorem exec_if_nativeSwitchGuardedMatch_miss
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
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
    (eval_nativeSwitchGuardedMatch_miss_ok state codeOverride discrName matchedName tag
      hMatched hDiscr)

/-- Fuel-parametric native `if` skip for a non-selected lowered switch case. -/
theorem exec_if_nativeSwitchGuardedMatch_miss_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_nativeSwitchGuardedMatch_miss_ok_fuel fuel state codeOverride
        discrName matchedName tag hMatched hDiscr))

@[simp] theorem exec_lowerAssignNative_lit_ok
    (fuel' : Nat)
    (name : EvmYul.Identifier)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel')
      (Backends.lowerAssignNative name (.lit value)) codeOverride state =
      .ok (state.insert name (EvmYul.UInt256.ofNat value)) := by
  simp [Backends.lowerAssignNative, Backends.lowerExprNative]

/-- Native `if` execution for the selected lowered switch case, including the
    leading matched-flag assignment inserted by `lowerNativeSwitchBlock`.

This is the selected-case execution boundary the full lowered-switch proof can
reuse: after the guard hits, the selected body runs in the same state except
for `matchedName := 1`. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec 7 (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .ok final := by
  apply exec_if_nativeSwitchGuardedMatch_hit
      (body := Backends.lowerAssignNative matchedName (.lit 1) :: body)
      (codeOverride := codeOverride) (state := state) (final := final)
      (discrName := discrName) (matchedName := matchedName) (tag := tag)
      hMatched hDiscr
  exact exec_block_cons_ok 7 (Backends.lowerAssignNative matchedName (.lit 1))
    body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
    final (by simp) hBody

/-- Fuel-parametric selected-case guard reduction. -/
theorem eval_nativeSwitchGuardedMatch_hit_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched, hDiscr]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric selected-case execution, including the matched-flag
    assignment inserted at the start of each lowered native switch case. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .ok final := by
  apply exec_if_eval_nonzero (fuel + 8) _ _ codeOverride state state final
      (EvmYul.UInt256.ofNat 1)
  · exact eval_nativeSwitchGuardedMatch_hit_ok_fuel fuel state codeOverride discrName matchedName tag
      hMatched hDiscr
  · decide
  · exact exec_block_cons_ok (fuel + 7) (Backends.lowerAssignNative matchedName (.lit 1))
      body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
      final (by simp) hBody

/-- Fuel-parametric selected-case execution, including the matched-flag
    assignment inserted at the start of each lowered native switch case, when
    the selected body halts or errors. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked_error_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .error err := by
  apply exec_if_eval_nonzero_error (fuel + 8) _ _ codeOverride state state
      (EvmYul.UInt256.ofNat 1) err
  · exact eval_nativeSwitchGuardedMatch_hit_ok_fuel fuel state codeOverride discrName matchedName tag
      hMatched hDiscr
  · decide
  · exact exec_block_cons_tail_error (fuel + 7)
      (Backends.lowerAssignNative matchedName (.lit 1))
      body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
      err (by simp) hBody

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

/-- Fuel-parametric native `if` skip for a later lowered switch case after an
    earlier case has set the matched flag. -/
theorem exec_if_nativeSwitchGuardedMatch_matched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_nativeSwitchGuardedMatch_matched_ok_fuel fuel state codeOverride
        discrName matchedName tag hMatched))

/-- Native evaluation of the lazy lowered switch default guard peels to
    `ISZERO(matched)`. -/
theorem eval_nativeSwitchDefaultGuard_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.isZero state[matchedName]!) := by
  simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
    EvmYul.Yul.cons', EvmYul.Yul.head']

/-- Fuel-parametric form of `eval_nativeSwitchDefaultGuard_ok`, for use under
    recursively executed generated switch blocks. -/
theorem eval_nativeSwitchDefaultGuard_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.isZero state[matchedName]!) := by
  cases fuel <;>
    simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
      EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
      EvmYul.Yul.cons', EvmYul.Yul.head']

/-- If no lowered switch case has matched, the default guard is nonzero. -/
theorem eval_nativeSwitchDefaultGuard_unmatched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchDefaultGuard_ok, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric default guard reduction when no case has matched. -/
theorem eval_nativeSwitchDefaultGuard_unmatched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchDefaultGuard_ok_fuel, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- If a lowered switch case has matched, the default guard is zero. -/
theorem eval_nativeSwitchDefaultGuard_matched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchDefaultGuard_ok, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric default guard reduction after a case has matched. -/
theorem eval_nativeSwitchDefaultGuard_matched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchDefaultGuard_ok_fuel, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Native `if` execution for the lowered switch default when no case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec 6 (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec 7
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok final := by
  exact exec_if_eval_nonzero 6 _ body codeOverride state state final
    (EvmYul.UInt256.ofNat 1)
    (eval_nativeSwitchDefaultGuard_unmatched_ok state codeOverride matchedName hMatched)
    (by decide)
    hBody

/-- Fuel-parametric default execution when no lowered switch case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec (fuel + 6) (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok final := by
  simpa using
    (exec_if_eval_nonzero (fuel + 6) _ body codeOverride state state final
      (EvmYul.UInt256.ofNat 1)
      (eval_nativeSwitchDefaultGuard_unmatched_ok_fuel fuel state codeOverride
        matchedName hMatched)
      (by decide)
      hBody)

/-- Fuel-parametric default execution when no lowered switch case matched and
    the default body halts or errors. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched_error_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec (fuel + 6) (.Block body) codeOverride state =
      .error err) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .error err := by
  simpa using
    (exec_if_eval_nonzero_error (fuel + 6) _ body codeOverride state state
      (EvmYul.UInt256.ofNat 1) err
      (eval_nativeSwitchDefaultGuard_unmatched_ok_fuel fuel state codeOverride
        matchedName hMatched)
      (by decide)
      hBody)

/-- Native `if` execution skips the lowered switch default after a case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_matched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 7
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok state := by
  exact exec_if_eval_zero 6 _ body codeOverride state state
    (eval_nativeSwitchDefaultGuard_matched_ok state codeOverride matchedName hMatched)

/-- Fuel-parametric default skip after a lowered switch case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_matched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 6) _ body codeOverride state state
      (eval_nativeSwitchDefaultGuard_matched_ok_fuel fuel state codeOverride
        matchedName hMatched))

def nativeSwitchGuardedMatchExpr
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.Ast.Expr :=
  Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
    [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
      [.Var matchedName],
     Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
      [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]]

def nativeSwitchDefaultGuardExpr
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.Ast.Expr :=
  Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
    [.Var matchedName]

def nativeSwitchCaseIf
    (discrName matchedName : EvmYul.Identifier)
    (entry : Nat × List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.Stmt :=
  .If (nativeSwitchGuardedMatchExpr discrName matchedName entry.1)
    (Backends.lowerAssignNative matchedName (.lit 1) :: entry.2)

def nativeSwitchCaseIfs
    (discrName matchedName : EvmYul.Identifier)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) :
    List EvmYul.Yul.Ast.Stmt :=
  cases.map (nativeSwitchCaseIf discrName matchedName)

def nativeSwitchDefaultIf
    (matchedName : EvmYul.Identifier)
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    List EvmYul.Yul.Ast.Stmt :=
  if defaultBody.isEmpty then []
  else [.If (nativeSwitchDefaultGuardExpr matchedName) defaultBody]

def nativeSwitchTailStmts
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    List EvmYul.Yul.Ast.Stmt :=
  nativeSwitchCaseIfs (Backends.nativeSwitchDiscrTempName switchId)
    (Backends.nativeSwitchMatchedTempName switchId) cases ++
    nativeSwitchDefaultIf (Backends.nativeSwitchMatchedTempName switchId)
      defaultBody

theorem lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    Backends.lowerNativeSwitchBlock Compiler.Proofs.YulGeneration.selectorExpr
      switchId cases defaultBody =
    .Block
      (nativeSwitchPrefixStmts (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId) ++
        nativeSwitchTailStmts switchId cases defaultBody) := by
  simp [Backends.lowerNativeSwitchBlock, nativeSwitchPrefixStmts,
    nativeSwitchCaseIfs, nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr,
    nativeSwitchTailStmts, nativeSwitchDefaultIf, nativeSwitchDefaultGuardExpr]

def NativeBlockPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state[name]! = value →
      EvmYul.Yul.exec fuel (.Block body) codeOverride state = .ok final →
        final[name]! = value

def NativeStmtPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state[name]! = value →
      EvmYul.Yul.exec fuel stmt codeOverride state = .ok final →
        final[name]! = value

def NativeExprPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (expr : EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final result,
    state[name]! = value →
      EvmYul.Yul.eval fuel expr codeOverride state = .ok (final, result) →
        final[name]! = value

def NativeEvalArgsPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final results,
    state[name]! = value →
      EvmYul.Yul.evalArgs fuel args codeOverride state = .ok (final, results) →
        final[name]! = value

theorem state_lookup_insert_of_ne
    (state : EvmYul.Yul.State)
    (name other : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (hne : name ≠ other) :
    EvmYul.Yul.State.lookup! name (state.insert other value) =
      EvmYul.Yul.State.lookup! name state := by
  cases state with
  | Ok shared store =>
      simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!]
      rw [Finmap.lookup_insert_of_ne store hne]
  | OutOfFuel => simp [EvmYul.Yul.State.insert]
  | Checkpoint jump => simp [EvmYul.Yul.State.insert]

theorem state_getElem_insert_of_ne
    (state : EvmYul.Yul.State)
    (name other : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (hne : name ≠ other) :
    (state.insert other value)[name]! = state[name]! := by
  cases state with
  | Ok shared store =>
      simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!,
        EvmYul.Yul.State.store, GetElem?.getElem!, decidableGetElem?,
        GetElem.getElem]
      by_cases hmem : name ∈ store
      · simp [hmem, hne, Finmap.lookup_insert_of_ne store hne]
      · simp [hmem, hne]
  | OutOfFuel =>
      simp [EvmYul.Yul.State.insert]
  | Checkpoint jump =>
      simp [EvmYul.Yul.State.insert]

theorem state_getElem_multifill_of_not_mem
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (vars : List EvmYul.Identifier)
    (vals : List EvmYul.Literal)
    (hnot : name ∉ vars) :
    (EvmYul.Yul.State.multifill vars vals state)[name]! = state[name]! := by
  induction vars generalizing state vals with
  | nil =>
      cases state <;> simp [EvmYul.Yul.State.multifill]
  | cons var rest ih =>
      simp at hnot
      rcases hnot with ⟨hneq, hrest⟩
      cases vals with
      | nil =>
          cases state <;> simp [EvmYul.Yul.State.multifill]
      | cons val restVals =>
          cases state with
          | Ok shared store =>
              have hTail :
                  (EvmYul.Yul.State.multifill rest restVals
                    (EvmYul.Yul.State.Ok shared store))[name]! =
                    (EvmYul.Yul.State.Ok shared store)[name]! :=
                ih (EvmYul.Yul.State.Ok shared store) restVals hrest
              simp [EvmYul.Yul.State.multifill]
              rw [state_getElem_insert_of_ne
                (List.foldr (fun x s => s.insert x.1 x.2)
                  (EvmYul.Yul.State.Ok shared store) (rest.zip restVals))
                name var val hneq]
              simpa [EvmYul.Yul.State.multifill] using hTail
          | OutOfFuel =>
              rfl
          | Checkpoint jump =>
              rfl

theorem state_getElem_foldr_insert_zero_of_not_mem
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (vars : List EvmYul.Identifier)
    (hnot : name ∉ vars) :
    ((List.foldr (fun var s => s.insert var ⟨0⟩) state vars))[name]! =
      state[name]! := by
  induction vars generalizing state with
  | nil =>
      rfl
  | cons var rest ih =>
      simp at hnot
      rcases hnot with ⟨hneq, hrest⟩
      have hTail :
          (List.foldr (fun var s => s.insert var ⟨0⟩) state rest)[name]! =
            state[name]! :=
        ih state hrest
      change
        ((List.foldr (fun var s => s.insert var ⟨0⟩) state rest).insert
          var ⟨0⟩)[name]! = state[name]!
      rw [state_getElem_insert_of_ne
        (List.foldr (fun var s => s.insert var ⟨0⟩) state rest)
        name var ⟨0⟩ hneq, hTail]

theorem state_getElem_setSharedState
    (state : EvmYul.Yul.State)
    (shared : EvmYul.SharedState .Yul)
    (name : EvmYul.Identifier) :
    (state.setSharedState shared)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setMachineState
    (state : EvmYul.Yul.State)
    (mstate : EvmYul.MachineState)
    (name : EvmYul.Identifier) :
    (state.setMachineState mstate)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setState
    (state : EvmYul.Yul.State)
    (estate : EvmYul.State .Yul)
    (name : EvmYul.Identifier) :
    (state.setState estate)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setStore_ok_left
    (shared : EvmYul.SharedState .Yul)
    (shared' : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) :
    (((EvmYul.Yul.State.Ok shared ∅) : EvmYul.Yul.State).setStore
      (EvmYul.Yul.State.Ok shared' store))[name]! =
      (EvmYul.Yul.State.Ok shared' store)[name]! := by
  simp [EvmYul.Yul.State.setStore, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem state_getElem_setStore_ok
    (shared shared' : EvmYul.SharedState .Yul)
    (store store' : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) :
    (((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State).setStore
      (EvmYul.Yul.State.Ok shared' store'))[name]! =
      (EvmYul.Yul.State.Ok shared' store')[name]! := by
  simp [EvmYul.Yul.State.setStore, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem NativePrimCallPreservesWord_calldatasize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATASIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_calldatasize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_callvalue
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLVALUE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_callvalue_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_address
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDRESS [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_address_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_balance
    (name : EvmYul.Identifier)
    (expected account : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BALANCE [account] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_balance_ok] at hExec
      cases hExec
      cases state with
      | Ok shared store =>
          simpa [EvmYul.Yul.State.setSharedState] using hLookup
      | OutOfFuel =>
          simpa [EvmYul.Yul.State.setSharedState] using hLookup
      | Checkpoint jump =>
          cases jump <;>
            simpa [EvmYul.Yul.State.setSharedState] using hLookup

theorem NativePrimCallPreservesWord_origin
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ORIGIN [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_origin_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_caller
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLER [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_caller_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_timestamp
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TIMESTAMP [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_timestamp_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_number
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NUMBER [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_number_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_chainid
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CHAINID [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_chainid_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_blobbasefee
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BLOBBASEFEE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_blobbasefee_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_gasprice
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GASPRICE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gasprice_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_coinbase
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.COINBASE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_coinbase_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_gaslimit
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GASLIMIT [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gaslimit_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_selfbalance
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SELFBALANCE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_selfbalance_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_unary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected value result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [value] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [value] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_binary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected left right result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [left, right] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [left, right] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_ternary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected first second third result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [first, second, third] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [first, second, third] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_iszero
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ISZERO [value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state EvmYul.Operation.ISZERO
    name expected value (EvmYul.UInt256.isZero value)
    (by intro fuel state; exact primCall_iszero_ok fuel state value)

theorem NativePrimCallPreservesWord_shr
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHR [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SHR
    name expected shift value (EvmYul.UInt256.shiftRight value shift)
    (by intro fuel state; exact primCall_shr_ok fuel state shift value)

theorem NativePrimCallPreservesWord_add
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.ADD
    name expected left right (EvmYul.UInt256.add left right)
    (by intro fuel state; exact primCall_add_ok fuel state left right)

theorem NativePrimCallPreservesWord_sub
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SUB [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SUB
    name expected left right (EvmYul.UInt256.sub left right)
    (by intro fuel state; exact primCall_sub_ok fuel state left right)

theorem NativePrimCallPreservesWord_mul
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MUL [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.MUL
    name expected left right (EvmYul.UInt256.mul left right)
    (by intro fuel state; exact primCall_mul_ok fuel state left right)

theorem NativePrimCallPreservesWord_div
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.DIV [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.DIV
    name expected left right (EvmYul.UInt256.div left right)
    (by intro fuel state; exact primCall_div_ok fuel state left right)

theorem NativePrimCallPreservesWord_mod
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MOD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.MOD
    name expected left right (EvmYul.UInt256.mod left right)
    (by intro fuel state; exact primCall_mod_ok fuel state left right)

theorem NativePrimCallPreservesWord_sdiv
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SDIV [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SDIV
    name expected left right (EvmYul.UInt256.sdiv left right)
    (by intro fuel state; exact primCall_sdiv_ok fuel state left right)

theorem NativePrimCallPreservesWord_smod
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SMOD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SMOD
    name expected left right (EvmYul.UInt256.smod left right)
    (by intro fuel state; exact primCall_smod_ok fuel state left right)

theorem NativePrimCallPreservesWord_addmod
    (name : EvmYul.Identifier)
    (expected left right modulus : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDMOD
          [left, right, modulus] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state EvmYul.Operation.ADDMOD
    name expected left right modulus
    (EvmYul.UInt256.addMod left right modulus)
    (by intro fuel state; exact primCall_addmod_ok fuel state left right modulus)

theorem NativePrimCallPreservesWord_mulmod
    (name : EvmYul.Identifier)
    (expected left right modulus : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MULMOD
          [left, right, modulus] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state EvmYul.Operation.MULMOD
    name expected left right modulus
    (EvmYul.UInt256.mulMod left right modulus)
    (by intro fuel state; exact primCall_mulmod_ok fuel state left right modulus)

theorem NativePrimCallPreservesWord_exp
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EXP [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.EXP
    name expected left right (EvmYul.UInt256.exp left right)
    (by intro fuel state; exact primCall_exp_ok fuel state left right)

theorem NativePrimCallPreservesWord_signextend
    (name : EvmYul.Identifier)
    (expected byteIdx value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SIGNEXTEND
          [byteIdx, value] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SIGNEXTEND
    name expected byteIdx value (EvmYul.UInt256.signextend byteIdx value)
    (by intro fuel state; exact primCall_signextend_ok fuel state byteIdx value)

theorem NativePrimCallPreservesWord_eq
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EQ [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.EQ
    name expected left right (EvmYul.UInt256.eq left right)
    (by intro fuel state; exact primCall_eq_ok fuel state left right)

theorem NativePrimCallPreservesWord_lt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.LT
    name expected left right (EvmYul.UInt256.lt left right)
    (by intro fuel state; exact primCall_lt_ok fuel state left right)

theorem NativePrimCallPreservesWord_gt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.GT
    name expected left right (EvmYul.UInt256.gt left right)
    (by intro fuel state; exact primCall_gt_ok fuel state left right)

theorem NativePrimCallPreservesWord_slt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SLT
    name expected left right (EvmYul.UInt256.slt left right)
    (by intro fuel state; exact primCall_slt_ok fuel state left right)

theorem NativePrimCallPreservesWord_sgt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SGT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SGT
    name expected left right (EvmYul.UInt256.sgt left right)
    (by intro fuel state; exact primCall_sgt_ok fuel state left right)

theorem NativePrimCallPreservesWord_and
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.AND [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.AND
    name expected left right (EvmYul.UInt256.land left right)
    (by intro fuel state; exact primCall_and_ok fuel state left right)

theorem NativePrimCallPreservesWord_or
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.OR [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.OR
    name expected left right (EvmYul.UInt256.lor left right)
    (by intro fuel state; exact primCall_or_ok fuel state left right)

theorem NativePrimCallPreservesWord_xor
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.XOR [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.XOR
    name expected left right (EvmYul.UInt256.xor left right)
    (by intro fuel state; exact primCall_xor_ok fuel state left right)

theorem NativePrimCallPreservesWord_not
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NOT [value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state EvmYul.Operation.NOT
    name expected value (EvmYul.UInt256.lnot value)
    (by intro fuel state; exact primCall_not_ok fuel state value)

theorem NativePrimCallPreservesWord_shl
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHL [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SHL
    name expected shift value (EvmYul.UInt256.shiftLeft value shift)
    (by intro fuel state; exact primCall_shl_ok fuel state shift value)

theorem NativePrimCallPreservesWord_byte
    (name : EvmYul.Identifier)
    (expected index value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BYTE [index, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.BYTE
    name expected index value (EvmYul.UInt256.byteAt index value)
    (by intro fuel state; exact primCall_byte_ok fuel state index value)

theorem NativePrimCallPreservesWord_sar
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SAR [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SAR
    name expected shift value (EvmYul.UInt256.sar shift value)
    (by intro fuel state; exact primCall_sar_ok fuel state shift value)

theorem NativePrimCallPreservesWord_sload
    (name : EvmYul.Identifier)
    (expected slot : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLOAD [slot] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_sload_ok] at hExec
      cases hSload : state.toState.sload slot with
      | mk state' value =>
          simp [hSload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setSharedState]
          exact hLookup

theorem NativePrimCallPreservesWord_calldataload
    (name : EvmYul.Identifier)
    (expected offset : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATALOAD [offset] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      cases state with
      | Ok shared store =>
          rw [primCall_calldataload_ok] at hExec
          cases hExec
          exact hLookup
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall] at hExec
          cases hExec
          exact hLookup
      | Checkpoint jump =>
          cases jump <;> simp [EvmYul.Yul.primCall] at hExec <;>
            cases hExec <;> exact hLookup

theorem NativePrimCallPreservesWord_mload
    (name : EvmYul.Identifier)
    (expected offset : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MLOAD [offset] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mload_ok] at hExec
      cases hMload : state.toSharedState.toMachineState.mload offset with
      | mk value machineState' =>
          simp [hMload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setMachineState]
          exact hLookup

theorem NativePrimCallPreservesWord_mstore
    (name : EvmYul.Identifier)
    (expected offset value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE [offset, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mstore_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_mstore8
    (name : EvmYul.Identifier)
    (expected offset value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE8 [offset, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mstore8_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_tload
    (name : EvmYul.Identifier)
    (expected slot : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TLOAD [slot] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_tload_ok] at hExec
      cases hTload : state.toState.tload slot with
      | mk state' value =>
          simp [hTload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setSharedState]
          exact hLookup

theorem NativePrimCallPreservesWord_tstore
    (name : EvmYul.Identifier)
    (expected slot value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TSTORE [slot, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_tstore_ok fuel' state slot value hPerm] at hExec
        cases hExec
        rw [state_getElem_setState]
        exact hLookup
      · simp [EvmYul.Yul.primCall, hPerm] at hExec
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
              Except EvmYul.Yul.Exception
                (EvmYul.Yul.State × List EvmYul.Literal)) =
            Except.ok (final, rets) at hExec
        cases hExec

theorem NativePrimCallPreservesWord_sstore
    (name : EvmYul.Identifier)
    (expected slot value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SSTORE [slot, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_sstore_ok fuel' state slot value hPerm] at hExec
        cases hExec
        rw [state_getElem_setState]
        exact hLookup
      · simp [EvmYul.Yul.primCall, hPerm] at hExec
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
              Except EvmYul.Yul.Exception
                (EvmYul.Yul.State × List EvmYul.Literal)) =
            Except.ok (final, rets) at hExec
        cases hExec

theorem NativePrimCallPreservesWord_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.STOP [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_stop_ok] at hExec
      cases hExec

theorem NativePrimCallPreservesWord_return
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURN [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_return_ok fuel' state offset size] at hExec
      cases hReturn :
          EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
            state [offset, size] with
      | error err =>
          simp [hReturn] at hExec
      | ok ret =>
          rcases ret with ⟨returnState, value⟩
          simp [hReturn] at hExec

theorem NativePrimCallPreservesWord_revert
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.REVERT [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_revert_ok fuel' state offset size] at hExec
      cases hRevert :
          EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
            state [offset, size] with
      | error err =>
          simp [hRevert] at hExec
      | ok ret =>
          rcases ret with ⟨revertState, value⟩
          simp [hRevert] at hExec

theorem NativePrimCallPreservesWord_msize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_msize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_gas
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GAS [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gas_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_returndatasize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURNDATASIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_returndatasize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_calldatacopy
    (name : EvmYul.Identifier)
    (expected mstart datastart size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATACOPY
          [mstart, datastart, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_calldatacopy_ok] at hExec
      cases hExec
      rw [state_getElem_setSharedState]
      exact hLookup

theorem NativePrimCallPreservesWord_returndatacopy
    (name : EvmYul.Identifier)
    (expected mstart rstart size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURNDATACOPY
          [mstart, rstart, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_returndatacopy_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_pop
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.POP [value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_pop_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_keccak256
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.KECCAK256
          [offset, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_keccak256_ok] at hExec
      cases hKeccak : state.toMachineState.keccak256 offset size with
      | mk value machineState' =>
          simp [hKeccak] at hExec
          cases hExec
          subst final
          rw [state_getElem_setMachineState]
          exact hLookup

theorem NativePrimCallPreservesWord_log0
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG0 [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log0_ok fuel' state offset size hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log1
    (name : EvmYul.Identifier)
    (expected offset size topic0 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG1
          [offset, size, topic0] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log1_ok fuel' state offset size topic0 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log2
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG2
          [offset, size, topic0, topic1] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log2_ok fuel' state offset size topic0 topic1 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log3
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 topic2 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG3
          [offset, size, topic0, topic1, topic2] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log3_ok fuel' state offset size topic0 topic1 topic2 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log4
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 topic2 topic3 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG4
          [offset, size, topic0, topic1, topic2, topic3] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log4_ok fuel' state offset size topic0 topic1 topic2 topic3 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativeExprPreservesWord_var
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected (.Var identifier) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeExprPreservesWord_lit
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected (.Lit value) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeEvalArgsPreservesWord_nil
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeEvalArgsPreservesWord name expected [] codeOverride := by
  intro fuel state final results hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.evalArgs] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.evalArgs] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeEvalArgsPreservesWord_cons
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (arg : EvmYul.Yul.Ast.Expr)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArg : NativeExprPreservesWord name expected arg codeOverride)
    (hArgs : NativeEvalArgsPreservesWord name expected args codeOverride) :
    NativeEvalArgsPreservesWord name expected (arg :: args) codeOverride := by
  intro fuel state final results hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.evalArgs] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.evalArgs] at hEval
      cases hEvalArg : EvmYul.Yul.eval fuel' arg codeOverride state with
      | error err =>
          rw [hEvalArg] at hEval
          cases fuel' <;> simp [EvmYul.Yul.evalTail] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, argValue⟩
          have hArgLookup : argState[name]! = expected :=
            hArg fuel' state argState argValue hLookup hEvalArg
          simp [hEvalArg] at hEval
          cases fuel' with
          | zero =>
              change
                EvmYul.Yul.evalTail 0 args codeOverride
                  (.ok (argState, argValue)) = .ok (final, results) at hEval
              simp [EvmYul.Yul.evalTail] at hEval
          | succ tailFuel =>
              change
                EvmYul.Yul.evalTail (Nat.succ tailFuel) args codeOverride
                  (.ok (argState, argValue)) = .ok (final, results) at hEval
              simp [EvmYul.Yul.evalTail] at hEval
              cases hEvalArgs :
                  EvmYul.Yul.evalArgs tailFuel args codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.cons'] at hEval
              | ok argsResult =>
                  rcases argsResult with ⟨argsState, values⟩
                  simp [hEvalArgs, EvmYul.Yul.cons'] at hEval
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hArgs tailFuel argState argsState values
                    hArgLookup hEvalArgs

theorem NativeEvalArgsPreservesWord_map_lowerExprNative
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ arg, arg ∈ args →
        NativeExprPreservesWord name expected
          (Backends.lowerExprNative arg) codeOverride) :
    NativeEvalArgsPreservesWord name expected
      (args.map Backends.lowerExprNative) codeOverride := by
  induction args with
  | nil =>
      exact NativeEvalArgsPreservesWord_nil name expected codeOverride
  | cons arg rest ih =>
      exact NativeEvalArgsPreservesWord_cons name expected
        (Backends.lowerExprNative arg) (rest.map Backends.lowerExprNative)
        codeOverride
        (hArgs arg (by simp))
        (ih (by
          intro restArg hRest
          exact hArgs restArg (by simp [hRest])))

theorem NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ arg, arg ∈ args →
        NativeExprPreservesWord name expected
          (Backends.lowerExprNative arg) codeOverride) :
    NativeEvalArgsPreservesWord name expected
      ((args.map Backends.lowerExprNative).reverse) codeOverride := by
  simpa [List.map_reverse] using
    NativeEvalArgsPreservesWord_map_lowerExprNative name expected
      args.reverse codeOverride
      (by
        intro arg hArg
        exact hArgs arg (by simpa using hArg))

theorem NativeExprPreservesWord_lowerExprNative_lit
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.lit value)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_lit name expected (EvmYul.UInt256.ofNat value)
      codeOverride

theorem NativeExprPreservesWord_lowerExprNative_hex
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.hex value)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_lit name expected (EvmYul.UInt256.ofNat value)
      codeOverride

theorem NativeExprPreservesWord_lowerExprNative_str
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.str identifier)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_var name expected identifier codeOverride

theorem NativeExprPreservesWord_lowerExprNative_ident
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.ident identifier)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_var name expected identifier codeOverride

theorem NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (.Call (Sum.inl prim) args) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          rw [hEvalArgs] at hEval
          simp [EvmYul.Yul.reverse', EvmYul.Yul.evalPrimCall] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          rw [hEvalArgs] at hEval
          simp [EvmYul.Yul.reverse', EvmYul.Yul.evalPrimCall] at hEval
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall, EvmYul.Yul.head'] at hEval
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall, EvmYul.Yul.head'] at hEval
              cases rets with
              | nil =>
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hPrim fuel' argState values.reverse primState []
                    hArgLookup hPrimCall
              | cons ret rest =>
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hPrim fuel' argState values.reverse primState (ret :: rest)
                    hArgLookup hPrimCall

theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves
    name expected op (args.map Backends.lowerExprNative) codeOverride hArgs
    hPrim

theorem NativeExprPreservesWord_call_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hCall :
      ∀ fuel state values final rets, state[name]! = expected →
        EvmYul.Yul.call fuel values (some functionName) codeOverride state =
          .ok (final, rets) → final[name]! = expected) :
    NativeExprPreservesWord name expected (.Call (Sum.inr functionName) args)
      codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      cases hEvalArgs : EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          rw [hEvalArgs] at hEval
          cases fuel' <;>
            simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          rw [hEvalArgs] at hEval
          cases fuel' with
          | zero => simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
          | succ callFuel =>
              simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hUserCall, EvmYul.Yul.head'] at hEval
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hUserCall, EvmYul.Yul.head'] at hEval
                  cases rets with
                  | nil =>
                      rcases hEval with ⟨rfl, _⟩
                      exact hCall callFuel argState values.reverse callState []
                        hArgLookup hUserCall
                  | cons ret rest =>
                      rcases hEval with ⟨rfl, _⟩
                      exact hCall callFuel argState values.reverse callState
                        (ret :: rest) hArgLookup hUserCall

theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeExprPreservesWord_call_user_of_evalArgs_call_preserves
    name expected func (args.map Backends.lowerExprNative) codeOverride hArgs
    hCall

theorem state_getElem_overwrite?_left
    (state next : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hOk : ∃ shared store, next = EvmYul.Yul.State.Ok shared store) :
    (state.overwrite? next)[name]! = state[name]! := by
  rcases hOk with ⟨shared, store, rfl⟩
  cases state <;> rfl

theorem state_getElem_restoreCallFrame_of_ok
    (state next : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hState : ∃ shared store, state = EvmYul.Yul.State.Ok shared store)
    (hNext : ∃ shared store, next.reviveJump = EvmYul.Yul.State.Ok shared store) :
    ((next.reviveJump.overwrite? state).setStore state)[name]! = state[name]! := by
  rcases hState with ⟨shared, store, rfl⟩
  rcases hNext with ⟨shared', store', hNextOk⟩
  simp [EvmYul.Yul.State.overwrite?]
  rw [hNextOk, state_getElem_setStore_ok]

theorem nativeSwitchDiscrTempName_ne_matchedTempName
    (switchId : Nat) :
    Backends.nativeSwitchDiscrTempName switchId ≠
      Backends.nativeSwitchMatchedTempName switchId := by
  intro h
  have hlen := congrArg String.length h
  have hd :
      (toString "__verity_native_switch_discr_").length = 29 := by
    decide
  have hm :
      (toString "__verity_native_switch_matched_").length = 31 := by
    decide
  simp [Backends.nativeSwitchDiscrTempName,
    Backends.nativeSwitchMatchedTempName, hd, hm] at hlen

theorem nativeSwitchPrefixFinalState_matched
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName)[matchedName]! = EvmYul.UInt256.ofNat 0 := by
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem nativeSwitchPrefixFinalState_discr
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (selector : Nat)
    (hne : discrName ≠ matchedName)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus) :
    (nativeSwitchPrefixFinalState contract tx storage observableSlots discrName matchedName)[discrName]! =
      EvmYul.UInt256.ofNat selector := by
  rw [hSelector]
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne]
  · rw [Finmap.lookup_insert]
    simp
  · exact hne

theorem nativeSwitchPrefixFinalState_marked
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    ((nativeSwitchPrefixFinalState contract tx storage observableSlots discrName matchedName).insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
      EvmYul.UInt256.ofNat 1 := by
  simp [nativeSwitchPrefixFinalState, nativeSwitchInitialOkState,
    EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

def nativeSwitchPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat) :
    EvmYul.Yul.State :=
  nativeSwitchPrefixFinalState contract tx storage observableSlots
    (Backends.nativeSwitchDiscrTempName switchId)
    (Backends.nativeSwitchMatchedTempName switchId)

def nativeSwitchMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (switchId : Nat) :
    EvmYul.Yul.State :=
  (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

theorem NativeBlockPreservesWord_nil
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeBlockPreservesWord name value [] codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      exact hLookup

theorem NativeBlockPreservesWord_cons
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hHead :
      ∀ fuel state next,
        state[name]! = value →
          EvmYul.Yul.exec fuel stmt codeOverride state = .ok next →
            next[name]! = value)
    (hRest : NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hStmt : EvmYul.Yul.exec fuel' stmt codeOverride state with
      | error err =>
          simp [hStmt] at hExec
      | ok next =>
          simp [hStmt] at hExec
          have hNext : next[name]! = value :=
            hHead fuel' state next hLookup hStmt
          exact hRest fuel' next final hNext hExec

theorem NativeBlockPreservesWord_cons_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hHead : NativeStmtPreservesWord name value stmt codeOverride)
    (hRest : NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride :=
  NativeBlockPreservesWord_cons name value stmt rest codeOverride hHead hRest

theorem NativeBlockPreservesWord_singleton
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hStmt : NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value [stmt] codeOverride := by
  exact NativeBlockPreservesWord_cons_stmt name value stmt [] codeOverride
    hStmt (NativeBlockPreservesWord_nil name value codeOverride)

theorem NativeBlockPreservesWord_of_forall_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride := by
  induction body with
  | nil =>
      exact NativeBlockPreservesWord_nil name value codeOverride
  | cons stmt rest ih =>
      refine NativeBlockPreservesWord_cons_stmt name value stmt rest
        codeOverride ?_ ?_
      · exact hPreserves stmt (by simp)
      · exact ih (by
          intro stmt' hmem
          exact hPreserves stmt' (by simp [hmem]))

theorem NativeBlockPreservesWord_of_forall_stmt_write_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      ∀ stmt, stmt ∈ body → name ∉ Backends.nativeStmtWriteNames stmt)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt name value body codeOverride
    (by
      intro stmt hmem
      exact hPreserves stmt hmem (hFresh stmt hmem))

theorem nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (body : List EvmYul.Yul.Ast.Stmt)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames body)
    (hMem : stmt ∈ body) :
    name ∉ Backends.nativeStmtWriteNames stmt := by
  induction body with
  | nil =>
      simp at hMem
  | cons head tail ih =>
      simp [Backends.nativeStmtsWriteNames,
        Backends.collectNativeStmtWriteNames] at hFresh hMem
      rcases hMem with hEq | hTail
      · subst stmt
        exact hFresh.1
      · exact ih hFresh.2 hTail

theorem collectNativeStmtWriteNames_append
    (writeStmt : EvmYul.Yul.Ast.Stmt → List String)
    (left right : List EvmYul.Yul.Ast.Stmt) :
    Backends.collectNativeStmtWriteNames writeStmt (left ++ right) =
      Backends.collectNativeStmtWriteNames writeStmt left ++
        Backends.collectNativeStmtWriteNames writeStmt right := by
  induction left with
  | nil =>
      simp [Backends.collectNativeStmtWriteNames]
  | cons head tail ih =>
      simp [Backends.collectNativeStmtWriteNames, ih, List.append_assoc]

theorem nativeStmtsWriteNames_append
    (left right : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames (left ++ right) =
      Backends.nativeStmtsWriteNames left ++ Backends.nativeStmtsWriteNames right := by
  simp [Backends.nativeStmtsWriteNames, collectNativeStmtWriteNames_append]

theorem nativeStmtsWriteNames_cons
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt) :
    Backends.nativeStmtsWriteNames (stmt :: rest) =
      Backends.nativeStmtWriteNames stmt ++ Backends.nativeStmtsWriteNames rest := by
  simp [Backends.nativeStmtsWriteNames, Backends.collectNativeStmtWriteNames]

theorem nativeStmtsWriteNames_cons_not_mem_iff
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames (stmt :: rest) ↔
      name ∉ Backends.nativeStmtWriteNames stmt ∧
        name ∉ Backends.nativeStmtsWriteNames rest := by
  rw [nativeStmtsWriteNames_cons, List.mem_append]
  constructor
  · intro hFresh
    exact ⟨fun hMem => hFresh (Or.inl hMem),
      fun hMem => hFresh (Or.inr hMem)⟩
  · intro hFresh hMem
    rcases hFresh with ⟨hHead, hTail⟩
    rcases hMem with hMem | hMem
    · exact hHead hMem
    · exact hTail hMem

theorem nativeStmtsWriteNames_head_not_mem_of_cons_not_mem
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (stmt :: rest)) :
    name ∉ Backends.nativeStmtWriteNames stmt := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_cons]
  exact List.mem_append_left _ hMem

theorem nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (stmt :: rest)) :
    name ∉ Backends.nativeStmtsWriteNames rest := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_cons]
  exact List.mem_append_right _ hMem

theorem nativeStmtsWriteNames_left_not_mem_of_append_not_mem
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (left ++ right)) :
    name ∉ Backends.nativeStmtsWriteNames left := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_append]
  exact List.mem_append_left _ hMem

theorem nativeStmtsWriteNames_right_not_mem_of_append_not_mem
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (left ++ right)) :
    name ∉ Backends.nativeStmtsWriteNames right := by
  intro hMem
  apply hFresh
  rw [nativeStmtsWriteNames_append]
  exact List.mem_append_right _ hMem

theorem nativeStmtsWriteNames_append_not_mem_iff
    (name : EvmYul.Identifier)
    (left right : List EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames (left ++ right) ↔
      name ∉ Backends.nativeStmtsWriteNames left ∧
        name ∉ Backends.nativeStmtsWriteNames right := by
  rw [nativeStmtsWriteNames_append, List.mem_append]
  constructor
  · intro hFresh
    exact ⟨fun hMem => hFresh (Or.inl hMem),
      fun hMem => hFresh (Or.inr hMem)⟩
  · intro hFresh hMem
    rcases hFresh with ⟨hLeft, hRight⟩
    rcases hMem with hMem | hMem
    · exact hLeft hMem
    · exact hRight hMem

theorem nativeStmtsWriteNames_singleton_not_mem_iff
    (name : EvmYul.Identifier)
    (stmt : EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames [stmt] ↔
      name ∉ Backends.nativeStmtWriteNames stmt := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff]
  constructor
  · intro hFresh
    exact hFresh.1
  · intro hFresh
    exact ⟨hFresh, by simp [Backends.nativeStmtsWriteNames,
      Backends.collectNativeStmtWriteNames]⟩

theorem nativeStmtsWriteNames_pair_not_mem_iff
    (name : EvmYul.Identifier)
    (first second : EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames [first, second] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_singleton_not_mem_iff]

theorem nativeStmtsWriteNames_triple_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third : EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames [first, second, third] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_pair_not_mem_iff]

theorem nativeStmtsWriteNames_quad_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth : EvmYul.Yul.Ast.Stmt) :
    name ∉ Backends.nativeStmtsWriteNames [first, second, third, fourth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_triple_not_mem_iff]

theorem nativeStmtsWriteNames_quint_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames [first, second, third, fourth, fifth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_quad_not_mem_iff]

theorem nativeStmtsWriteNames_sext_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_quint_not_mem_iff]

theorem nativeStmtsWriteNames_sept_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_sext_not_mem_iff]

theorem nativeStmtsWriteNames_oct_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth :
      EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_sept_not_mem_iff]

theorem nativeStmtsWriteNames_nona_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth :
      EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_oct_not_mem_iff]

theorem nativeStmtsWriteNames_deca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth :
      EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_nona_not_mem_iff]

theorem nativeStmtsWriteNames_undeca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_deca_not_mem_iff]

theorem nativeStmtsWriteNames_duodeca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_undeca_not_mem_iff]

theorem nativeStmtsWriteNames_tredeca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_duodeca_not_mem_iff]

theorem nativeStmtsWriteNames_quattuordeca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_tredeca_not_mem_iff]

theorem nativeStmtsWriteNames_quindeca_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth :
        EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_quattuordeca_not_mem_iff]

theorem nativeStmtsWriteNames_sedecim_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth sixteenth :
        EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth, sixteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth ∧
                                    name ∉ Backends.nativeStmtWriteNames
                                      sixteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_quindeca_not_mem_iff]

theorem nativeStmtsWriteNames_septendecim_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth :
        EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth, sixteenth, seventeenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth ∧
                                    name ∉ Backends.nativeStmtWriteNames
                                      sixteenth ∧
                                      name ∉ Backends.nativeStmtWriteNames
                                        seventeenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_sedecim_not_mem_iff]

theorem nativeStmtsWriteNames_octodecim_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
      eighteenth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth, sixteenth, seventeenth, eighteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth ∧
                                    name ∉ Backends.nativeStmtWriteNames
                                      sixteenth ∧
                                      name ∉ Backends.nativeStmtWriteNames
                                        seventeenth ∧
                                        name ∉ Backends.nativeStmtWriteNames
                                          eighteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_septendecim_not_mem_iff]

theorem nativeStmtsWriteNames_nonadecim_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
      eighteenth nineteenth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth, sixteenth, seventeenth, eighteenth, nineteenth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth ∧
                                    name ∉ Backends.nativeStmtWriteNames
                                      sixteenth ∧
                                      name ∉ Backends.nativeStmtWriteNames
                                        seventeenth ∧
                                        name ∉ Backends.nativeStmtWriteNames
                                          eighteenth ∧
                                          name ∉ Backends.nativeStmtWriteNames
                                            nineteenth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_octodecim_not_mem_iff]

theorem nativeStmtsWriteNames_viginti_not_mem_iff
    (name : EvmYul.Identifier)
    (first second third fourth fifth sixth seventh eighth ninth tenth
      eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
      eighteenth nineteenth twentieth : EvmYul.Yul.Ast.Stmt) :
    name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth, fourteenth,
            fifteenth, sixteenth, seventeenth, eighteenth, nineteenth,
            twentieth] ↔
      name ∉ Backends.nativeStmtWriteNames first ∧
        name ∉ Backends.nativeStmtWriteNames second ∧
          name ∉ Backends.nativeStmtWriteNames third ∧
            name ∉ Backends.nativeStmtWriteNames fourth ∧
              name ∉ Backends.nativeStmtWriteNames fifth ∧
                name ∉ Backends.nativeStmtWriteNames sixth ∧
                  name ∉ Backends.nativeStmtWriteNames seventh ∧
                    name ∉ Backends.nativeStmtWriteNames eighth ∧
                      name ∉ Backends.nativeStmtWriteNames ninth ∧
                        name ∉ Backends.nativeStmtWriteNames tenth ∧
                          name ∉ Backends.nativeStmtWriteNames eleventh ∧
                            name ∉ Backends.nativeStmtWriteNames twelfth ∧
                              name ∉ Backends.nativeStmtWriteNames
                                thirteenth ∧
                                name ∉ Backends.nativeStmtWriteNames
                                  fourteenth ∧
                                  name ∉ Backends.nativeStmtWriteNames
                                    fifteenth ∧
                                    name ∉ Backends.nativeStmtWriteNames
                                      sixteenth ∧
                                      name ∉ Backends.nativeStmtWriteNames
                                        seventeenth ∧
                                        name ∉ Backends.nativeStmtWriteNames
                                          eighteenth ∧
                                          name ∉ Backends.nativeStmtWriteNames
                                            nineteenth ∧
                                            name ∉ Backends.nativeStmtWriteNames
                                              twentieth := by
  rw [nativeStmtsWriteNames_cons_not_mem_iff,
    nativeStmtsWriteNames_nonadecim_not_mem_iff]

theorem NativeBlockPreservesWord_append_of_forall_stmt
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hLeft :
      ∀ stmt, stmt ∈ left →
        NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt name value (left ++ right)
    codeOverride
    (by
      intro stmt hMem
      rw [List.mem_append] at hMem
      rcases hMem with hMem | hMem
      · exact hLeft stmt hMem
      · exact hRight stmt hMem)

theorem NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value body codeOverride :=
  NativeBlockPreservesWord_of_forall_stmt_write_not_mem name value body
    codeOverride
    (by
      intro stmt hMem
      exact nativeStmtWriteNames_not_mem_of_nativeStmtsWriteNames_not_mem
        name body stmt hFresh hMem)
    hPreserves

theorem NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (stmt :: rest))
    (hHead :
      name ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord name value stmt codeOverride)
    (hRest :
      name ∉ Backends.nativeStmtsWriteNames rest →
        NativeBlockPreservesWord name value rest codeOverride) :
    NativeBlockPreservesWord name value (stmt :: rest) codeOverride :=
  NativeBlockPreservesWord_cons_stmt name value stmt rest codeOverride
    (hHead
      (nativeStmtsWriteNames_head_not_mem_of_cons_not_mem
        name stmt rest hFresh))
    (hRest
      (nativeStmtsWriteNames_tail_not_mem_of_cons_not_mem
        name stmt rest hFresh))

theorem NativeBlockPreservesWord_singleton_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [stmt])
    (hStmt :
      name ∉ Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value [stmt] codeOverride :=
  NativeBlockPreservesWord_singleton name value stmt codeOverride
    (hStmt
      ((nativeStmtsWriteNames_singleton_not_mem_iff name stmt).mp hFresh))

theorem NativeBlockPreservesWord_pair_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride) :
    NativeBlockPreservesWord name value [first, second] codeOverride := by
  rcases (nativeStmtsWriteNames_pair_not_mem_iff name first second).mp hFresh with
    ⟨hFirstFresh, hSecondFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first [second] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_singleton name value second codeOverride
      (hSecond hSecondFresh))

theorem NativeBlockPreservesWord_triple_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride) :
    NativeBlockPreservesWord name value [first, second, third] codeOverride := by
  rcases (nativeStmtsWriteNames_triple_not_mem_iff
    name first second third).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first [second, third]
    codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_pair_of_nativeStmtsWriteNames_not_mem
      name value second third codeOverride
      ((nativeStmtsWriteNames_pair_not_mem_iff name second third).mpr
        ⟨hSecondFresh, hThirdFresh⟩)
      hSecond hThird)

theorem NativeBlockPreservesWord_quad_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames [first, second, third, fourth])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth]
      codeOverride := by
  rcases (nativeStmtsWriteNames_quad_not_mem_iff
    name first second third fourth).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh, hFourthFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first
    [second, third, fourth] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_triple_of_nativeStmtsWriteNames_not_mem
      name value second third fourth codeOverride
      ((nativeStmtsWriteNames_triple_not_mem_iff name second third fourth).mpr
        ⟨hSecondFresh, hThirdFresh, hFourthFresh⟩)
      hSecond hThird hFourth)

theorem NativeBlockPreservesWord_quint_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉
        Backends.nativeStmtsWriteNames [first, second, third, fourth, fifth])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth :
      name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth]
      codeOverride := by
  rcases (nativeStmtsWriteNames_quint_not_mem_iff
    name first second third fourth fifth).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first
    [second, third, fourth, fifth] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_quad_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth codeOverride
      ((nativeStmtsWriteNames_quad_not_mem_iff
        name second third fourth fifth).mpr
        ⟨hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh⟩)
      hSecond hThird hFourth hFifth)

theorem NativeBlockPreservesWord_sext_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth :
      name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth :
      name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride) :
    NativeBlockPreservesWord name value
      [first, second, third, fourth, fifth, sixth] codeOverride := by
  rcases (nativeStmtsWriteNames_sext_not_mem_iff
    name first second third fourth fifth sixth).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh,
      hSixthFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first
    [second, third, fourth, fifth, sixth] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_quint_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth codeOverride
      ((nativeStmtsWriteNames_quint_not_mem_iff
        name second third fourth fifth sixth).mpr
        ⟨hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh, hSixthFresh⟩)
      hSecond hThird hFourth hFifth hSixth)

theorem NativeBlockPreservesWord_sept_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth :
      name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth :
      name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh :
      name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride) :
    NativeBlockPreservesWord name value
      [first, second, third, fourth, fifth, sixth, seventh]
      codeOverride := by
  rcases (nativeStmtsWriteNames_sept_not_mem_iff
    name first second third fourth fifth sixth seventh).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh,
      hSixthFresh, hSeventhFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first
    [second, third, fourth, fifth, sixth, seventh] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_sext_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh codeOverride
      ((nativeStmtsWriteNames_sext_not_mem_iff
        name second third fourth fifth sixth seventh).mpr
        ⟨hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh, hSixthFresh,
          hSeventhFresh⟩)
      hSecond hThird hFourth hFifth hSixth hSeventh)

theorem NativeBlockPreservesWord_oct_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉
        Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth :
      name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth :
      name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh :
      name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth :
      name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth] codeOverride := by
  rcases (nativeStmtsWriteNames_oct_not_mem_iff
    name first second third fourth fifth sixth seventh eighth).mp hFresh with
    ⟨hFirstFresh, hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh,
      hSixthFresh, hSeventhFresh, hEighthFresh⟩
  exact NativeBlockPreservesWord_cons_stmt name value first
    [second, third, fourth, fifth, sixth, seventh, eighth] codeOverride
    (hFirst hFirstFresh)
    (NativeBlockPreservesWord_sept_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth codeOverride
      ((nativeStmtsWriteNames_sept_not_mem_iff
        name second third fourth fifth sixth seventh eighth).mpr
        ⟨hSecondFresh, hThirdFresh, hFourthFresh, hFifthFresh,
          hSixthFresh, hSeventhFresh, hEighthFresh⟩)
      hSecond hThird hFourth hFifth hSixth hSeventh hEighth)

theorem NativeBlockPreservesWord_nona_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth :
      EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth])
    (hFirst :
      name ∉ Backends.nativeStmtWriteNames first →
      NativeStmtPreservesWord name value first codeOverride)
    (hSecond :
      name ∉ Backends.nativeStmtWriteNames second →
      NativeStmtPreservesWord name value second codeOverride)
    (hThird :
      name ∉ Backends.nativeStmtWriteNames third →
      NativeStmtPreservesWord name value third codeOverride)
    (hFourth :
      name ∉ Backends.nativeStmtWriteNames fourth →
      NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth :
      name ∉ Backends.nativeStmtWriteNames fifth →
      NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth :
      name ∉ Backends.nativeStmtWriteNames sixth →
      NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh :
      name ∉ Backends.nativeStmtWriteNames seventh →
      NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth :
      name ∉ Backends.nativeStmtWriteNames eighth →
      NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth :
      name ∉ Backends.nativeStmtWriteNames ninth →
      NativeStmtPreservesWord name value ninth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_oct_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth codeOverride
        hRestFresh hSecond hThird hFourth hFifth hSixth hSeventh hEighth
        hNinth)

theorem NativeBlockPreservesWord_deca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth :
      EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_nona_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        codeOverride hRestFresh hSecond hThird hFourth hFifth hSixth hSeventh
        hEighth hNinth hTenth)

theorem NativeBlockPreservesWord_undeca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh :
      EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh →
        NativeStmtPreservesWord name value eleventh codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_deca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh codeOverride hRestFresh hSecond hThird hFourth hFifth hSixth
        hSeventh hEighth hNinth hTenth hEleventh)

theorem NativeBlockPreservesWord_duodeca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh →
        NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth →
        NativeStmtPreservesWord name value twelfth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth]
      codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_undeca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth codeOverride hRestFresh hSecond hThird hFourth hFifth
        hSixth hSeventh hEighth hNinth hTenth hEleventh hTwelfth)

theorem NativeBlockPreservesWord_tredeca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      name ∉ Backends.nativeStmtsWriteNames
          [first, second, third, fourth, fifth, sixth, seventh, eighth,
            ninth, tenth, eleventh, twelfth, thirteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh →
        NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth →
        NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth →
        NativeStmtPreservesWord name value thirteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth]
      codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_duodeca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth codeOverride hRestFresh hSecond hThird
        hFourth hFifth hSixth hSeventh hEighth hNinth hTenth hEleventh
        hTwelfth hThirteenth)

theorem NativeBlockPreservesWord_quattuordeca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh, twelfth,
      thirteenth, fourteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh →
        NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth →
        NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth →
        NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth →
        NativeStmtPreservesWord name value fourteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth] codeOverride
    hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_tredeca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth codeOverride hRestFresh hSecond
        hThird hFourth hFifth hSixth hSeventh hEighth hNinth hTenth hEleventh
        hTwelfth hThirteenth hFourteenth)

theorem NativeBlockPreservesWord_quindeca_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth →
        NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth →
        NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh →
        NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth →
        NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth]
    codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_quattuordeca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth codeOverride hRestFresh
        hSecond hThird hFourth hFifth hSixth hSeventh hEighth hNinth hTenth
        hEleventh hTwelfth hThirteenth hFourteenth hFifteenth)

theorem NativeBlockPreservesWord_sedecim_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth sixteenth :
      EvmYul.Yul.Ast.Stmt) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth, sixteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth → NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth → NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh → NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth → NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride)
    (hSixteenth : name ∉ Backends.nativeStmtWriteNames sixteenth → NativeStmtPreservesWord name value sixteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth, sixteenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth,
      sixteenth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_quindeca_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth sixteenth codeOverride
        hRestFresh hSecond hThird hFourth hFifth hSixth hSeventh hEighth
        hNinth hTenth hEleventh hTwelfth hThirteenth hFourteenth hFifteenth
        hSixteenth)

theorem NativeBlockPreservesWord_septendecim_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth sixteenth seventeenth :
      EvmYul.Yul.Ast.Stmt) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth, sixteenth, seventeenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth → NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth → NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh → NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth → NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride)
    (hSixteenth : name ∉ Backends.nativeStmtWriteNames sixteenth → NativeStmtPreservesWord name value sixteenth codeOverride)
    (hSeventeenth : name ∉ Backends.nativeStmtWriteNames seventeenth → NativeStmtPreservesWord name value seventeenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth, sixteenth, seventeenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth,
      sixteenth, seventeenth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_sedecim_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
        codeOverride hRestFresh hSecond hThird hFourth hFifth hSixth hSeventh
        hEighth hNinth hTenth hEleventh hTwelfth hThirteenth hFourteenth
        hFifteenth hSixteenth hSeventeenth)

theorem NativeBlockPreservesWord_octodecim_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth sixteenth seventeenth eighteenth :
      EvmYul.Yul.Ast.Stmt) (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth, sixteenth, seventeenth,
      eighteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first →
        NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second →
        NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third →
        NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth →
        NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth →
        NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth →
        NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh →
        NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth →
        NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth → NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth → NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh → NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth → NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride)
    (hSixteenth : name ∉ Backends.nativeStmtWriteNames sixteenth → NativeStmtPreservesWord name value sixteenth codeOverride)
    (hSeventeenth : name ∉ Backends.nativeStmtWriteNames seventeenth → NativeStmtPreservesWord name value seventeenth codeOverride)
    (hEighteenth : name ∉ Backends.nativeStmtWriteNames eighteenth → NativeStmtPreservesWord name value eighteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth, sixteenth, seventeenth, eighteenth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth,
      sixteenth, seventeenth, eighteenth] codeOverride hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_septendecim_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
        eighteenth codeOverride hRestFresh hSecond hThird hFourth hFifth hSixth
        hSeventh hEighth hNinth hTenth hEleventh hTwelfth hThirteenth
        hFourteenth hFifteenth hSixteenth hSeventeenth hEighteenth)

theorem NativeBlockPreservesWord_nonadecim_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth sixteenth seventeenth eighteenth
      nineteenth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth, sixteenth, seventeenth,
      eighteenth, nineteenth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first → NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second → NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third → NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth → NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth → NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth → NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh → NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth → NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth → NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth → NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh → NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth → NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride)
    (hSixteenth : name ∉ Backends.nativeStmtWriteNames sixteenth → NativeStmtPreservesWord name value sixteenth codeOverride)
    (hSeventeenth : name ∉ Backends.nativeStmtWriteNames seventeenth → NativeStmtPreservesWord name value seventeenth codeOverride)
    (hEighteenth : name ∉ Backends.nativeStmtWriteNames eighteenth → NativeStmtPreservesWord name value eighteenth codeOverride)
    (hNineteenth : name ∉ Backends.nativeStmtWriteNames nineteenth → NativeStmtPreservesWord name value nineteenth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth, sixteenth, seventeenth, eighteenth, nineteenth]
      codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth,
      sixteenth, seventeenth, eighteenth, nineteenth] codeOverride hFresh
    hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_octodecim_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
        eighteenth nineteenth codeOverride hRestFresh hSecond hThird hFourth
        hFifth hSixth hSeventh hEighth hNinth hTenth hEleventh hTwelfth
        hThirteenth hFourteenth hFifteenth hSixteenth hSeventeenth hEighteenth
        hNineteenth)

theorem NativeBlockPreservesWord_viginti_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier) (value : EvmYul.Literal)
    (first second third fourth fifth sixth seventh eighth ninth tenth eleventh
      twelfth thirteenth fourteenth fifteenth sixteenth seventeenth eighteenth
      nineteenth twentieth : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames [first, second, third,
      fourth, fifth, sixth, seventh, eighth, ninth, tenth, eleventh,
      twelfth, thirteenth, fourteenth, fifteenth, sixteenth, seventeenth,
      eighteenth, nineteenth, twentieth])
    (hFirst : name ∉ Backends.nativeStmtWriteNames first → NativeStmtPreservesWord name value first codeOverride)
    (hSecond : name ∉ Backends.nativeStmtWriteNames second → NativeStmtPreservesWord name value second codeOverride)
    (hThird : name ∉ Backends.nativeStmtWriteNames third → NativeStmtPreservesWord name value third codeOverride)
    (hFourth : name ∉ Backends.nativeStmtWriteNames fourth → NativeStmtPreservesWord name value fourth codeOverride)
    (hFifth : name ∉ Backends.nativeStmtWriteNames fifth → NativeStmtPreservesWord name value fifth codeOverride)
    (hSixth : name ∉ Backends.nativeStmtWriteNames sixth → NativeStmtPreservesWord name value sixth codeOverride)
    (hSeventh : name ∉ Backends.nativeStmtWriteNames seventh → NativeStmtPreservesWord name value seventh codeOverride)
    (hEighth : name ∉ Backends.nativeStmtWriteNames eighth → NativeStmtPreservesWord name value eighth codeOverride)
    (hNinth : name ∉ Backends.nativeStmtWriteNames ninth → NativeStmtPreservesWord name value ninth codeOverride)
    (hTenth : name ∉ Backends.nativeStmtWriteNames tenth → NativeStmtPreservesWord name value tenth codeOverride)
    (hEleventh : name ∉ Backends.nativeStmtWriteNames eleventh → NativeStmtPreservesWord name value eleventh codeOverride)
    (hTwelfth : name ∉ Backends.nativeStmtWriteNames twelfth → NativeStmtPreservesWord name value twelfth codeOverride)
    (hThirteenth : name ∉ Backends.nativeStmtWriteNames thirteenth → NativeStmtPreservesWord name value thirteenth codeOverride)
    (hFourteenth : name ∉ Backends.nativeStmtWriteNames fourteenth → NativeStmtPreservesWord name value fourteenth codeOverride)
    (hFifteenth : name ∉ Backends.nativeStmtWriteNames fifteenth → NativeStmtPreservesWord name value fifteenth codeOverride)
    (hSixteenth : name ∉ Backends.nativeStmtWriteNames sixteenth → NativeStmtPreservesWord name value sixteenth codeOverride)
    (hSeventeenth : name ∉ Backends.nativeStmtWriteNames seventeenth → NativeStmtPreservesWord name value seventeenth codeOverride)
    (hEighteenth : name ∉ Backends.nativeStmtWriteNames eighteenth → NativeStmtPreservesWord name value eighteenth codeOverride)
    (hNineteenth : name ∉ Backends.nativeStmtWriteNames nineteenth → NativeStmtPreservesWord name value nineteenth codeOverride)
    (hTwentieth : name ∉ Backends.nativeStmtWriteNames twentieth → NativeStmtPreservesWord name value twentieth codeOverride) :
    NativeBlockPreservesWord name value [first, second, third, fourth, fifth,
      sixth, seventh, eighth, ninth, tenth, eleventh, twelfth, thirteenth,
      fourteenth, fifteenth, sixteenth, seventeenth, eighteenth, nineteenth,
      twentieth] codeOverride := by
  exact NativeBlockPreservesWord_cons_of_nativeStmtsWriteNames_not_mem
    name value first [second, third, fourth, fifth, sixth, seventh, eighth,
      ninth, tenth, eleventh, twelfth, thirteenth, fourteenth, fifteenth,
      sixteenth, seventeenth, eighteenth, nineteenth, twentieth] codeOverride
    hFresh hFirst
    (fun hRestFresh =>
      NativeBlockPreservesWord_nonadecim_of_nativeStmtsWriteNames_not_mem
      name value second third fourth fifth sixth seventh eighth ninth tenth
        eleventh twelfth thirteenth fourteenth fifteenth sixteenth seventeenth
        eighteenth nineteenth twentieth codeOverride hRestFresh hSecond hThird
        hFourth hFifth hSixth hSeventh hEighth hNinth hTenth hEleventh
        hTwelfth hThirteenth hFourteenth hFifteenth hSixteenth hSeventeenth
        hEighteenth hNineteenth hTwentieth)

theorem NativeStmtPreservesWord_block
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.Block body) codeOverride :=
  hBody

theorem NativeStmtPreservesWord_block_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.Block body) codeOverride :=
  NativeStmtPreservesWord_block name value body codeOverride
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hLeftFresh : name ∉ Backends.nativeStmtsWriteNames left)
    (hRightFresh : name ∉ Backends.nativeStmtsWriteNames right)
    (hLeft :
      ∀ stmt, stmt ∈ left →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem name value
    (left ++ right) codeOverride
    (by
      rw [nativeStmtsWriteNames_append]
      intro hMem
      rw [List.mem_append] at hMem
      rcases hMem with hMem | hMem
      · exact hLeftFresh hMem
      · exact hRightFresh hMem)
    (by
      intro stmt hMem hFresh
      rw [List.mem_append] at hMem
      rcases hMem with hMem | hMem
      · exact hLeft stmt hMem hFresh
      · exact hRight stmt hMem hFresh)

theorem NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_append_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames (left ++ right))
    (hLeft :
      ∀ stmt, stmt ∈ left →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride)
    (hRight :
      ∀ stmt, stmt ∈ right →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeBlockPreservesWord name value (left ++ right) codeOverride :=
  NativeBlockPreservesWord_append_of_nativeStmtsWriteNames_not_mem
    name value left right codeOverride
    (nativeStmtsWriteNames_left_not_mem_of_append_not_mem
      name left right hFresh)
    (nativeStmtsWriteNames_right_not_mem_of_append_not_mem
      name left right hFresh)
    hLeft hRight

theorem NativeStmtPreservesWord_if_of_eval_self
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (state, condValue))
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hCond fuel' state hLookup with ⟨condValue, hEval⟩
      simp [EvmYul.Yul.exec, hEval] at hExec
      by_cases hCondNonzero : condValue ≠ ⟨0⟩
      · simp [hCondNonzero] at hExec
        exact hBody fuel' state final hLookup hExec
      · have hCondZero : condValue = ⟨0⟩ := by
          exact Decidable.not_not.mp hCondNonzero
        simp [hCondZero] at hExec
        cases hExec
        exact hLookup

theorem NativeStmtPreservesWord_if_of_eval_preserves
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hCond fuel' state hLookup with
        ⟨condState, condValue, hEval, hCondLookup⟩
      simp [EvmYul.Yul.exec, hEval] at hExec
      by_cases hCondNonzero : condValue ≠ ⟨0⟩
      · simp [hCondNonzero] at hExec
        exact hBody fuel' condState final hCondLookup hExec
      · have hCondZero : condValue = ⟨0⟩ := by
          exact Decidable.not_not.mp hCondNonzero
        simp [hCondZero] at hExec
        cases hExec
        exact hCondLookup

theorem NativeStmtPreservesWord_if_of_eval_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond :
      ∀ fuel state,
        state[name]! = value →
          ∃ condState condValue,
            EvmYul.Yul.eval fuel cond codeOverride state =
              .ok (condState, condValue) ∧
            condState[name]! = value)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride :=
  NativeStmtPreservesWord_if_of_eval_preserves name value cond body codeOverride
    hCond
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

theorem NativeStmtPreservesWord_if_of_cond_preserves
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hBody : NativeBlockPreservesWord name value body codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEval : EvmYul.Yul.eval fuel' cond codeOverride state with
      | error err =>
          simp [hEval] at hExec
      | ok condResult =>
          rcases condResult with ⟨condState, condValue⟩
          have hCondLookup : condState[name]! = value :=
            hCond fuel' state condState condValue hLookup hEval
          simp [hEval] at hExec
          by_cases hCondNonzero : condValue ≠ ⟨0⟩
          · simp [hCondNonzero] at hExec
            exact hBody fuel' condState final hCondLookup hExec
          · have hCondZero : condValue = ⟨0⟩ :=
              Decidable.not_not.mp hCondNonzero
            simp [hCondZero] at hExec
            cases hExec
            exact hCondLookup

theorem NativeStmtPreservesWord_if_of_cond_preserves_and_nativeStmtsWriteNames_not_mem
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hCond : NativeExprPreservesWord name value cond codeOverride)
    (hFresh : name ∉ Backends.nativeStmtsWriteNames body)
    (hPreserves :
      ∀ stmt, stmt ∈ body →
        name ∉ Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord name value stmt codeOverride) :
    NativeStmtPreservesWord name value (.If cond body) codeOverride :=
  NativeStmtPreservesWord_if_of_cond_preserves name value cond body codeOverride
    hCond
    (NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
      name value body codeOverride hFresh hPreserves)

theorem NativeStmtPreservesWord_lowerAssignNative_lit_of_ne
    (name target : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (assigned : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.lit assigned)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target
        (EvmYul.UInt256.ofNat assigned) hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_hex_of_ne
    (name target : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (assigned : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.hex assigned)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [Backends.lowerAssignNative, Backends.lowerExprNative] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name target
        (EvmYul.UInt256.ofNat assigned) hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_ident_of_ne
    (name target source : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.ident source)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      have hFinal : state.insert target state[source]! = final := by
        simpa [Backends.lowerAssignNative, Backends.lowerExprNative,
          EvmYul.Yul.exec] using hExec
      subst final
      rw [state_getElem_insert_of_ne state name target state[source]! hne]
      exact hLookup

theorem NativeStmtPreservesWord_lowerAssignNative_str_of_ne
    (name target source : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.str source)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      have hFinal : state.insert target state[source]! = final := by
        simpa [Backends.lowerAssignNative, Backends.lowerExprNative,
          EvmYul.Yul.exec] using hExec
      subst final
      rw [state_getElem_insert_of_ne state name target state[source]! hne]
      exact hLookup

theorem NativeStmtPreservesWord_let_none_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected (.Let vars none) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_foldr_insert_zero_of_not_mem state name vars hnot]
      exact hLookup

theorem NativeStmtPreservesWord_let_var_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Var identifier))) codeOverride := by
  intro fuel state final hLookup hExec
  rcases List.exists_cons_of_ne_nil hvars with ⟨head, tail, rfl⟩
  simp at hnot
  rcases hnot with ⟨hneq, _⟩
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name head state[identifier]! hneq]
      exact hLookup

theorem NativeStmtPreservesWord_let_lit_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Lit literal))) codeOverride := by
  intro fuel state final hLookup hExec
  rcases List.exists_cons_of_ne_nil hvars with ⟨head, tail, rfl⟩
  simp at hnot
  rcases hnot with ⟨hneq, _⟩
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hExec
      rw [state_getElem_insert_of_ne state name head literal hneq]
      exact hLookup

theorem NativeStmtPreservesWord_let_lowerExprNative_lit_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.lit literal))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_lit_of_not_mem name expected vars
      (EvmYul.UInt256.ofNat literal) codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_hex_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (literal : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.hex literal))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_lit_of_not_mem name expected vars
      (EvmYul.UInt256.ofNat literal) codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_str_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.str identifier))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_var_of_not_mem name expected vars identifier
      codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_lowerExprNative_ident_of_not_mem
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hvars : vars ≠ [])
    (hnot : name ∉ vars) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.ident identifier))))
      codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeStmtPreservesWord_let_var_of_not_mem name expected vars identifier
      codeOverride hvars hnot

theorem NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier) (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected →
          EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets, state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected (.Let vars (some (.Call (Sum.inl prim) args))) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse',
            EvmYul.Yul.execPrimCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          simp [hEvalArgs, EvmYul.Yul.reverse',
            EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall] at hExec
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall] at hExec
              cases hExec
              have hPrimLookup : primState[name]! = expected :=
                hPrim fuel' argState values.reverse primState rets hArgLookup
                  hPrimCall
              rw [state_getElem_multifill_of_not_mem primState name vars rets
                hnot]
              exact hPrimLookup

theorem NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal) (vars : List EvmYul.Identifier)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected → EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) → argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets, state[name]! = expected → EvmYul.Yul.call fuel values (some functionName) codeOverride state = .ok (callState, rets) → callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (.Call (Sum.inr functionName) args))) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          cases fuel' with
          | zero =>
              simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall]
                at hExec
          | succ callFuel =>
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
                  cases hExec
                  have hCallLookup : callState[name]! = expected :=
                    hCall callFuel argState values.reverse callState rets
                      hArgLookup hUserCall
                  rw [state_getElem_multifill_of_not_mem callState name vars rets hnot]
                  exact hCallLookup

theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    name expected vars op (args.map Backends.lowerExprNative) codeOverride
    hnot hArgs hPrim

theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    name expected vars func (args.map Backends.lowerExprNative) codeOverride
    hnot hArgs hCall

theorem NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride :=
  NativeStmtPreservesWord_let_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name func expected vars args op codeOverride hnot hOp hArgs hPrim

theorem NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (vars : List EvmYul.Identifier)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hnot : name ∉ vars)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.Let vars (some (Backends.lowerExprNative (.call func args))))
      codeOverride :=
  NativeStmtPreservesWord_let_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    name func expected vars args codeOverride hnot hOp hArgs hCall

theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride := by
  rw [Backends.lowerAssignNative,
    Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_let_prim_of_evalArgs_primCall_preserves
    name expected [target] op (args.map Backends.lowerExprNative) codeOverride
    (by simp [hne]) hArgs hPrim

theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride := by
  rw [Backends.lowerAssignNative,
    Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_let_user_of_evalArgs_call_preserves
    name expected [target] func (args.map Backends.lowerExprNative) codeOverride
    (by simp [hne]) hArgs hCall

theorem NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values primState rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (primState, rets) →
          primState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride :=
  NativeStmtPreservesWord_lowerAssignNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name target func expected args op codeOverride hne hOp hArgs hPrim

theorem NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name target func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hne : name ≠ target)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values callState rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (callState, rets) →
          callState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (Backends.lowerAssignNative target (.call func args)) codeOverride :=
  NativeStmtPreservesWord_lowerAssignNative_call_userFunction_of_evalArgs_call_preserves
    name target func expected args codeOverride hne hOp hArgs hCall

theorem NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl prim) args)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execPrimCall,
            EvmYul.Yul.multifill'] at hExec
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall] at hExec
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall, EvmYul.Yul.State.multifill] at hExec
              cases hExec
              have hPrimLookup : primState[name]! = expected :=
                hPrim fuel' argState values.reverse primState rets hArgLookup
                  hPrimCall
              cases primState <;> simpa using hPrimLookup

theorem NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state argState values, state[name]! = expected → EvmYul.Yul.evalArgs fuel args.reverse codeOverride state = .ok (argState, values) → argState[name]! = expected)
    (hCall :
      ∀ fuel state values final rets, state[name]! = expected → EvmYul.Yul.call fuel values (some functionName) codeOverride state = .ok (final, rets) → final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inr functionName) args)) codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      simp [EvmYul.Yul.exec] at hExec
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall] at hExec
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          cases fuel' with
          | zero =>
              simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall]
                at hExec
          | succ callFuel =>
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill'] at hExec
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hEvalArgs, EvmYul.Yul.reverse', EvmYul.Yul.execCall, hUserCall,
                    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill] at hExec
                  cases hExec
                  have hCallLookup : callState[name]! = expected :=
                    hCall callFuel argState values.reverse callState rets
                      hArgLookup hUserCall
                  cases callState <;> simpa using hCallLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeStmtPreservesWord_exprStmtCall_prim_of_evalArgs_primCall_preserves
    name expected op (args.map Backends.lowerExprNative) codeOverride hArgs
    hPrim

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      ∀ fuel state argState values,
        state[name]! = expected →
          EvmYul.Yul.evalArgs fuel
              ((args.map Backends.lowerExprNative).reverse) codeOverride state =
            .ok (argState, values) →
          argState[name]! = expected)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeStmtPreservesWord_exprStmtCall_user_of_evalArgs_call_preserves
    name expected func (args.map Backends.lowerExprNative) codeOverride hArgs
    hCall

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name func expected args op codeOverride hOp hArgs hPrim

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call func args)))
      codeOverride :=
  NativeStmtPreservesWord_exprStmtCall_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    name func expected args codeOverride hOp hArgs hCall

theorem NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_mstore_ok] at hExec
          simp [EvmYul.Yul.State.multifill] at hExec
          cases hExec
          cases argState with
          | Ok shared store =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | OutOfFuel =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | Checkpoint jump =>
              cases jump <;>
                simpa [EvmYul.Yul.State.setMachineState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore" args
    EvmYul.Operation.MSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.MSTORE8) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_mstore8_ok] at hExec
          simp [EvmYul.Yul.State.multifill] at hExec
          cases hExec
          cases argState with
          | Ok shared store =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | OutOfFuel =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | Checkpoint jump =>
              cases jump <;>
                simpa [EvmYul.Yul.State.setMachineState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_mstore8_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "mstore8" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "mstore8" args
    EvmYul.Operation.MSTORE8 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_mstore8_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.SSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, slot, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_sstore_ok primFuel argState slot value hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_sstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "sstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "sstore" args
    EvmYul.Operation.SSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_sstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.TSTORE) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, slot, value, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_tstore_ok primFuel argState slot value hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_tstore_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState slot value,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [value, slot]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "tstore" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "tstore" args
    EvmYul.Operation.TSTORE (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_tstore_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, datastart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.CALLDATACOPY) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, mstart, datastart, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_calldatacopy_ok] at hExec
          simp [EvmYul.Yul.State.multifill] at hExec
          cases hExec
          cases argState with
          | Ok shared store =>
              simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
          | OutOfFuel =>
              simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
          | Checkpoint jump =>
              cases jump <;>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_calldatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart datastart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, datastart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "calldatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "calldatacopy" args
    EvmYul.Operation.CALLDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_calldatacopy_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, rstart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURNDATACOPY) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, mstart, rstart, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          rw [primCall_returndatacopy_ok] at hExec
          simp [EvmYul.Yul.State.multifill] at hExec
          cases hExec
          cases argState with
          | Ok shared store =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | OutOfFuel =>
              simpa [EvmYul.Yul.State.setMachineState] using hArgLookup
          | Checkpoint jump =>
              cases jump <;>
                simpa [EvmYul.Yul.State.setMachineState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_returndatacopy_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState mstart rstart size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, rstart, mstart]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "returndatacopy" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "returndatacopy" args
    EvmYul.Operation.RETURNDATACOPY (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_returndatacopy_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG0) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log0_ok primFuel argState offset size hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log0_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log0" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log0" args
    EvmYul.Operation.LOG0 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log0_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG1) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log1_ok primFuel argState offset size topic0 hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log1_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log1" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log1" args
    EvmYul.Operation.LOG1 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log1_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG2) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log2_ok primFuel argState offset size topic0 topic1 hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log2_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log2" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log2" args
    EvmYul.Operation.LOG2 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log2_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG3) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log3_ok primFuel argState offset size topic0 topic1 topic2 hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log3_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log3" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log3" args
    EvmYul.Operation.LOG3 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log3_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.LOG4) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, topic0, topic1, topic2, topic3, hEval, hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ primFuel =>
          cases hPerm : argState.executionEnv.perm
          · simp [EvmYul.Yul.primCall, hPerm,
              EvmYul.Yul.State.multifill] at hExec
            cases hExec
          · rw [primCall_log4_ok primFuel argState offset size topic0 topic1 topic2 topic3 hPerm] at hExec
            simp [EvmYul.Yul.State.multifill] at hExec
            cases hExec
            cases argState with
            | Ok shared store =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | OutOfFuel =>
                simpa [EvmYul.Yul.State.setSharedState] using hArgLookup
            | Checkpoint jump =>
                cases jump <;>
                  simpa [EvmYul.Yul.State.setSharedState] using hArgLookup

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_log4_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size topic0 topic1 topic2 topic3,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [topic3, topic2, topic1, topic0, size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "log4" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "log4" args
    EvmYul.Operation.LOG4 (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_log4_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.RETURN) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, _hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ returnFuel =>
          rw [primCall_return_ok returnFuel argState offset size] at hExec
          cases hReturn :
              EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
                argState [offset, size] with
          | error err =>
              simp [hReturn] at hExec
          | ok ret =>
              rcases ret with ⟨returnState, value⟩
              simp [hReturn] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_return_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "return" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "return" args
    EvmYul.Operation.RETURN (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_return_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel args.reverse codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.REVERT) args))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      rcases hArgs fuel' state hLookup with
        ⟨argState, offset, size, hEval, _hArgLookup⟩
      simp [EvmYul.Yul.exec, hEval, EvmYul.Yul.reverse',
        EvmYul.Yul.execPrimCall, EvmYul.Yul.multifill'] at hExec
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ revertFuel =>
          rw [primCall_revert_ok revertFuel argState offset size] at hExec
          cases hRevert :
              EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
                argState [offset, size] with
          | error err =>
              simp [hRevert] at hExec
          | ok ret =>
              rcases ret with ⟨revertState, value⟩
              simp [hRevert] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_revert_of_evalArgs_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ fuel state,
        state[name]! = expected →
          ∃ argState offset size,
            EvmYul.Yul.evalArgs fuel
                ((args.map Backends.lowerExprNative).reverse) codeOverride state =
              .ok (argState, [size, offset]) ∧
            argState[name]! = expected) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "revert" args)))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "revert" args
    EvmYul.Operation.REVERT (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_revert_of_evalArgs_preserves
    name expected (args.map Backends.lowerExprNative) codeOverride hArgs

theorem NativeStmtPreservesWord_exprStmtCall_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (.Call (Sum.inl EvmYul.Operation.STOP) []))
      codeOverride := by
  intro fuel state final hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.exec] at hExec
  | succ fuel' =>
      cases fuel' with
      | zero =>
          simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
            EvmYul.Yul.evalArgs, EvmYul.Yul.reverse'] at hExec
      | succ stopFuel =>
          simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall,
            EvmYul.Yul.evalArgs, EvmYul.Yul.reverse'] at hExec
          simp [EvmYul.Yul.multifill'] at hExec

theorem NativeStmtPreservesWord_exprStmtCall_lowerExprNative_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeStmtPreservesWord name expected
      (.ExprStmtCall (Backends.lowerExprNative (.call "stop" [])))
      codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp "stop" []
    EvmYul.Operation.STOP (by rfl)]
  exact NativeStmtPreservesWord_exprStmtCall_stop name expected codeOverride

theorem nativeSwitchTempsFreshForNativeBodies_case_matched_not_mem
    (switchId tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hMem : (tag, body) ∈ cases) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames body :=
  (hFresh.1 tag body hMem).2

theorem nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem
    (switchId tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hMem : (tag, body) ∈ cases) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames body :=
  (hFresh.1 tag body hMem).1

theorem nativeSwitchTempsFreshForNativeBodies_find_hit_matched_not_mem
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body)) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames body := by
  have hMem : (tag, body) ∈ cases := by
    clear hFresh
    induction cases with
    | nil =>
        simp [List.find?] at hFind
    | cons head rest ih =>
        cases hHead : (head.1 == selector)
        · simp [List.find?, hHead] at hFind
          exact List.mem_cons_of_mem head (ih hFind)
        · simp [List.find?, hHead] at hFind
          simp [hFind]
  exact nativeSwitchTempsFreshForNativeBodies_case_matched_not_mem
    switchId tag body defaultBody cases hFresh hMem

theorem nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body)) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames body := by
  have hMem : (tag, body) ∈ cases := by
    clear hFresh
    induction cases with
    | nil =>
        simp [List.find?] at hFind
    | cons head rest ih =>
        cases hHead : (head.1 == selector)
        · simp [List.find?, hHead] at hFind
          exact List.mem_cons_of_mem head (ih hFind)
        · simp [List.find?, hHead] at hFind
          simp [hFind]
  exact nativeSwitchTempsFreshForNativeBodies_case_discr_not_mem
    switchId tag body defaultBody cases hFresh hMem

theorem nativeSwitchTempsFreshForNativeBodies_default_matched_not_mem
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody) :
    Backends.nativeSwitchMatchedTempName switchId ∉
      Backends.nativeStmtsWriteNames defaultBody :=
  hFresh.2.2

theorem nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody) :
    Backends.nativeSwitchDiscrTempName switchId ∉
      Backends.nativeStmtsWriteNames defaultBody :=
  hFresh.2.1

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
      expected body codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchMatchedTempName switchId) expected body codeOverride
    (nativeSwitchTempsFreshForNativeBodies_find_hit_matched_not_mem
      switchId selector tag body defaultBody cases hFresh hFind)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_discr
    (switchId selector tag : Nat)
    (body defaultBody : List EvmYul.Yul.Ast.Stmt)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hFind : cases.find? (fun entry => entry.1 == selector) =
      some (tag, body))
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchDiscrTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
      expected body codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchDiscrTempName switchId) expected body codeOverride
    (nativeSwitchTempsFreshForNativeBodies_find_hit_discr_not_mem
      switchId selector tag body defaultBody cases hFresh hFind)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_matched
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ defaultBody →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
      expected defaultBody codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchMatchedTempName switchId) expected defaultBody
    codeOverride
    (nativeSwitchTempsFreshForNativeBodies_default_matched_not_mem
      switchId cases defaultBody hFresh)
    hStmtPreserves

theorem NativeBlockPreservesWord_of_nativeSwitchFresh_default_discr
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ defaultBody →
        Backends.nativeSwitchDiscrTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
        NativeStmtPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
          expected stmt codeOverride) :
    NativeBlockPreservesWord (Backends.nativeSwitchDiscrTempName switchId)
      expected defaultBody codeOverride :=
  NativeBlockPreservesWord_of_nativeStmtsWriteNames_not_mem
    (Backends.nativeSwitchDiscrTempName switchId) expected defaultBody
    codeOverride
    (nativeSwitchTempsFreshForNativeBodies_default_discr_not_mem
      switchId cases defaultBody hFresh)
    hStmtPreserves

@[simp] theorem nativeSwitchCaseIfs_nil
    (discrName matchedName : EvmYul.Identifier) :
    nativeSwitchCaseIfs discrName matchedName [] = [] := by
  rfl

@[simp] theorem nativeSwitchCaseIfs_cons
    (discrName matchedName : EvmYul.Identifier)
    (entry : Nat × List EvmYul.Yul.Ast.Stmt)
    (rest : List (Nat × List EvmYul.Yul.Ast.Stmt)) :
    nativeSwitchCaseIfs discrName matchedName (entry :: rest) =
      nativeSwitchCaseIf discrName matchedName entry ::
        nativeSwitchCaseIfs discrName matchedName rest := by
  rfl

private theorem list_find?_eq_some_split_false
    {α : Type}
    (p : α → Bool) :
    ∀ {xs : List α} {x : α},
      xs.find? p = some x →
        ∃ pre suffix,
          xs = pre ++ x :: suffix ∧
          ∀ y, y ∈ pre → p y = false
  | [], _, hFind => by
      simp [List.find?] at hFind
  | y :: ys, x, hFind => by
      by_cases hp : p y = true
      · have hxy : x = y := by
          simpa [List.find?, hp] using hFind.symm
        subst x
        exact ⟨[], ys, by simp, by simp⟩
      · have hFalse : p y = false := Bool.eq_false_iff.2 hp
        have hRest : ys.find? p = some x := by
          simpa [List.find?, hFalse] using hFind
        rcases list_find?_eq_some_split_false p hRest with
          ⟨pre, suffix, hSplit, hPre⟩
        refine ⟨y :: pre, suffix, ?_, ?_⟩
        · simp [hSplit]
        · intro z hz
          have hz' : z = y ∨ z ∈ pre := by
            simpa [List.mem_cons] using hz
          rcases hz' with hzy | hzPre
          · cases hzy
            exact hFalse
          · exact hPre z hzPre

private theorem list_find?_eq_none_all_false
    {α : Type}
    (p : α → Bool) :
    ∀ {xs : List α},
      xs.find? p = none →
        ∀ x, x ∈ xs → p x = false
  | [], hFind, x, hx => by
      simp at hx
  | y :: ys, hFind, x, hx => by
      by_cases hp : p y = true
      · simp [List.find?, hp] at hFind
      · have hFalse : p y = false := Bool.eq_false_iff.2 hp
        have hRest : ys.find? p = none := by
          simpa [List.find?, hFalse] using hFind
        have hx' : x = y ∨ x ∈ ys := by
          simpa [List.mem_cons] using hx
        rcases hx' with hxy | hxTail
        · cases hxy
          exact hFalse
        · exact list_find?_eq_none_all_false p hRest x hxTail

private theorem uint256_ofNat_ne_of_ne_of_lt
    {a b : Nat}
    (ha : a < EvmYul.UInt256.size)
    (hb : b < EvmYul.UInt256.size)
    (hne : a ≠ b) :
    EvmYul.UInt256.ofNat a ≠ EvmYul.UInt256.ofNat b := by
  intro h
  apply hne
  have hToNat := congrArg EvmYul.UInt256.toNat h
  rw [uint256_ofNat_toNat_of_lt a ha,
    uint256_ofNat_toNat_of_lt b hb] at hToNat
  exact hToNat

private theorem nativeSwitch_prefix_miss_of_selector_find
    (selector : Nat)
    (cases pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (state : EvmYul.Yul.State)
    (discrName : EvmYul.Identifier)
    (hCases : cases = pre ++ (tag, body) :: suffix)
    (hPrefix :
      ∀ entry, entry ∈ pre → (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) entry = false)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size) :
    ∀ tag' body', (tag', body') ∈ pre →
      state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
  intro tag' body' hmem hDiscrTag
  have hPrefixFalse := hPrefix (tag', body') hmem
  have hTagNe : tag' ≠ selector := by
    intro hEq
    have hTrue : (tag' == selector) = true := beq_iff_eq.mpr hEq
    have hFalse : (tag' == selector) = false := by
      simpa using hPrefixFalse
    rw [hTrue] at hFalse
    contradiction
  have hCaseMem : (tag', body') ∈ cases := by
    rw [hCases]
    simp [hmem]
  have hWordNe :
      EvmYul.UInt256.ofNat selector ≠ EvmYul.UInt256.ofNat tag' :=
    uint256_ofNat_ne_of_ne_of_lt hSelectorRange
      (hTagsRange tag' body' hCaseMem) (Ne.symm hTagNe)
  exact hWordNe (hDiscrSelector.symm.trans hDiscrTag)

/-- A selector lookup hit exposes the generated case list as a miss prefix,
    selected case, and suffix. This is the list-shape bridge consumed by the
    native lazy-switch execution lemmas. -/
theorem nativeSwitch_find_hit_split
    (selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = some (tag, body)) :
    ∃ pre suffix,
      cases = pre ++ (tag, body) :: suffix ∧
      tag = selector ∧
      ∀ entry, entry ∈ pre →
        (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
          entry.1 == selector) entry = false := by
  rcases list_find?_eq_some_split_false
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt => entry.1 == selector)
      hFind with
    ⟨pre, suffix, hSplit, hPrefix⟩
  have hSelected :
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) (tag, body) = true :=
    List.find?_some
      (p := fun entry : Nat × List EvmYul.Yul.Ast.Stmt =>
        entry.1 == selector) hFind
  have hTag : tag = selector := by
    exact beq_iff_eq.mp hSelected
  exact ⟨pre, suffix, hSplit, hTag, hPrefix⟩

/-- A selector lookup miss proves every generated case tag misses the native
    dispatcher discriminator when the discriminator contains that selector and
    all case tags are in the `UInt256` range. -/
theorem nativeSwitch_find_none_all_miss
    (selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (state : EvmYul.Yul.State)
    (discrName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    ∀ tag body, (tag, body) ∈ cases →
      state[discrName]! ≠ EvmYul.UInt256.ofNat tag := by
  intro tag body hmem hDiscrTag
  have hFalse :=
    list_find?_eq_none_all_false
      (fun entry : Nat × List EvmYul.Yul.Ast.Stmt => entry.1 == selector)
      hFind (tag, body) hmem
  have hTagNe : tag ≠ selector := by
    intro hEq
    have hTrue : (tag == selector) = true := beq_iff_eq.mpr hEq
    have hFalse' : (tag == selector) = false := by
      simpa using hFalse
    rw [hTrue] at hFalse'
    contradiction
  have hWordNe :
      EvmYul.UInt256.ofNat selector ≠ EvmYul.UInt256.ofNat tag :=
    uint256_ofNat_ne_of_ne_of_lt hSelectorRange
      (hTagsRange tag body hmem) (Ne.symm hTagNe)
  exact hWordNe (hDiscrSelector.symm.trans hDiscrTag)

/-- If no case tag matches and the matched flag is still clear, the generated
    native switch case chain skips every case body and leaves the state
    unchanged. -/
theorem exec_nativeSwitchCaseIfs_all_miss_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMiss :
      ∀ tag body, (tag, body) ∈ cases →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  induction cases generalizing fuel codeOverride state discrName matchedName with
  | nil =>
      simp [nativeSwitchCaseIfs, EvmYul.Yul.exec]
  | cons entry rest ih =>
      rcases entry with ⟨tag, body⟩
      have hHeadMiss : state[discrName]! ≠ EvmYul.UInt256.ofNat tag := by
        exact hMiss tag body (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMiss tag' body' (by simp [hmem])
      have hHead :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (nativeSwitchCaseIf discrName matchedName (tag, body))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_miss_fuel
            (fuel + rest.length) (Backends.lowerAssignNative matchedName (.lit 1) :: body)
            codeOverride state discrName matchedName tag hMatched hHeadMiss)
      have hTail :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName rest))
            codeOverride state = .ok state :=
        ih fuel codeOverride state discrName matchedName hMatched hRestMiss
      have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        (nativeSwitchCaseIfs discrName matchedName rest)
        codeOverride state state state hHead hTail
      simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hBlock

/-- Once a selected lowered switch body preserves the matched flag at one, every
    later generated case guard skips. -/
theorem exec_nativeSwitchCaseIfs_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  induction cases generalizing fuel codeOverride state discrName matchedName with
  | nil =>
      simp [nativeSwitchCaseIfs, EvmYul.Yul.exec]
  | cons entry rest ih =>
      rcases entry with ⟨tag, body⟩
      have hHead :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (nativeSwitchCaseIf discrName matchedName (tag, body))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_matched_fuel
            (fuel + rest.length) (Backends.lowerAssignNative matchedName (.lit 1) :: body)
            codeOverride state discrName matchedName tag hMatched)
      have hTail :
          EvmYul.Yul.exec (fuel + rest.length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName rest))
            codeOverride state = .ok state :=
        ih fuel codeOverride state discrName matchedName hMatched
      have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        (nativeSwitchCaseIfs discrName matchedName rest)
        codeOverride state state state hHead hTail
      simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hBlock

/-- Whole generated case-chain execution when the first remaining case is the
    selected case and suffix cases must skip after the selected body preserves
    the matched flag. -/
theorem exec_nativeSwitchCaseIfs_head_hit_fuel
    (fuel : Nat)
    (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + suffix.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName ((tag, body) :: suffix)))
      codeOverride state = .ok final := by
  have hHead :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        codeOverride state = .ok final := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_hit_marked_fuel
        (fuel + suffix.length) body codeOverride state final discrName
        matchedName tag hMatched hDiscr hBody)
  have hTail :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName suffix))
        codeOverride final = .ok final :=
    exec_nativeSwitchCaseIfs_matched_fuel fuel suffix codeOverride final
      discrName matchedName hFinalMatched
  have hBlock := exec_block_cons_ok (fuel + suffix.length + 9)
    (nativeSwitchCaseIf discrName matchedName (tag, body))
    (nativeSwitchCaseIfs discrName matchedName suffix)
    codeOverride state final final hHead hTail
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Whole generated case-chain execution when the first remaining case is the
    selected case and that selected body halts or errors before the suffix can
    run. -/
theorem exec_nativeSwitchCaseIfs_head_hit_error_fuel
    (fuel : Nat)
    (suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + suffix.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName ((tag, body) :: suffix)))
      codeOverride state = .error err := by
  have hHead :
      EvmYul.Yul.exec (fuel + suffix.length + 9)
        (nativeSwitchCaseIf discrName matchedName (tag, body))
        codeOverride state = .error err := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_hit_marked_error_fuel
        (fuel + suffix.length) body codeOverride state discrName matchedName
        tag err hMatched hDiscr hBody)
  have hBlock :=
    exec_block_cons_error (fuel + suffix.length + 9)
      (nativeSwitchCaseIf discrName matchedName (tag, body))
      (nativeSwitchCaseIfs discrName matchedName suffix)
      codeOverride state err hHead
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Cons a non-selected generated switch case onto an already-proved generated
    case-chain execution. -/
theorem exec_nativeSwitchCaseIfs_cons_miss_fuel
    (fuel : Nat)
    (rest : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (missTag : Nat)
    (missBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hHeadMiss : state[discrName]! ≠ EvmYul.UInt256.ofNat missTag)
    (hTail :
      EvmYul.Yul.exec (fuel + rest.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName rest))
        codeOverride state = .ok final) :
    EvmYul.Yul.exec (fuel + rest.length + 10)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName
          ((missTag, missBody) :: rest)))
      codeOverride state = .ok final := by
  have hHead :
      EvmYul.Yul.exec (fuel + rest.length + 9)
        (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
        codeOverride state = .ok state := by
    simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
      (exec_if_nativeSwitchGuardedMatch_miss_fuel
        (fuel + rest.length)
        (Backends.lowerAssignNative matchedName (.lit 1) :: missBody)
        codeOverride state discrName matchedName missTag hMatched hHeadMiss)
  have hBlock := exec_block_cons_ok (fuel + rest.length + 9)
    (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
    (nativeSwitchCaseIfs discrName matchedName rest)
    codeOverride state state final hHead hTail
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hBlock

/-- Whole generated case-chain execution for a miss prefix, selected case, and suffix. -/
theorem exec_nativeSwitchCaseIfs_prefix_hit_fuel
    (fuel : Nat)
    (pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMissPrefix : ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag')
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + (pre ++ (tag, body) :: suffix).length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName
        (pre ++ (tag, body) :: suffix)))
      codeOverride state = .ok final := by
  induction pre generalizing fuel with
  | nil =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_head_hit_fuel fuel suffix tag body codeOverride
          state final discrName matchedName hMatched hDiscr hBody hFinalMatched)
  | cons entry rest ih =>
      rcases entry with ⟨missTag, missBody⟩
      have hHeadMiss :
          state[discrName]! ≠ EvmYul.UInt256.ofNat missTag := by
        exact hMissPrefix missTag missBody (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMissPrefix tag' body' (by simp [hmem])
      have hTail :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName
              (rest ++ (tag, body) :: suffix)))
            codeOverride state = .ok final :=
        ih fuel hRestMiss hBody
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_cons_miss_fuel fuel
          (rest ++ (tag, body) :: suffix) missTag missBody codeOverride state
          final discrName matchedName hMatched hHeadMiss hTail)

/-- Whole generated case-chain execution for a miss prefix, selected case, and
    suffix when the selected case halts or errors. -/
theorem exec_nativeSwitchCaseIfs_prefix_hit_error_fuel
    (fuel : Nat)
    (pre suffix : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hMissPrefix : ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag')
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + (pre ++ (tag, body) :: suffix).length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName
        (pre ++ (tag, body) :: suffix)))
      codeOverride state = .error err := by
  induction pre generalizing fuel with
  | nil =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_nativeSwitchCaseIfs_head_hit_error_fuel fuel suffix tag body
          codeOverride state discrName matchedName err hMatched hDiscr hBody)
  | cons entry rest ih =>
      rcases entry with ⟨missTag, missBody⟩
      have hHeadMiss :
          state[discrName]! ≠ EvmYul.UInt256.ofNat missTag := by
        exact hMissPrefix missTag missBody (by simp)
      have hRestMiss :
          ∀ tag' body', (tag', body') ∈ rest →
            state[discrName]! ≠ EvmYul.UInt256.ofNat tag' := by
        intro tag' body' hmem
        exact hMissPrefix tag' body' (by simp [hmem])
      have hTail :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (.Block (nativeSwitchCaseIfs discrName matchedName
              (rest ++ (tag, body) :: suffix)))
            codeOverride state = .error err :=
        ih fuel hRestMiss hBody
      have hHead :
          EvmYul.Yul.exec
            (fuel + (rest ++ (tag, body) :: suffix).length + 9)
            (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
            codeOverride state = .ok state := by
        simpa [nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr] using
          (exec_if_nativeSwitchGuardedMatch_miss_fuel
            (fuel + (rest ++ (tag, body) :: suffix).length)
            (Backends.lowerAssignNative matchedName (.lit 1) :: missBody)
            codeOverride state discrName matchedName missTag hMatched hHeadMiss)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (exec_block_cons_tail_error
          (fuel + (rest ++ (tag, body) :: suffix).length + 9)
          (nativeSwitchCaseIf discrName matchedName (missTag, missBody))
          (nativeSwitchCaseIfs discrName matchedName
            (rest ++ (tag, body) :: suffix))
          codeOverride state state err hHead hTail)

/-- Whole generated case-chain execution for a selector lookup hit. This wraps
    `exec_nativeSwitchCaseIfs_prefix_hit_fuel` with the generated dispatcher
    lookup split, so callers only need the `find?` result and the selected body
    execution premise for the discovered suffix. -/
theorem exec_nativeSwitchCaseIfs_find_hit_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok final := by
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, hTag, hPrefix⟩
  subst tag
  have hMissPrefix :
      ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag' :=
    nativeSwitch_prefix_miss_of_selector_find selector cases pre suffix selector body
      state discrName hCases hPrefix hDiscrSelector hSelectorRange hTagsRange
  have hSelectedBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
        codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
        .ok final :=
    hBody pre suffix hCases
  have hExec :=
    exec_nativeSwitchCaseIfs_prefix_hit_fuel fuel pre suffix selector body
      codeOverride state final discrName matchedName hMatched hMissPrefix
      hDiscrSelector hSelectedBody hFinalMatched
  simpa [hCases, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Whole generated case-chain execution for a selector lookup hit whose
    selected body halts or errors. -/
theorem exec_nativeSwitchCaseIfs_find_hit_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .error err := by
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, hTag, hPrefix⟩
  subst tag
  have hMissPrefix :
      ∀ tag' body', (tag', body') ∈ pre →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag' :=
    nativeSwitch_prefix_miss_of_selector_find selector cases pre suffix selector body
      state discrName hCases hPrefix hDiscrSelector hSelectorRange hTagsRange
  have hSelectedBody :
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
        codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
        .error err :=
    hBody pre suffix hCases
  have hExec :=
    exec_nativeSwitchCaseIfs_prefix_hit_error_fuel fuel pre suffix selector body
      codeOverride state discrName matchedName err hMatched hMissPrefix
      hDiscrSelector hSelectedBody
  simpa [hCases, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hExec

/-- Selector-hit case-chain execution with the selected-body matched-flag
    preservation obligation factored into a reusable predicate.

This is the proof boundary needed by the full native dispatcher bridge: the
lowered case body may update storage, memory, and user variables, but it must
not clobber the generated lazy-switch matched flag after the lowering has set
it to one. -/
theorem exec_nativeSwitchCaseIfs_find_hit_preserved_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hMarked :
      (state.insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
        EvmYul.UInt256.ofNat 1)
    (hBody :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body)
            codeOverride (state.insert matchedName (EvmYul.UInt256.ofNat 1)) =
            .ok final)
    (hPreservesMatched :
      ∀ pre suffix,
        cases = pre ++ (tag, body) :: suffix →
          NativeBlockPreservesWord matchedName (EvmYul.UInt256.ofNat 1)
            body codeOverride) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok final := by
  apply exec_nativeSwitchCaseIfs_find_hit_fuel
      (fuel := fuel) (selector := selector) (cases := cases) (tag := tag)
      (body := body) (codeOverride := codeOverride) (state := state)
      (final := final) (discrName := discrName) (matchedName := matchedName)
      hFind hMatched hDiscrSelector hSelectorRange hTagsRange hBody
  rcases nativeSwitch_find_hit_split selector cases tag body hFind with
    ⟨pre, suffix, hCases, _hTag, _hPrefix⟩
  exact hPreservesMatched pre suffix hCases (fuel + suffix.length + 7)
    (state.insert matchedName (EvmYul.UInt256.ofNat 1)) final hMarked
    (hBody pre suffix hCases)

/-- Whole generated case-chain skip for a selector lookup miss. This packages
    the `find? = none` selector fact into the all-cases-miss premise expected by
    the lazy native switch executor. -/
theorem exec_nativeSwitchCaseIfs_find_none_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block (nativeSwitchCaseIfs discrName matchedName cases))
      codeOverride state = .ok state := by
  have hMiss :
      ∀ tag body, (tag, body) ∈ cases →
        state[discrName]! ≠ EvmYul.UInt256.ofNat tag :=
    nativeSwitch_find_none_all_miss selector cases state discrName hFind
      hDiscrSelector hSelectorRange hTagsRange
  exact exec_nativeSwitchCaseIfs_all_miss_fuel fuel cases codeOverride state
    discrName matchedName hMatched hMiss
/-- Non-empty generated default block execution when no case matched. -/
theorem exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 6) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 8)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  cases defaultBody with
  | nil => contradiction
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .ok final := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_unmatched_fuel fuel
            (stmt :: rest) codeOverride state final matchedName hMatched hBody)
      have hTail :
          EvmYul.Yul.exec (fuel + 7) (.Block [])
            codeOverride final = .ok final := by
        simp [EvmYul.Yul.exec]
      exact exec_block_cons_ok (fuel + 7)
        (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
        [] codeOverride state final final hHead hTail

/-- Non-empty generated default block execution when no case matched and the
    default body halts or errors. This is the selector-miss path used by a
    default `revert(0, 0)` body. -/
theorem exec_nativeSwitchDefaultIf_unmatched_nonempty_error_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 6) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 8)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  cases defaultBody with
  | nil => contradiction
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .error err := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_unmatched_error_fuel fuel
            (stmt :: rest) codeOverride state matchedName err hMatched hBody)
      exact exec_block_cons_error (fuel + 7)
        (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
        [] codeOverride state err hHead

/-- After a selected case preserves the matched flag at one, the optional
    generated default block skips. Empty defaults also skip because no default
    statement is emitted. -/
theorem exec_nativeSwitchDefaultIf_matched_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec
      (fuel + (nativeSwitchDefaultIf matchedName defaultBody).length + 7)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok state := by
  cases defaultBody with
  | nil =>
      simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  | cons stmt rest =>
      have hHead :
          EvmYul.Yul.exec (fuel + 7)
            (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
            codeOverride state = .ok state := by
        simpa [nativeSwitchDefaultGuardExpr] using
          (exec_if_nativeSwitchDefaultGuard_matched_fuel fuel
            (stmt :: rest) codeOverride state matchedName hMatched)
      have hTail :
          EvmYul.Yul.exec (fuel + 7) (.Block [])
            codeOverride state = .ok state := by
        simp [EvmYul.Yul.exec]
      simpa [nativeSwitchDefaultIf] using
        (exec_block_cons_ok (fuel + 7)
          (.If (nativeSwitchDefaultGuardExpr matchedName) (stmt :: rest))
          [] codeOverride state state state hHead hTail)

/-- Default-tail skip at the fuel level left after a generated case chain. -/
theorem exec_nativeSwitchDefaultIf_matched_caseTail_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok state := by
  cases defaultBody with
  | nil =>
      simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  | cons stmt rest =>
      simpa [nativeSwitchDefaultIf, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (exec_nativeSwitchDefaultIf_matched_fuel (fuel + 1)
          (stmt :: rest) codeOverride state matchedName hMatched)

/-- Non-empty default-tail execution at the fuel level left after all generated
    cases miss. -/
theorem exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exec_nativeSwitchDefaultIf_unmatched_nonempty_fuel (fuel + 1)
      defaultBody codeOverride state final matchedName hMatched hBody hNonempty)

/-- Non-empty default-tail error execution at the fuel level left after all
    generated cases miss. -/
theorem exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_error_fuel
    (fuel : Nat)
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + 9)
      (.Block (nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exec_nativeSwitchDefaultIf_unmatched_nonempty_error_fuel (fuel + 1)
      defaultBody codeOverride state matchedName err hMatched hBody hNonempty)

/-- Compose a generated case chain with its optional default when the case chain
    has already set and preserved the matched flag. -/
theorem exec_nativeSwitchCaseIfs_with_default_matched_fuel
    (fuel : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok final)
    (hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride final = .ok final :=
    exec_nativeSwitchDefaultIf_matched_caseTail_fuel fuel defaultBody
      codeOverride final matchedName hFinalMatched
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using exec_block_append_ok fuel 9
      (nativeSwitchCaseIfs discrName matchedName cases)
      (nativeSwitchDefaultIf matchedName defaultBody)
      codeOverride state final final
      (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hCases)
      hDefault

/-- Selector-hit execution for the generated case chain followed by the
    generated optional default statement list. The selected body must preserve
    the matched flag so the default guard and suffix cases skip. -/
theorem exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hMarked : (state.insert matchedName (EvmYul.UInt256.ofNat 1))[matchedName]! =
      EvmYul.UInt256.ofNat 1)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hPreservesMatched : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      NativeBlockPreservesWord matchedName (EvmYul.UInt256.ofNat 1) body codeOverride) :
    EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
      (nativeSwitchCaseIfs discrName matchedName cases ++ nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok final :=
    exec_nativeSwitchCaseIfs_find_hit_preserved_fuel fuel selector cases tag
      body codeOverride state final discrName matchedName hFind hMatched
      hDiscrSelector hSelectorRange hTagsRange hMarked hBody hPreservesMatched
  have hFinalMatched : final[matchedName]! = EvmYul.UInt256.ofNat 1 := by
    rcases nativeSwitch_find_hit_split selector cases tag body hFind with
      ⟨pre, suffix, hCasesEq, _hTag, _hPrefix⟩
    exact hPreservesMatched pre suffix hCasesEq
      (fuel + suffix.length + 7)
      (state.insert matchedName (EvmYul.UInt256.ofNat 1)) final hMarked
      (hBody pre suffix hCasesEq)
  exact exec_nativeSwitchCaseIfs_with_default_matched_fuel fuel cases
    defaultBody codeOverride state final discrName matchedName hCases
    hFinalMatched

/-- Selector-hit execution for the generated case chain followed by the
    generated optional default statement list when the selected case halts or
    errors. The default never runs because block execution stops at the
    selected-case exception. -/
theorem exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec (fuel + suffix.length + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
      (nativeSwitchCaseIfs discrName matchedName cases ++ nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .error err :=
    exec_nativeSwitchCaseIfs_find_hit_error_fuel fuel selector cases tag body
      codeOverride state discrName matchedName err hFind hMatched
      hDiscrSelector hSelectorRange hTagsRange hBody
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_prefix_error fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state err
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases))

/-- Selector-miss execution for the generated case chain followed by a
    non-empty generated default block. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .ok final := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride state = .ok final :=
    exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_fuel fuel
      defaultBody codeOverride state final matchedName hMatched hDefaultBody
      hNonempty
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_ok fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state state final
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

/-- Selector-miss execution for the generated case chain followed by a
    non-empty generated default block that halts or errors. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_error_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block defaultBody) codeOverride state =
        .error err)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName defaultBody))
      codeOverride state = .error err := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9) (.Block
        (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9) (.Block
        (nativeSwitchDefaultIf matchedName defaultBody))
        codeOverride state = .error err :=
    exec_nativeSwitchDefaultIf_unmatched_caseTail_nonempty_error_fuel fuel
      defaultBody codeOverride state matchedName err hMatched hDefaultBody
      hNonempty
  simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using
      (exec_block_append_error fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName defaultBody)
        codeOverride state state err
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

/-- Guarded selector-miss execution for the generated lazy switch when the
    default body is the compiler's `revert(0, 0)` statement. This discharges the
    default-body premise in the generic selector-miss theorem with the actual
    native `REVERT` primitive path. -/
theorem exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName [nativeRevertZeroZeroStmt]))
      codeOverride state = .error EvmYul.Yul.Exception.Revert := by
  have hDefaultBody :
      EvmYul.Yul.exec (fuel + 7) (.Block [nativeRevertZeroZeroStmt])
        codeOverride state = .error EvmYul.Yul.Exception.Revert := by
    exact exec_block_cons_error (fuel + 6) nativeRevertZeroZeroStmt []
      codeOverride state EvmYul.Yul.Exception.Revert
      (exec_revert_zero_zero_error fuel state codeOverride)
  exact exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_error_fuel
    fuel selector cases [nativeRevertZeroZeroStmt] codeOverride state
    discrName matchedName EvmYul.Yul.Exception.Revert hFind hMatched
    hDiscrSelector hSelectorRange hTagsRange hDefaultBody (by simp)

/-- Selector-miss execution for the generated case chain when no default is
    emitted. -/
theorem exec_nativeSwitchCaseIfs_find_none_without_default_fuel
    (fuel selector : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (hFind :
      cases.find? (fun entry => entry.1 == selector) = none)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscrSelector : state[discrName]! = EvmYul.UInt256.ofNat selector)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 9)
      (.Block
        (nativeSwitchCaseIfs discrName matchedName cases ++
          nativeSwitchDefaultIf matchedName []))
      codeOverride state = .ok state := by
  have hCases :
      EvmYul.Yul.exec (fuel + cases.length + 9)
        (.Block (nativeSwitchCaseIfs discrName matchedName cases))
        codeOverride state = .ok state :=
    exec_nativeSwitchCaseIfs_find_none_fuel fuel selector cases codeOverride
      state discrName matchedName hFind hMatched hDiscrSelector hSelectorRange
      hTagsRange
  have hDefault :
      EvmYul.Yul.exec (fuel + 9)
        (.Block (nativeSwitchDefaultIf matchedName []))
        codeOverride state = .ok state := by
    simp [nativeSwitchDefaultIf, EvmYul.Yul.exec]
  simpa [nativeSwitchCaseIfs, nativeSwitchDefaultIf, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using
      (exec_block_append_ok fuel 9
        (nativeSwitchCaseIfs discrName matchedName cases)
        (nativeSwitchDefaultIf matchedName [])
        codeOverride state state state
        (by simpa [nativeSwitchCaseIfs, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hCases)
        hDefault)

theorem exec_nativeSwitchPrefix_then_tail_fuel
    (fuel : Nat)
    (tail : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (final : EvmYul.Yul.State)
    (hTail :
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          discrName matchedName) =
        .ok final) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName ++ tail))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hPrefix :
      EvmYul.Yul.exec (fuel + 12)
        (.Block (nativeSwitchPrefixStmts discrName matchedName))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .ok prefixState := by
    simpa [prefixState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (exec_nativeSwitchPrefix_selector_initialState_ok_fuel fuel
        contract tx storage observableSlots discrName matchedName)
  exact exec_block_append_ok (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName) tail
    (some contract)
    (nativeSwitchInitialOkState contract tx storage observableSlots)
    prefixState final
    (by simpa [nativeSwitchPrefixStmts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hPrefix)
    (by simpa [prefixState] using hTail)

theorem exec_nativeSwitchPrefix_then_tail_error_fuel
    (fuel : Nat)
    (tail : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          discrName matchedName) =
        .error err) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName ++ tail))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error err := by
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hPrefix :
      EvmYul.Yul.exec (fuel + 12)
        (.Block (nativeSwitchPrefixStmts discrName matchedName))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .ok prefixState := by
    simpa [prefixState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (exec_nativeSwitchPrefix_selector_initialState_ok_fuel fuel
        contract tx storage observableSlots discrName matchedName)
  exact exec_block_append_error (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName) tail
    (some contract)
    (nativeSwitchInitialOkState contract tx storage observableSlots)
    prefixState err
    (by simpa [nativeSwitchPrefixStmts, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hPrefix)
    (by simpa [prefixState] using hTail)

theorem exec_nativeSwitchTail_find_hit_preserved_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .ok final)
    (hPreservesMatched : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
        (EvmYul.UInt256.ofNat 1) body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .ok final := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract)
      prefixState final discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_marked contract tx storage
          observableSlots discrName matchedName))
      (by intro pre suffix hCases; simpa [nativeSwitchMarkedPrefixStateForId,
        nativeSwitchPrefixStateForId, prefixState, discrName, matchedName]
        using hBody pre suffix hCases)
      (by intro pre suffix hCases; simpa [matchedName] using
        hPreservesMatched pre suffix hCases)
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

/-- Selector-hit switch-tail execution deriving matched-flag preservation from generated freshness. -/
theorem exec_nativeSwitchTail_find_hit_fresh_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .ok final := by
  apply exec_nativeSwitchTail_find_hit_preserved_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final hSelector
    hFind hSelectorRange hTagsRange hBody
  intro pre suffix _hCases
  exact NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    switchId selector tag body defaultBody cases (EvmYul.UInt256.ofNat 1)
    (some contract) hFresh hFind hStmtPreserves

theorem exec_nativeSwitchTail_find_hit_error_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchMarkedPrefixStateForId contract tx storage observableSlots switchId) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage observableSlots switchId) =
    .error err := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract)
      prefixState discrName matchedName err hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by intro pre suffix hCases; simpa [nativeSwitchMarkedPrefixStateForId,
        nativeSwitchPrefixStateForId, prefixState, discrName, matchedName]
        using hBody pre suffix hCases)
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_nativeSwitchTail_find_none_with_default_nonempty_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec ((fuel + 1) + 7) (.Block defaultBody) (some contract)
        (nativeSwitchPrefixStateForId contract tx storage observableSlots
          switchId) = .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases defaultBody))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .ok final := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_with_default_nonempty_fuel
      (fuel + 1) selector cases defaultBody (some contract)
      prefixState final discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
      (by simpa [nativeSwitchPrefixStateForId, prefixState, discrName,
        matchedName] using hDefaultBody)
      hNonempty
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_nativeSwitchTail_find_none_without_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases []))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .ok (nativeSwitchPrefixStateForId contract tx storage observableSlots
      switchId) := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_without_default_fuel
      (fuel + 1) selector cases (some contract)
      prefixState discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

/-- Selector-miss execution for a lowered switch tail with the compiler's
    generated `revert(0, 0)` default. This carries the guarded miss proof from
    the case-chain level to the switch-tail shape used by lowered dispatchers. -/
theorem exec_nativeSwitchTail_find_none_with_revert_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 10)
      (.Block (nativeSwitchTailStmts switchId cases [nativeRevertZeroZeroStmt]))
      (some contract) (nativeSwitchPrefixStateForId contract tx storage
        observableSlots switchId) =
    .error EvmYul.Yul.Exception.Revert := by
  let discrName : EvmYul.Identifier := Backends.nativeSwitchDiscrTempName switchId
  let matchedName : EvmYul.Identifier := Backends.nativeSwitchMatchedTempName switchId
  let prefixState :=
    nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName
  have hCasesDefault :=
    exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
      (fuel + 1) selector cases (some contract)
      prefixState discrName matchedName hFind
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_matched contract tx storage
          observableSlots discrName matchedName))
      (by simpa [prefixState, discrName, matchedName] using
        (nativeSwitchPrefixFinalState_discr contract tx storage observableSlots
          discrName matchedName selector
          (nativeSwitchDiscrTempName_ne_matchedTempName switchId) hSelector))
      hSelectorRange hTagsRange
  simpa [nativeSwitchTailStmts, nativeSwitchPrefixStateForId, prefixState,
    discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using hCasesDefault

theorem exec_lowerNativeSwitchBlock_selector_find_hit_preserved_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hPreservesMatched : ∀ pre suffix,
      cases = pre ++ (tag, body) :: suffix →
        NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
          (EvmYul.UInt256.ofNat 1) body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_hit_preserved_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final
    hSelector hFind hSelectorRange hTagsRange hBody hPreservesMatched

theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_hit_fresh_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots final hSelector
    hFind hSelectorRange hTagsRange hFresh hBody hStmtPreserves

theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (tag : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error err := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_error_fuel
  exact exec_nativeSwitchTail_find_hit_error_fuel fuel selector switchId tag
    cases defaultBody body contract tx storage observableSlots err
    hSelector hFind hSelectorRange hTagsRange hBody

theorem exec_lowerNativeSwitchBlock_selector_find_none_with_default_nonempty_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size)
    (hDefaultBody :
      EvmYul.Yul.exec ((fuel + 1) + 7) (.Block defaultBody) (some contract)
        (nativeSwitchPrefixFinalState contract tx storage observableSlots
          (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId)) =
        .ok final)
    (hNonempty : defaultBody ≠ []) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok final := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_none_with_default_nonempty_fuel fuel
    selector switchId cases defaultBody contract tx storage observableSlots
    final hSelector hFind hSelectorRange hTagsRange hDefaultBody hNonempty

/-- Guarded selector-miss execution for a fully lowered native switch block
    whose generated default is `revert(0, 0)`. This discharges the generic
    default-body premise with the actual native `REVERT` primitive path at the
    same lowered-block boundary used by dispatcher proofs. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
          [nativeRevertZeroZeroStmt])
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .error EvmYul.Yul.Exception.Revert := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_error_fuel
  exact exec_nativeSwitchTail_find_none_with_revert_default_fuel fuel selector
    switchId cases contract tx storage observableSlots hSelector hFind
    hSelectorRange hTagsRange

/-- Store-parametric prefix-then-tail-error glue for `lowerNativeSwitchBlock`.
    Given the tail body errors on the post-prefix state extended over an
    arbitrary preceding native varstore, the full lowered switch block errors
    on the matching state with that store. Together with the store-parametric
    prefix lemma `exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel`,
    this lifts switch-block error proofs to states already carrying additional
    bindings (e.g. the buildSwitch wrapper's `__has_selector := 1`). -/
theorem exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (((.Ok (initialState contract tx storage observableSlots).sharedState store
                : EvmYul.Yul.State).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)) =
        .error err) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let prefixState : EvmYul.Yul.State :=
    (initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
      matchedName (EvmYul.UInt256.ofNat 0)
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_error (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState err
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState] using hTail

def nativeSwitchStoreInitialState
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  .Ok (initialState contract tx storage observableSlots).sharedState store

def nativeSwitchStorePrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  ((nativeSwitchStoreInitialState contract tx storage observableSlots store).insert
      (Backends.nativeSwitchDiscrTempName switchId)
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 0)

def nativeSwitchStoreMarkedPrefixStateForId
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (switchId : Nat) (store : EvmYul.Yul.VarStore) : EvmYul.Yul.State :=
  (nativeSwitchStorePrefixStateForId contract tx storage observableSlots
    switchId store).insert
    (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)

def nativeSwitchHasSelectorStore : EvmYul.Yul.VarStore :=
  (∅ : EvmYul.Yul.VarStore).insert "__has_selector" (EvmYul.UInt256.ofNat 1)

def nativeSwitchHasSelectorInitialState
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) : EvmYul.Yul.State :=
  nativeSwitchStoreInitialState contract tx storage observableSlots
    nativeSwitchHasSelectorStore

theorem nativeSwitchInitialOkState_insert_hasSelector_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) :
    (nativeSwitchInitialOkState contract tx storage observableSlots).insert
        "__has_selector" (EvmYul.UInt256.ofNat 1) =
      nativeSwitchHasSelectorInitialState contract tx storage observableSlots := by
  simp [nativeSwitchInitialOkState, nativeSwitchHasSelectorInitialState,
    nativeSwitchStoreInitialState, nativeSwitchHasSelectorStore,
    EvmYul.Yul.State.insert]

/-- `matched := 0` lookup on the post-prefix state with arbitrary store. -/
theorem nativeSwitchPrefixStoreState_matched_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (discrValue : EvmYul.Literal) :
    (((.Ok (initialState contract tx storage observableSlots).sharedState store
              : EvmYul.Yul.State).insert discrName discrValue).insert
        matchedName (EvmYul.UInt256.ofNat 0))[matchedName]! =
      EvmYul.UInt256.ofNat 0 := by
  simp [EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

/-- `discr := selector` lookup on the post-prefix state with arbitrary store. -/
theorem nativeSwitchPrefixStoreState_discr_eq
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier)
    (selector : Nat) (hne : discrName ≠ matchedName)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus) :
    (((.Ok (initialState contract tx storage observableSlots).sharedState store
              : EvmYul.Yul.State).insert discrName
          (EvmYul.UInt256.ofNat
            (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
        matchedName (EvmYul.UInt256.ofNat 0))[discrName]! =
      EvmYul.UInt256.ofNat selector := by
  rw [hSelector]
  simp [EvmYul.Yul.State.insert, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]
  rw [Finmap.lookup_insert_of_ne]
  · rw [Finmap.lookup_insert]; simp
  · exact hne

/-- Store-parametric prefix-then-tail-ok glue for `lowerNativeSwitchBlock`.
    This is the success dual of
    `exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel`: it lifts switch
    tail proofs to states already carrying additional bindings while preserving
    the final state returned by the tail. -/
theorem exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel
    (fuel switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hTail :
      EvmYul.Yul.exec (fuel + 10)
        (.Block (nativeSwitchTailStmts switchId cases defaultBody))
        (some contract)
        (nativeSwitchStorePrefixStateForId contract tx storage observableSlots
          switchId store) = .ok final) :
    EvmYul.Yul.exec (fuel + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  let initState :=
    nativeSwitchStoreInitialState contract tx storage observableSlots store
  let prefixState :=
    nativeSwitchStorePrefixStateForId contract tx storage observableSlots
      switchId store
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_block_append_ok (fuel + 10) 0
    (nativeSwitchPrefixStmts discrName matchedName)
    (nativeSwitchTailStmts switchId cases defaultBody)
    (some contract) initState prefixState final
  · simpa [nativeSwitchPrefixStmts, prefixState, initState, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, nativeSwitchStorePrefixStateForId,
      nativeSwitchStoreInitialState, discrName, matchedName] using
      exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
        fuel contract tx storage observableSlots store discrName matchedName
  · simpa [prefixState, initState] using hTail

/-- Store-parametric guarded selector-hit execution for the lowered switch
    block. This is the success dual of
    `exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel`, retaining
    the matched-flag preservation premise needed to skip the generated default
    after a successful selected body. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel
    (fuel selector switchId tag : Nat) (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt) (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) (store : EvmYul.Yul.VarStore) (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx storage observableSlots switchId store) = .ok final)
    (hPreservesMatched : ∀ pre suffix,
      cases = pre ++ (tag, body) :: suffix →
        NativeBlockPreservesWord (Backends.nativeSwitchMatchedTempName switchId) (EvmYul.UInt256.ofNat 1)
          body (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody) (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_preserved_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract) _
      final discrName matchedName hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage
        observableSlots store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage
        observableSlots store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange
      (by
        simp [EvmYul.Yul.State.insert, GetElem?.getElem!,
          decidableGetElem?, GetElem.getElem, EvmYul.Yul.State.store,
          EvmYul.Yul.State.lookup!])
      hBody
      (by intro pre suffix hCases; simpa [matchedName] using
        hPreservesMatched pre suffix hCases)
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_ok_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store final (by
      simpa [nativeSwitchTailStmts, discrName, matchedName, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
        nativeSwitchStoreMarkedPrefixStateForId] using hCases)

/-- Store-parametric selector-hit success derived from generated native switch
    freshness. This removes the explicit matched-flag preservation premise for
    selected bodies when the generated freshness predicate proves the body does
    not write the matched temp. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId store) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (nativeSwitchStoreInitialState contract tx storage observableSlots store) =
    .ok final := by
  apply exec_lowerNativeSwitchBlock_selector_find_hit_preserved_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots store final hSelector hFind hSelectorRange hTagsRange hBody
  intro pre suffix _hCases
  exact NativeBlockPreservesWord_of_nativeSwitchFresh_find_hit_matched
    switchId selector tag body defaultBody cases (EvmYul.UInt256.ofNat 1)
    (some contract) hFresh hFind hStmtPreserves

/-- Store-parametric guarded selector-miss execution for the lowered switch
    block whose default is `revert(0, 0)`. Lifts the empty-store version to
    states already carrying additional bindings (e.g. `__has_selector := 1`). -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
          [nativeRevertZeroZeroStmt])
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error EvmYul.Yul.Exception.Revert := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_none_with_revert_default_fuel
      (fuel + 1) selector cases (some contract) _ discrName matchedName hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage observableSlots
        store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage observableSlots
        store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel + cases.length) switchId cases [nativeRevertZeroZeroStmt]
    contract tx storage observableSlots store EvmYul.Yul.Exception.Revert
    (by simpa [nativeSwitchTailStmts, discrName, matchedName,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases)

/-- Store-parametric guarded selector-hit execution for the lowered switch
    block. Hit-case dual of `_find_none_with_revert_default_store_fuel`. -/
theorem exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat) (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        ((((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).insert
              (Backends.nativeSwitchDiscrTempName switchId)
              (EvmYul.UInt256.ofNat
                (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 0)).insert
            (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody)
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .error err := by
  let discrName := Backends.nativeSwitchDiscrTempName switchId
  let matchedName := Backends.nativeSwitchMatchedTempName switchId
  have hne := nativeSwitchDiscrTempName_ne_matchedTempName switchId
  have hCases :=
    exec_nativeSwitchCaseIfs_find_hit_with_default_error_fuel
      (fuel + 1) selector cases defaultBody tag body (some contract) _
      discrName matchedName err hFind
      (nativeSwitchPrefixStoreState_matched_eq contract tx storage
        observableSlots store discrName matchedName _)
      (nativeSwitchPrefixStoreState_discr_eq contract tx storage
        observableSlots store discrName matchedName selector hne hSelector)
      hSelectorRange hTagsRange hBody
  exact exec_lowerNativeSwitchBlock_storePrefix_tail_error_fuel
    (fuel + cases.length) switchId cases defaultBody contract tx storage
    observableSlots store err
    (by simpa [nativeSwitchTailStmts, discrName, matchedName,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hCases)

/-- Bridge-shape selector-miss endpoint on the post-`__has_selector := 1`
    state, yielding `.error Revert`. -/
theorem exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases
        [nativeRevertZeroZeroStmt]])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error EvmYul.Yul.Exception.Revert := by
  have hEndpoint :=
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_store_fuel
      fuel selector switchId cases contract tx storage observableSlots
      ((∅ : EvmYul.Yul.VarStore).insert "__has_selector" (EvmYul.UInt256.ofNat 1))
      hSelector hFind hSelectorRange hTagsRange
  have hStateEq :
      (nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1) =
        .Ok (initialState contract tx storage observableSlots).sharedState
          ((∅ : EvmYul.Yul.VarStore).insert "__has_selector"
            (EvmYul.UInt256.ofNat 1)) := by
    simp [nativeSwitchInitialOkState, EvmYul.Yul.State.insert]
  rw [hStateEq]
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [hFuelEq]
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _
    EvmYul.Yul.Exception.Revert hEndpoint

/-- Bridge-shape selector-hit endpoint on the post-`__has_selector := 1`
    state, yielding `.error err`. Hit-case dual of
    `exec_block_lowerNativeSwitchBlock_revert_default_hasSelectorState_error`. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract) (nativeSwitchStoreMarkedPrefixStateForId contract tx
          storage observableSlots switchId nativeSwitchHasSelectorStore) =
        .error err) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .error err := by
  have hEndpoint := exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
    fuel selector switchId tag cases defaultBody body contract tx storage
    observableSlots nativeSwitchHasSelectorStore err hSelector hFind
    hSelectorRange hTagsRange (by
      intro pre suffix hCases
      simpa [nativeSwitchStoreMarkedPrefixStateForId,
        nativeSwitchStorePrefixStateForId, nativeSwitchStoreInitialState,
        nativeSwitchHasSelectorStore] using hBody pre suffix hCases)
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_error (fuel + cases.length + 12) _ [] _ _ err hEndpoint

/-- Bridge-shape selector-hit endpoint on the post-`__has_selector := 1`
    state, yielding the selected body's successful final state. This is the
    success dual of
    `exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_error`
    and derives the default-skip preservation premise from generated native
    switch freshness. -/
theorem exec_block_lowerNativeSwitchBlock_selector_find_hit_hasSelectorState_ok_fresh
    (fuel selector switchId tag : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody body : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (final : EvmYul.Yul.State)
    (hSelector : selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = some (tag, body))
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange : ∀ tag' body', (tag', body') ∈ cases → tag' < EvmYul.UInt256.size)
    (hFresh :
      Backends.nativeSwitchTempsFreshForNativeBodies switchId cases defaultBody)
    (hBody : ∀ pre suffix, cases = pre ++ (tag, body) :: suffix →
      EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7) (.Block body)
        (some contract)
        (nativeSwitchStoreMarkedPrefixStateForId contract tx storage
          observableSlots switchId nativeSwitchHasSelectorStore) = .ok final)
    (hStmtPreserves :
      ∀ stmt, stmt ∈ body →
        Backends.nativeSwitchMatchedTempName switchId ∉
          Backends.nativeStmtWriteNames stmt →
          NativeStmtPreservesWord (Backends.nativeSwitchMatchedTempName switchId)
            (EvmYul.UInt256.ofNat 1) stmt (some contract)) :
    EvmYul.Yul.exec (fuel + cases.length + 13)
      (.Block [Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases defaultBody])
      (some contract)
      ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          "__has_selector" (EvmYul.UInt256.ofNat 1)) =
      .ok final := by
  have hEndpoint :=
    exec_lowerNativeSwitchBlock_selector_find_hit_fresh_store_fuel
      fuel selector switchId tag cases defaultBody body contract tx storage
      observableSlots nativeSwitchHasSelectorStore final hSelector hFind
      hSelectorRange hTagsRange hFresh hBody hStmtPreserves
  have hFuelEq : fuel + cases.length + 13 = (fuel + cases.length + 12).succ := by
    omega
  rw [nativeSwitchInitialOkState_insert_hasSelector_eq, hFuelEq]
  exact exec_block_cons_ok (fuel + cases.length + 12) _ [] _ _ final final
    hEndpoint (by simp [EvmYul.Yul.exec])

theorem exec_lowerNativeSwitchBlock_selector_find_none_without_default_fuel
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
      (Backends.lowerNativeSwitchBlock
        Compiler.Proofs.YulGeneration.selectorExpr switchId cases [])
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      (Backends.nativeSwitchDiscrTempName switchId)
      (Backends.nativeSwitchMatchedTempName switchId)) := by
  rw [lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts]
  apply exec_nativeSwitchPrefix_then_tail_fuel
  exact exec_nativeSwitchTail_find_none_without_default_fuel fuel selector
    switchId cases contract tx storage observableSlots hSelector hFind
    hSelectorRange hTagsRange

@[simp] theorem initialState_unbridgedEnvironmentDefaults
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
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
    `IRStorageSlot → IRStorageWord` storage view. -/
def projectStorageFromState (tx : YulTransaction) (state : EvmYul.Yul.State) :
    IRStorageSlot → IRStorageWord :=
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
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = value := by
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
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0 := by
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
    projectStorageFromState tx state (IRStorageSlot.ofNat slot) = 0 := by
  simp [projectStorageFromState, extractStorage, hAccount]

/-- Native initial-state storage materialization agrees with Verity storage on
    every explicit observable slot. Slots and values are interpreted in the
    EVM word domain, so the result is modulo `UInt256.size`. -/
theorem initialState_observableStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  simp only [projectStorageFromState, extractStorage, initialState,
    EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  have h := storageLookup_projectStorage storage observableSlots slot hSlot hRange
  unfold storageLookup at h
  exact h

/-- Native `sload` from an initially materialized observable slot returns the
    exact EVM word projected from Verity storage. The range hypothesis keeps
    the slot key word-canonical, so the finite native storage map cannot alias
    another observed slot. -/
theorem initialState_sload_observableSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    (EvmYul.State.sload
      (initialState contract tx storage observableSlots).toState
      (natToUInt256 slot)).2 =
      storage (IRStorageSlot.ofNat slot) := by
  have hFindStorage :
      (projectStorage storage observableSlots).find? (natToUInt256 slot) =
        some (storage (IRStorageSlot.ofNat slot)) := by
    simpa [projectStorage, IRStorageWord.toUInt256] using
      foldl_insert_find storage observableSlots slot hSlot hRange
        (Batteries.RBMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  change (Batteries.RBMap.find? (projectStorage storage observableSlots)
      (natToUInt256 slot)).getD ⟨0⟩ = storage (IRStorageSlot.ofNat slot)
  rw [hFindStorage]
  rfl

/-- Native `sload` from an initially materialized slot returns the exact bounded
    IR storage word. This is the range-free version used after IR storage keys
    moved to `IRStorageSlot`: Nat aliases modulo 2^256 carry the same bounded
    key and therefore the same projected value. -/
theorem initialState_sload_materializedSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    (EvmYul.State.sload
      (initialState contract tx storage slots).toState
      (natToUInt256 slot)).2 =
      storage (IRStorageSlot.ofNat slot) := by
  have hFindStorage :
      (projectStorage storage slots).find? (natToUInt256 slot) =
        some (storage (IRStorageSlot.ofNat slot)) := by
    simpa [projectStorage, IRStorageWord.toUInt256] using
      foldl_insert_find_projected storage slots slot hSlot
        (Batteries.RBMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  change (Batteries.RBMap.find? (projectStorage storage slots)
      (natToUInt256 slot)).getD ⟨0⟩ = storage (IRStorageSlot.ofNat slot)
  rw [hFindStorage]
  rfl

/-- Projected storage is unchanged by the generated retrieve core
    `sload(0); mstore(0, _); return(0, 32)`. The only `sload` state effect is
    recording an accessed storage key, and `mstore`/`return` update only the
    machine-state fields used for returndata. -/
theorem projectStorageFromState_retrieveHit_initialState_materialized
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (slots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ slots) :
    let shared := (initialState contract tx storage slots).sharedState
    let p := shared.sload (EvmYul.UInt256.ofNat 0)
    let shared1 : EvmYul.SharedState .Yul := { shared with toState := p.1 }
    let shared2 : EvmYul.SharedState .Yul :=
      { shared1 with
        toMachineState :=
          shared1.toMachineState.mstore (EvmYul.UInt256.ofNat 0) p.2 }
    let shared3 : EvmYul.SharedState .Yul :=
      { shared2 with
        toMachineState :=
          shared2.toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32) }
    projectStorageFromState tx (EvmYul.Yul.State.Ok shared3 store)
        (IRStorageSlot.ofNat slot) =
      storage (IRStorageSlot.ofNat slot) := by
  intro shared p shared1 shared2 shared3
  have hAccountMap :
      shared3.accountMap =
        (initialState contract tx storage slots).sharedState.accountMap := by
    simp [shared3, shared2, shared1, p, shared, EvmYul.State.sload,
      EvmYul.State.addAccessedStorageKey, EvmYul.Substate.addAccessedStorageKey]
  simp only [projectStorageFromState, extractStorage,
    EvmYul.Yul.State.sharedState, hAccountMap, initialState, YulState.initial,
    toSharedState]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  have h := storageLookup_projectStorage_projected storage slots slot hSlot
  unfold storageLookup at h
  exact h

/-- Native `sload` from an initially omitted materialized slot returns the EVM
    zero word. The range hypotheses rule out modular aliasing between the omitted
    slot and any materialized storage key. -/
theorem initialState_sload_omittedSlot_value
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    (EvmYul.State.sload
      (initialState contract tx storage observableSlots).toState
      (natToUInt256 slot)).2 =
      natToUInt256 0 := by
  have hFindStorage :
      (projectStorage storage observableSlots).find? (natToUInt256 slot) = none := by
    simpa [projectStorage] using
      foldl_insert_find_not_mem storage observableSlots slot hNotSlot hRange
        hSlotRange (Batteries.RBMap.empty : EvmYul.Storage)
  simp only [EvmYul.State.sload, EvmYul.State.lookupAccount,
    EvmYul.Yul.State.toState, initialState, toSharedState, YulState.initial]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  rw [Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self]
  change (Batteries.RBMap.find? (projectStorage storage observableSlots)
      (natToUInt256 slot)).getD ⟨0⟩ = natToUInt256 0
  rw [hFindStorage]
  rfl

/-- Native primitive execution of `sload(slot)` on an initially materialized,
    word-canonical observable slot returns exactly the projected storage word. -/
theorem primCall_sload_initialState_observableSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok ((initialState contract tx storage observableSlots).setSharedState
              { (initialState contract tx storage observableSlots).toSharedState with
                toState := state' },
            [storage (IRStorageSlot.ofNat slot)]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hvalue :=
        initialState_sload_observableSlot_value contract tx storage
          observableSlots slot hSlot hRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hvalue]

/-- Native primitive execution of `sload(slot)` on an initially omitted,
    word-canonical materialization slot returns the EVM zero word. -/
theorem primCall_sload_initialState_omittedSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok ((initialState contract tx storage observableSlots).setSharedState
              { (initialState contract tx storage observableSlots).toSharedState with
                toState := state' },
            [natToUInt256 0]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hvalue :=
        initialState_sload_omittedSlot_value contract tx storage
          observableSlots slot hNotSlot hRange hSlotRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hvalue]

/-- Native primitive execution of `sload(slot)` is independent of the current
    Yul local-variable store when reading an initially materialized,
    word-canonical observable slot. This is the selected-body shape left after
    the lowered dispatcher inserts switch temporaries. -/
theorem primCall_sload_initialState_observableSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hSlot : slot ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok (((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).setSharedState
              { (.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).toSharedState with
                toState := state' }),
            [storage (IRStorageSlot.ofNat slot)]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hloadShared :
          (initialState contract tx storage observableSlots).sharedState.sload
              (natToUInt256 slot) = (state', value) := by
        simpa [EvmYul.Yul.State.toState] using hload
      have hvalue :=
        initialState_sload_observableSlot_value contract tx storage
          observableSlots slot hSlot hRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hloadShared, hvalue, EvmYul.Yul.State.toState]

/-- Native primitive execution of `sload(slot)` is independent of the current
    Yul local-variable store when reading an omitted word-canonical slot. -/
theorem primCall_sload_initialState_omittedSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SLOAD [natToUInt256 slot] =
      match EvmYul.State.sload
          (initialState contract tx storage observableSlots).toState
          (natToUInt256 slot) with
      | (state', _) =>
          .ok (((.Ok (initialState contract tx storage observableSlots).sharedState
                store : EvmYul.Yul.State).setSharedState
              { (.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).toSharedState with
                toState := state' }),
            [natToUInt256 0]) := by
  rw [primCall_sload_ok]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 slot) = loaded
  cases loaded with
  | mk state' value =>
      have hloadShared :
          (initialState contract tx storage observableSlots).sharedState.sload
              (natToUInt256 slot) = (state', value) := by
        simpa [EvmYul.Yul.State.toState] using hload
      have hvalue :=
        initialState_sload_omittedSlot_value contract tx storage
          observableSlots slot hNotSlot hRange hSlotRange
      rw [hload] at hvalue
      simp only at hvalue
      simp [hloadShared, hvalue, EvmYul.Yul.State.toState]

/-- Native primitive execution of `sstore(slot, value)` on an initial runtime
    state succeeds with the exact EVMYulLean `State.sstore` successor. The
    range hypothesis records the word-canonical slot condition needed by the
    dispatcher proof when this lemma is connected to projected storage. -/
theorem primCall_sstore_initialState_wordSlot_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot value : Nat)
    (_hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (initialState contract tx storage observableSlots)
        EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
      .ok (((initialState contract tx storage observableSlots).setState
          ((initialState contract tx storage observableSlots).toState.sstore
            (natToUInt256 slot) (natToUInt256 value))), []) := by
  rw [primCall_sstore_ok]
  simp [initialState, EvmYul.Yul.State.executionEnv]

/-- Native primitive execution of `sstore(slot, value)` from an initial runtime
    shared state is independent of the current Yul local-variable store. This
    packages the word-slot storage write in the shape produced after dispatcher
    switch temporaries have been inserted. -/
theorem primCall_sstore_initialState_wordSlot_ok_withStore
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (_hSlotRange : slot < EvmYul.UInt256.size) :
    EvmYul.Yul.primCall (fuel + 1)
        (.Ok (initialState contract tx storage observableSlots).sharedState store)
        EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
      .ok (((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).setState
          ((.Ok (initialState contract tx storage observableSlots).sharedState store :
              EvmYul.Yul.State).toState.sstore
            (natToUInt256 slot) (natToUInt256 value))), []) := by
  rw [primCall_sstore_ok]
  simp [initialState, EvmYul.Yul.State.sharedState,
    EvmYul.Yul.State.executionEnv, YulState.initial, toSharedState]

/-- Native primitive execution of the generated `store(uint256)` core:
    `calldataload(4)` decodes the first ABI argument and the following
    `sstore(0, value)` writes that word to slot zero. This is the real native
    primitive sequence under the emitted SimpleStorage setter body, before the
    terminating `stop`. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_ok
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (loadFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
      match values with
      | [value] =>
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .ok (((initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))), []) := by
  rw [primCall_calldataload4_initialState_arg0_ok loadFuel contract tx storage
    observableSlots arg rest hArgs]
  change EvmYul.Yul.primCall (storeFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, natToUInt256 arg] =
    .ok (((initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))), [])
  exact primCall_sstore_initialState_wordSlot_ok storeFuel contract tx storage
    observableSlots 0 arg (by norm_num [EvmYul.UInt256.size])

/-- Native primitive execution of the `return(0, 32)` half of the generated
    scalar-return sequence after `mstore(0, value)`. EVMYulLean models `RETURN`
    as a Yul halt carrying the post-`evmReturn` state; the halt literal is the
    default nonzero marker produced by `binaryMachineStateOp`, while the actual
    returned bytes live in the state's `H_return` buffer. -/
theorem primCall_return32_after_mstore0_ok
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    EvmYul.Yul.primCall (fuel + 1)
        (state.setMachineState
          (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value))
        EvmYul.Operation.RETURN
        [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32] =
      .error (EvmYul.Yul.Exception.YulHalt
        ((state.setMachineState
            (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).setMachineState
          ((state.setMachineState
              (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)))
        ⟨1⟩) := by
  rw [primCall_return_ok]
  simp [EvmYul.Yul.binaryMachineStateOp]

/-- Native primitive execution of the generated scalar-return instruction pair
    through EVMYulLean's actual `MSTORE` and `RETURN` primitive relation. This
    exposes the exact halt state that remains to be connected to Verity's
    single-word `returnValue` projection. -/
theorem primCall_mstore0_then_return32_ok
    (mstoreFuel returnFuel : Nat)
    (state : EvmYul.Yul.State)
    (value : EvmYul.UInt256) :
    (do
      let (state', values) ←
        EvmYul.Yul.primCall (mstoreFuel + 1) state
          EvmYul.Operation.MSTORE
          [EvmYul.UInt256.ofNat 0, value]
      match values with
      | [] =>
          EvmYul.Yul.primCall (returnFuel + 1) state'
            EvmYul.Operation.RETURN
            [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
      .error (EvmYul.Yul.Exception.YulHalt
        ((state.setMachineState
            (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).setMachineState
          ((state.setMachineState
              (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
            (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)))
        ⟨1⟩) := by
  rw [primCall_mstore_ok]
  exact primCall_return32_after_mstore0_ok returnFuel state value

/-- The native return buffer produced by `mstore(0, value); return(0, 32)` is
    exactly one EVM word wide. -/
theorem mstore0_then_return32_hReturn_size
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return.size = 32 := by
  dsimp
  have hZero : (EvmYul.UInt256.ofNat 0).toNat = 0 := by
    rfl
  have hLen : (EvmYul.UInt256.ofNat 32).toNat = 32 := by
    rfl
  simp [EvmYul.MachineState.evmReturn, readWithPadding_32_size,
    EvmYul.MachineState.mstore,
    EvmYul.MachineState.writeWord, EvmYul.writeBytes,
    EvmYul.UInt256.toByteArray, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.sharedState, EvmYul.Yul.State.toMachineState, hZero, hLen]

/-- If the generated scalar-return sequence starts from empty memory and the
    value word is represented by exactly 32 bytes, then the native `RETURN`
    halt buffer is byte-for-byte the word written by `MSTORE`. -/
theorem mstore0_then_return32_emptyMemory_hReturn_eq
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty)
    (hValueSize : value.toByteArray.size = 32) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return = value.toByteArray := by
  dsimp
  simp only [EvmYul.Yul.State.toMachineState, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.sharedState]
  simp only [EvmYul.MachineState.mstore, EvmYul.MachineState.writeWord,
    EvmYul.writeBytes, EvmYul.MachineState.evmReturn]
  simp only [hMemory]
  exact byteArray_write_empty_zero_32_readWithPadding_eq_of_size
    value.toByteArray hValueSize

/-- The generated scalar-return sequence started from empty memory returns
    exactly the 32-byte representation of the word written at offset zero. -/
theorem mstore0_then_return32_emptyMemory_hReturn_eq_toByteArray
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    let state : EvmYul.Yul.State := .Ok sharedState store
    let stored :=
      state.setMachineState
        (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
    let returned :=
      stored.setMachineState
        (stored.toMachineState.evmReturn
          (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
    returned.sharedState.H_return = value.toByteArray :=
  mstore0_then_return32_emptyMemory_hReturn_eq sharedState store value hMemory
    (uint256_toByteArray_size value)

/-- The concrete native primitive execution theorem for the generated scalar
    return sequence carries a one-word return buffer when started from an
    executable `Ok` Yul state. -/
theorem primCall_mstore0_then_return32_ok_hReturn_size
    (mstoreFuel returnFuel : Nat)
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      haltState.sharedState.H_return.size = 32 := by
  refine ⟨
    ((EvmYul.Yul.State.Ok sharedState store).setMachineState
        ((EvmYul.Yul.State.Ok sharedState store).toMachineState.mstore
          (EvmYul.UInt256.ofNat 0) value)).setMachineState
      (((EvmYul.Yul.State.Ok sharedState store).setMachineState
          ((EvmYul.Yul.State.Ok sharedState store).toMachineState.mstore
            (EvmYul.UInt256.ofNat 0) value)).toMachineState.evmReturn
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32)),
    ⟨1⟩, ?_⟩
  constructor
  · exact primCall_mstore0_then_return32_ok mstoreFuel returnFuel
      (.Ok sharedState store) value
  · exact mstore0_then_return32_hReturn_size sharedState store value

/-- Native initial-state storage materialization defaults omitted observable
    pre-state slots to zero. The in-range hypotheses rule out modular aliasing
    through the EVM word key used by the finite native storage map. -/
theorem initialState_omittedStorageSlot
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (slot : Nat)
    (hNotSlot : slot ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    projectStorageFromState tx
      (initialState contract tx storage observableSlots) (IRStorageSlot.ofNat slot) = 0 := by
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
  simp [IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hNone]

/-- Decode one 32-byte big-endian word from an EVMYulLean byte array. -/
def byteArrayWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => (acc * 256 + ((bytes.get? (offset + i)).getD 0).toNat) %
      Compiler.Constants.evmModulus)
    0

private def listByteArrayWordNoMod (bytes : List UInt8) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => acc * 256 + ((bytes[i]?).getD 0).toNat) 0

private def listByteArrayWordMod (bytes : List UInt8) (n : Nat) : Nat :=
  (List.range n).foldl
    (fun acc i => (acc * 256 + ((bytes[i]?).getD 0).toNat) %
      Compiler.Constants.evmModulus) 0

private theorem fromBytes'_reverse_append_single (xs : List UInt8) (b : UInt8) :
    EvmYul.fromBytes' ((xs ++ [b]).reverse) =
      EvmYul.fromBytes' xs.reverse * 256 + b.toNat := by
  simp [EvmYul.fromBytes']
  omega

private theorem listByteArrayWordNoMod_eq_fromBytes'_take_reverse
    (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    listByteArrayWordNoMod bytes n =
      EvmYul.fromBytes' (bytes.take n).reverse := by
  induction n with
  | zero =>
      simp [listByteArrayWordNoMod, EvmYul.fromBytes']
  | succ n ih =>
      have hn' : n ≤ bytes.length := by omega
      have hlt : n < bytes.length := by omega
      unfold listByteArrayWordNoMod at ih ⊢
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hn']
      rw [List.take_succ]
      rw [List.getElem?_eq_getElem hlt]
      simp only [Option.getD_some, Option.toList_some]
      rw [fromBytes'_reverse_append_single]

private theorem listByteArrayWordNoMod_lt
    (bytes : List UInt8) (n : Nat)
    (hn : n ≤ bytes.length) :
    listByteArrayWordNoMod bytes n < 2 ^ (8 * n) := by
  rw [listByteArrayWordNoMod_eq_fromBytes'_take_reverse bytes n hn]
  have h := fromBytes'_lt (bytes.take n).reverse
  have hlen : (bytes.take n).reverse.length = n := by
    simp [List.length_take, hn]
  simpa [hlen] using h

private theorem listByteArrayWordMod_eq_noMod
    (bytes : List UInt8) (n : Nat)
    (hnLen : n ≤ bytes.length) (hnWord : n ≤ 32) :
    listByteArrayWordMod bytes n = listByteArrayWordNoMod bytes n := by
  induction n with
  | zero =>
      simp [listByteArrayWordMod, listByteArrayWordNoMod]
  | succ n ih =>
      have hnLen' : n ≤ bytes.length := by omega
      have hnWord' : n ≤ 32 := by omega
      unfold listByteArrayWordMod listByteArrayWordNoMod at ih ⊢
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hnLen' hnWord']
      have hNoMod :
          (List.foldl (fun acc i => acc * 256 + (bytes[i]?.getD 0).toNat) 0
                (List.range n) *
              256 +
            (bytes[n]?.getD 0).toNat) < Compiler.Constants.evmModulus := by
        rw [show
            List.foldl (fun acc i => acc * 256 + (bytes[i]?.getD 0).toNat)
                0 (List.range n) =
              listByteArrayWordNoMod bytes n by rfl]
        have hprev := listByteArrayWordNoMod_lt bytes n hnLen'
        have hb : (bytes[n]?.getD 0).toNat < 256 := by
          cases hopt : bytes[n]?
          · simp
          · simp
            exact UInt8.toNat_lt _
        have hpow : 2 ^ (8 * n) * 256 = 2 ^ (8 * (n + 1)) := by
          rw [Nat.mul_add, Nat.pow_add]
        have hle : 2 ^ (8 * (n + 1)) ≤ Compiler.Constants.evmModulus := by
          have : 8 * (n + 1) ≤ 256 := by omega
          unfold Compiler.Constants.evmModulus
          exact Nat.pow_le_pow_right (by norm_num) this
        nlinarith
      rw [Nat.mod_eq_of_lt hNoMod]

private theorem byteArray_get?_data_toList (bytes : ByteArray) (i : Nat) :
    bytes.get? i = bytes.data.toList[i]? := by
  unfold ByteArray.get?
  split
  · rw [Array.getElem?_toList]
    simp [ByteArray.get]
  · rename_i h
    have hlen : bytes.data.toList.length ≤ i := by
      simp [ByteArray.size] at h
      simpa using h
    have hnone : bytes.data.toList[i]? = none := List.getElem?_eq_none hlen
    exact hnone.symm

theorem byteArrayWord_eq_fromBytes'_reverse_of_size
    (bytes : ByteArray)
    (hSize : bytes.size = 32) :
    byteArrayWord bytes 0 = EvmYul.fromBytes' bytes.data.toList.reverse := by
  have hLen : bytes.data.toList.length = 32 := by
    simpa [ByteArray.size] using hSize
  unfold byteArrayWord
  rw [show
      List.foldl
          (fun acc i => (acc * 256 + ((bytes.get? (0 + i)).getD 0).toNat) %
            Compiler.Constants.evmModulus)
          0 (List.range 32) =
        listByteArrayWordMod bytes.data.toList 32 by
      simp [listByteArrayWordMod, byteArray_get?_data_toList]]
  rw [listByteArrayWordMod_eq_noMod bytes.data.toList 32 (by omega) (by omega)]
  have hNoMod :=
    listByteArrayWordNoMod_eq_fromBytes'_take_reverse bytes.data.toList 32
      (by omega)
  rw [hNoMod]
  rw [show bytes.data.toList.take 32 = bytes.data.toList by
    rw [← hLen, List.take_length]]

private theorem fromBytes'_replicate_zero (n : Nat) :
    EvmYul.fromBytes' (List.replicate n (0 : UInt8)) = 0 := by
  induction n with
  | zero =>
      simp [EvmYul.fromBytes']
  | succ n ih =>
      simp [List.replicate, EvmYul.fromBytes', ih]

private theorem fromBytes'_append_replicate_zero (xs : List UInt8) (n : Nat) :
    EvmYul.fromBytes' (xs ++ List.replicate n (0 : UInt8)) =
      EvmYul.fromBytes' xs := by
  rw [fromBytes'_append]
  simp [fromBytes'_replicate_zero]

theorem byteArrayWord_uint256_toByteArray
    (value : EvmYul.UInt256) :
    byteArrayWord value.toByteArray 0 = value.toNat := by
  rw [byteArrayWord_eq_fromBytes'_reverse_of_size
    value.toByteArray (uint256_toByteArray_size value)]
  unfold EvmYul.UInt256.toByteArray BE
  simp [ByteArray.data_append, ffi.ByteArray.zeroes,
    list_toByteArray_data_toList]
  simp [EvmYul.toBytesBigEndian]

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

theorem primCall_mstore0_then_return32_emptyMemory_projectHaltReturn
    (mstoreFuel returnFuel : Nat)
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectHaltReturn haltState haltValue = some value.toNat := by
  let state : EvmYul.Yul.State := .Ok sharedState store
  let stored :=
    state.setMachineState
      (state.toMachineState.mstore (EvmYul.UInt256.ofNat 0) value)
  let returned :=
    stored.setMachineState
      (stored.toMachineState.evmReturn
        (EvmYul.UInt256.ofNat 0) (EvmYul.UInt256.ofNat 32))
  refine ⟨returned, ⟨1⟩, ?_⟩
  constructor
  · exact primCall_mstore0_then_return32_ok mstoreFuel returnFuel
      (.Ok sharedState store) value
  · have hHalt : (⟨1⟩ : EvmYul.Yul.Ast.Literal) ≠ ⟨0⟩ := by
      intro h
      norm_num [EvmYul.UInt256.size] at h
    have hSize : returned.sharedState.H_return.size = 32 := by
      exact mstore0_then_return32_hReturn_size sharedState store value
    have hReturn : returned.sharedState.H_return = value.toByteArray := by
      exact mstore0_then_return32_emptyMemory_hReturn_eq_toByteArray
        sharedState store value hMemory
    rw [projectHaltReturn_32ByteReturn returned ⟨1⟩ hHalt hSize]
    rw [hReturn, byteArrayWord_uint256_toByteArray]

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

/-- Executing a singleton block whose only statement is another block is the
    same as executing the inner block, after the outer block consumes its fuel
    step. This is the structural wrapper around lowered contract dispatchers:
    `contractDispatcherExecResult` installs `[contract.dispatcher]` as the
    function body, while generated dispatcher lemmas reason about the lowered
    block itself. -/
theorem exec_singleton_block_eq_exec_block
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ (Nat.succ fuel)) (.Block [.Block body])
        codeOverride state =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body) codeOverride state := by
  simp [EvmYul.Yul.exec]
  cases EvmYul.Yul.exec (Nat.succ fuel) (.Block body) codeOverride state <;>
    simp

/-- Raw dispatcher execution for a lowered contract whose dispatcher is already
    a block reduces to direct execution of that block from the native initial
    switch state. This removes the function-call-frame wrapper from later
    SimpleStorage dispatcher case proofs. -/
theorem contractDispatcherExecResult_block_dispatcher_eq_exec_block
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (functions : Compiler.Proofs.YulGeneration.Backends.NativeFunctionMap)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    contractDispatcherExecResult (Nat.succ (Nat.succ fuel))
        { dispatcher := .Block body, functions := functions }
        (initialState { dispatcher := .Block body, functions := functions } tx
          storage observableSlots) =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body)
        (some { dispatcher := .Block body, functions := functions })
        (nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots) := by
  have hCallState :
      EvmYul.Yul.State.mkOk
          ((initialState { dispatcher := .Block body, functions := functions } tx
            storage observableSlots).initcall [] []) =
        nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots := by
    simp [nativeSwitchInitialOkState, initialState, EvmYul.Yul.State.initcall,
      EvmYul.Yul.State.setStore, EvmYul.Yul.State.multifill,
      EvmYul.Yul.State.mkOk]
    constructor <;> rfl
  unfold contractDispatcherExecResult
  change
    EvmYul.Yul.exec (Nat.succ (Nat.succ fuel)) (.Block [.Block body])
        (some { dispatcher := .Block body, functions := functions })
        (EvmYul.Yul.State.mkOk
          ((initialState { dispatcher := .Block body, functions := functions } tx
            storage observableSlots).initcall [] [])) =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block body)
        (some { dispatcher := .Block body, functions := functions })
        (nativeSwitchInitialOkState
          { dispatcher := .Block body, functions := functions } tx storage
          observableSlots)
  rw [hCallState]
  exact exec_singleton_block_eq_exec_block fuel body
    (some { dispatcher := .Block body, functions := functions })
    (nativeSwitchInitialOkState
      { dispatcher := .Block body, functions := functions } tx storage
      observableSlots)

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
    (storage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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

/-- Exact projected result for native primitive execution of
    `sstore(slot, value)` from an initial runtime shared state and arbitrary
    dispatcher local-variable store.

This is the generic word-canonical `SSTORE` primitive result shape needed by
the dispatcher proof before the SimpleStorage setter composes it with
`CALLDATALOAD` and `STOP`. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_eq
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      projectResult tx storage initialEvents (.ok (finalState, [])) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState tx finalState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx finalState)
          events := initialEvents ++ projectLogsFromState finalState } := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · simp [projectResult]

@[simp] theorem projectResult_yulHalt
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents (.ok (state, values))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_ok_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).success = true := by
  rfl

@[simp] theorem projectResult_ok_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).returnValue =
      values.head?.map uint256ToNat := by
  rfl

@[simp] theorem projectResult_ok_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_ok_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = value := by
  simp [projectResult, projectStorageFromState_accountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_ok_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (values : List EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  simp [projectResult, projectStorageFromState_missingAccount, hAccount]

@[simp] theorem projectResult_ok_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
      (.ok (state, values))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  simp [projectResult, projectStorageFromState_missingAccountStorageSlot,
    hAccount, hSlot]

/-- Native primitive execution of `sstore(slot, value)` on a word-canonical
    initial runtime slot, lifted through Verity's projected native result
    boundary for a nonzero write.

This is the generic storage-projection form of the SimpleStorage slot-zero
setter lemma: it proves that the actual EVMYulLean `SSTORE` primitive writes
the projected final storage word for any canonical slot, as long as the EVM
storage update takes the insertion branch rather than the zero-value erasure
branch. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueNonzero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        natToUInt256 value := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (natToUInt256 slot) (natToUInt256 value)), ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok fuel contract tx storage
      observableSlots slot value hSlotRange
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState]
    have hBranch :
        (EvmYul.UInt256.ofNat value == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueNonzero
    rw [hBranch]
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self]

/-- Native primitive execution of `sstore(slot, 0)` on a word-canonical
    initial runtime slot, lifted through Verity's projected native result
    boundary with the EVMYulLean zero-write erasure lookup isolated.

This is the zero-write companion to
`primCall_sstore_initialState_wordSlot_projectResult_slot`: it proves the
actual native `SSTORE` primitive path and leaves only the map-level fact that
erasing a key makes the projected lookup miss. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot_zero_of_erase
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (natToUInt256 slot) (natToUInt256 value)), ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok fuel contract tx storage
      observableSlots slot value hSlotRange
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState,
      natToUInt256]
    have hBranch :
        (EvmYul.UInt256.ofNat value == (Inhabited.default : EvmYul.UInt256)) =
          true := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueZero
    rw [hBranch]
    have hErase :
        (Batteries.RBMap.erase (projectStorage storage observableSlots)
          (natToUInt256 slot)).find? (natToUInt256 slot) = none :=
      Batteries.RBMap.find?_erase_self _ _
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self, IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hErase]

/-- Native primitive execution of `sstore(slot, 0)` on a word-canonical
    initial runtime slot with no observable slots materialized. The zero-write
    erasure lookup is discharged by computation at the generic `SSTORE`
    projection boundary. -/
theorem primCall_sstore_initialState_wordSlot_projectResult_slot_zero_emptyObservable
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (initialState contract tx storage [])
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  exact
    primCall_sstore_initialState_wordSlot_projectResult_slot_zero_of_erase
      fuel contract tx storage initialEvents [] slot value hSlotRange hValueZero

/-- Native primitive execution of `sstore(slot, value)` from an initial runtime
    shared state and arbitrary local-variable store, lifted through Verity's
    projected native result boundary for a nonzero word-canonical write. This is
    the generic dispatcher-local-store companion to
    `primCall_sstore_initialState_wordSlot_projectResult_slot`. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueNonzero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        natToUInt256 value := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · dsimp [initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState]
    have hBranch :
        (EvmYul.UInt256.ofNat value == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueNonzero
    rw [hBranch]
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self]

/-- Native primitive execution of `sstore(slot, 0)` from an initial runtime
    shared state and arbitrary local-variable store, lifted through Verity's
    projected native result boundary with the zero-write erasure lookup
    isolated. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_of_erase
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  refine ⟨initialWithStore.setState
    (initialWithStore.toState.sstore (natToUInt256 slot) (natToUInt256 value)),
    ?_, ?_⟩
  · exact primCall_sstore_initialState_wordSlot_ok_withStore fuel contract tx
      storage observableSlots store slot value hSlotRange
  · dsimp [initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState,
      natToUInt256]
    have hBranch :
        (EvmYul.UInt256.ofNat value == (Inhabited.default : EvmYul.UInt256)) =
          true := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueZero
    rw [hBranch]
    have hErase :
        (Batteries.RBMap.erase (projectStorage storage observableSlots)
          (natToUInt256 slot)).find? (natToUInt256 slot) = none :=
      Batteries.RBMap.find?_erase_self _ _
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self, IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hErase]

/-- Native primitive execution of `sstore(slot, 0)` from an arbitrary local
    store when no observable storage (IRStorageSlot.ofNat slot)s were materialized. -/
theorem primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_emptyObservable
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (store : EvmYul.Yul.VarStore)
    (slot value : Nat)
    (hSlotRange : slot < EvmYul.UInt256.size)
    (hValueZero :
      (natToUInt256 value == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      EvmYul.Yul.primCall (fuel + 1)
          (.Ok (initialState contract tx storage []).sharedState store)
          EvmYul.Operation.SSTORE [natToUInt256 slot, natToUInt256 value] =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat slot) =
        0 := by
  exact
    primCall_sstore_initialState_wordSlot_withStore_projectResult_slot_zero_of_erase
      fuel contract tx storage initialEvents [] store slot value hSlotRange
      hValueZero

/-- Native primitive execution of the generated `store(uint256)` core, lifted
    through Verity's projected native result boundary for call success and
    absence of a return word. Storage-slot agreement remains the next setter
    projection obligation, but callers no longer need to inspect the raw
    `calldataload(4); sstore(0, arg0)` result shape for these fields. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_ok
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).success = true ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).returnValue =
        none := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · rfl
  · rfl

/-- The native primitive sequence used by the generated SimpleStorage setter
    body after dispatcher selection. -/
def primCall_calldataload4_then_sstore0_stop_initialState_arg0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (loadFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (stopFuel + 1) state''
              EvmYul.Operation.STOP []
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Store-parametric form of the native primitive sequence used by the
    generated SimpleStorage setter body. The lowered dispatcher executes the
    selected body after adding switch temporaries to the Yul `VarStore`, while
    calldata and storage effects are carried entirely by the shared state. -/
def primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (loadFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState store)
      EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (storeFuel + 1) state'
            EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (stopFuel + 1) state''
              EvmYul.Operation.STOP []
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Exact native primitive execution shape for the generated SimpleStorage setter
    body after dispatcher selection. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let finalState :=
      (initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
    primCall_calldataload4_then_sstore0_stop_initialState_arg0
      loadFuel storeFuel stopFuel contract tx storage observableSlots =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  dsimp
  unfold primCall_calldataload4_then_sstore0_stop_initialState_arg0
  rw [primCall_calldataload4_initialState_arg0_ok loadFuel contract tx
    storage observableSlots arg rest hArgs]
  change
    (do
      let (state'', values') ←
        EvmYul.Yul.primCall (storeFuel + 1)
          (initialState contract tx storage observableSlots)
          EvmYul.Operation.SSTORE
          [EvmYul.UInt256.ofNat 0, natToUInt256 arg]
      match values' with
      | [] =>
          EvmYul.Yul.primCall (stopFuel + 1) state''
            EvmYul.Operation.STOP []
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
    .error (EvmYul.Yul.Exception.YulHalt
      ((initialState contract tx storage observableSlots).setState
        ((initialState contract tx storage observableSlots).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))) ⟨0⟩)
  rw [primCall_sstore_initialState_wordSlot_ok storeFuel contract tx storage
    observableSlots 0 arg (by norm_num [EvmYul.UInt256.size])]
  exact primCall_stop_ok stopFuel _

/-- Exact native primitive execution shape for the generated SimpleStorage
    setter body when the selected body starts with an arbitrary Yul
    local-variable store. This removes the empty-store side condition left
    around the dispatcher-selected setter path. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    let initialWithStore : EvmYul.Yul.State :=
      .Ok (initialState contract tx storage observableSlots).sharedState store
    let finalState :=
      initialWithStore.setState
        (initialWithStore.toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
      loadFuel storeFuel stopFuel contract tx storage observableSlots store =
      .error (EvmYul.Yul.Exception.YulHalt finalState ⟨0⟩) := by
  dsimp
  unfold primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
  rw [primCall_calldataload4_initialState_arg0_ok_withStore loadFuel contract
    tx storage observableSlots store arg rest hArgs]
  change
    (do
      let (state'', values') ←
        EvmYul.Yul.primCall (storeFuel + 1)
          (.Ok (initialState contract tx storage observableSlots).sharedState store)
          EvmYul.Operation.SSTORE
          [EvmYul.UInt256.ofNat 0, natToUInt256 arg]
      match values' with
      | [] =>
          EvmYul.Yul.primCall (stopFuel + 1) state''
            EvmYul.Operation.STOP []
      | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
    .error (EvmYul.Yul.Exception.YulHalt
      ((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).setState
        ((.Ok (initialState contract tx storage observableSlots).sharedState store :
            EvmYul.Yul.State).toState.sstore
          (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))) ⟨0⟩)
  rw [primCall_sstore_initialState_wordSlot_ok_withStore storeFuel contract tx
    storage observableSlots store 0 arg (by norm_num [EvmYul.UInt256.size])]
  exact primCall_stop_ok stopFuel _

/-- Native primitive execution of the full generated `store(uint256)` selected
    body from an arbitrary local store, lifted through the terminating `STOP`
    halt and Verity's projected native result boundary for call success and
    absence of a return word. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_ok
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).success =
        true ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        none := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · rfl
  · rfl

/-- Exact projected result for the generated `store(uint256)` selected body
    from an arbitrary dispatcher local store. This packages the
    `CALLDATALOAD; SSTORE; STOP` native primitive sequence as one full
    `YulResult` equality, rather than only exposing success and return-value
    field facts. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · simp [projectResult]

/-- Exact projected result for the generated `store(uint256)` selected body at
    the IR transaction boundary used by the end-to-end native theorem. This is
    the `YulTransaction.ofIR` specialization of the dispatcher-local
    `CALLDATALOAD; SSTORE; STOP` native primitive sequence. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_ofIR_arg0_withStore_projectResult_eq
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract (YulTransaction.ofIR tx) storage
        observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult (YulTransaction.ofIR tx) storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := none
          finalStorage := projectStorageFromState (YulTransaction.ofIR tx) haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings
              (projectStorageFromState (YulTransaction.ofIR tx) haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_eq
      loadFuel storeFuel stopFuel contract (YulTransaction.ofIR tx) storage
      initialEvents observableSlots store arg rest (by simpa using hArgs)

/-- Native primitive execution of the full generated `store(uint256)` selected
    body from an arbitrary local store, lifted through `STOP` and Verity's
    projected native result boundary for a nonzero slot-zero write. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · dsimp [finalState, initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueNonzero
    rw [hBranch]
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self]

/-- Zero-write storage projection for the full generated `store(uint256)`
    selected body from an arbitrary local store, through the terminating
    `STOP`, with the remaining RBMap erasure fact isolated. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage observableSlots store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  let initialWithStore : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let finalState :=
    initialWithStore.setState
      (initialWithStore.toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots store arg
      rest hArgs
  · dsimp [finalState, initialWithStore]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState,
      natToUInt256]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          true := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueZero
    rw [hBranch]
    have hErase :
        (Batteries.RBMap.erase (projectStorage storage observableSlots)
          (EvmYul.UInt256.ofNat 0)).find? (EvmYul.UInt256.ofNat 0) = none :=
      Batteries.RBMap.find?_erase_self _ _
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self, IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hErase]

/-- Zero-write storage projection for the full generated `store(uint256)`
    selected body from an arbitrary local store when no observable slots were
    materialized. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (store : EvmYul.Yul.VarStore)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore
        loadFuel storeFuel stopFuel contract tx storage [] store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_withStore_projectResult_slot0_zero_of_erase
      loadFuel storeFuel stopFuel contract tx storage initialEvents [] store arg
      rest hArgs hValueZero

/-- Native primitive execution of the full generated `store(uint256)` selected
    body tail: `calldataload(4); sstore(0, arg0); stop`. The terminating
    `STOP` travels through EVMYulLean's Yul-halt channel and projects as a
    successful call with no return word. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_ok
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).success =
        true ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        none := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · rfl
  · rfl

/-- Native primitive execution of the full generated `store(uint256)` selected
    body, lifted through the terminating `STOP` halt and Verity's projected
    native result boundary for a nonzero slot-zero write. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction) (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · dsimp [finalState]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueNonzero
    rw [hBranch]
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self]

/-- Zero-write storage projection for the full generated `store(uint256)` selected
    body through the terminating `STOP`, with the remaining RBMap erasure fact
    isolated at the same boundary as the non-terminating setter-core lemma. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  let finalState :=
    (initialState contract tx storage observableSlots).setState
      ((initialState contract tx storage observableSlots).toState.sstore
        (EvmYul.UInt256.ofNat 0) (natToUInt256 arg))
  refine ⟨finalState, ⟨0⟩, ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_stop_initialState_arg0_eq
      loadFuel storeFuel stopFuel contract tx storage observableSlots arg rest
      hArgs
  · dsimp [finalState]
    simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState,
      natToUInt256]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          true := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueZero
    rw [hBranch]
    have hErase :
        (Batteries.RBMap.erase (projectStorage storage observableSlots)
          (EvmYul.UInt256.ofNat 0)).find? (EvmYul.UInt256.ofNat 0) = none :=
      Batteries.RBMap.find?_erase_self _ _
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self, IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hErase]

/-- Zero-write storage projection for the full generated `store(uint256)` selected
    body through `STOP` when no observable slots were materialized. -/
theorem primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel stopFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ haltState haltValue,
      primCall_calldataload4_then_sstore0_stop_initialState_arg0
        loadFuel storeFuel stopFuel contract tx storage [] =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_stop_initialState_arg0_projectResult_slot0_zero_of_erase
      loadFuel storeFuel stopFuel contract tx storage initialEvents [] arg rest
      hArgs hValueZero

/-- Native primitive execution of the generated `store(uint256)` core, lifted
    through Verity's projected native result boundary for a nonzero slot-zero
    write. The remaining zero-write case goes through `Account.updateStorage`'s
    key-erasure branch and needs the corresponding `RBMap.erase` lookup fact. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueNonzero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = false) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        natToUInt256 arg := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          false := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueNonzero
    rw [hBranch]
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self]

/-- Zero `sstore` projection, with the remaining RBMap erasure fact isolated. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_of_erase
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage observableSlots)
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  refine ⟨(initialState contract tx storage observableSlots).setState
    ((initialState contract tx storage observableSlots).toState.sstore
      (EvmYul.UInt256.ofNat 0) (natToUInt256 arg)), ?_, ?_⟩
  · exact primCall_calldataload4_then_sstore0_initialState_arg0_ok
      loadFuel storeFuel contract tx storage observableSlots arg rest hArgs
  · simp only [projectResult, projectStorageFromState, extractStorage,
      initialState, EvmYul.Yul.State.sharedState, EvmYul.Yul.State.setState,
      EvmYul.Yul.State.toState, EvmYul.State.sstore, EvmYul.State.lookupAccount,
      EvmYul.State.setAccount, EvmYul.State.addAccessedStorageKey,
      EvmYul.Account.updateStorage, YulState.initial, toSharedState,
      natToUInt256]
    have hBranch :
        (EvmYul.UInt256.ofNat arg == (Inhabited.default : EvmYul.UInt256)) =
          true := by
      simpa [natToUInt256, EvmYul.UInt256.instInhabited] using hValueZero
    rw [hBranch]
    have hErase :
        (Batteries.RBMap.erase (projectStorage storage observableSlots)
          (EvmYul.UInt256.ofNat 0)).find? (EvmYul.UInt256.ofNat 0) = none :=
      Batteries.RBMap.find?_erase_self _ _
    simp [Option.option, Batteries.RBMap.find?_insert_of_eq _
      Std.ReflCmp.compare_self, IRStorageSlot.toUInt256, IRStorageSlot.ofNat, hErase]

/-- Zero `sstore` projection with empty observable-slot materialization. -/
theorem primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_emptyObservable
    (loadFuel storeFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (arg : Nat)
    (rest : List Nat)
    (hArgs : tx.args = arg :: rest)
    (hValueZero :
      (natToUInt256 arg == (⟨0⟩ : EvmYul.UInt256)) = true) :
    ∃ finalState,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (loadFuel + 1)
            (initialState contract tx storage [])
            EvmYul.Operation.CALLDATALOAD [EvmYul.UInt256.ofNat 4]
        match values with
        | [value] =>
            EvmYul.Yul.primCall (storeFuel + 1) state'
              EvmYul.Operation.SSTORE [EvmYul.UInt256.ofNat 0, value]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .ok (finalState, []) ∧
      (projectResult tx storage initialEvents (.ok (finalState, []))).finalStorage (IRStorageSlot.ofNat 0) =
        0 := by
  exact
    primCall_calldataload4_then_sstore0_initialState_arg0_projectResult_slot0_zero_of_erase
      loadFuel storeFuel contract tx storage initialEvents [] arg rest hArgs
      hValueZero

@[simp] theorem projectResult_yulHalt_events
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).events =
      initialEvents ++ projectLogsFromState state := by
  rfl

@[simp] theorem projectResult_yulHalt_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).success = true := by
  rfl

@[simp] theorem projectResult_yulHalt_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).returnValue =
      projectHaltReturn state value := by
  rfl

/-- The exact native scalar-return primitive proof lifted through Verity's
    projected native result boundary. This is the shape consumed by dispatcher
    agreement: after native `mstore(0, value); return(0, 32)` halts, the
    projected `YulResult.returnValue` is exactly the returned word. -/
theorem primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
    (mstoreFuel returnFuel : Nat)
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx initialStorage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some value.toNat := by
  rcases primCall_mstore0_then_return32_emptyMemory_projectHaltReturn
      mstoreFuel returnFuel sharedState store value hMemory with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  simpa using hReturn

/-- Exact projected result for the generated scalar-return primitive sequence.
    Starting from empty native memory, `mstore(0, value); return(0, 32)` halts
    through the actual EVMYulLean primitive relation and projects as a successful
    one-word return containing exactly `value`. -/
theorem primCall_mstore0_then_return32_emptyMemory_projectResult_eq
    (mstoreFuel returnFuel : Nat)
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (sharedState : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (value : EvmYul.UInt256)
    (hMemory : sharedState.memory = ByteArray.empty) :
    ∃ haltState haltValue,
      (do
        let (state', values) ←
          EvmYul.Yul.primCall (mstoreFuel + 1) (.Ok sharedState store)
            EvmYul.Operation.MSTORE
            [EvmYul.UInt256.ofNat 0, value]
        match values with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state'
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx initialStorage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue := some value.toNat
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  rcases
    primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
      mstoreFuel returnFuel tx initialStorage initialEvents sharedState store value
      hMemory with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  have hProjectReturn :
      projectHaltReturn haltState haltValue = some value.toNat := by
    simpa [projectResult] using hReturn
  simp [projectResult, hProjectReturn]

/-- The native primitive sequence used by the generated SimpleStorage getter
    body after dispatcher selection. -/
def primCall_sload0_then_mstore0_return32_initialState
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (sloadFuel + 1)
      (initialState contract tx storage observableSlots)
      EvmYul.Operation.SLOAD [EvmYul.UInt256.ofNat 0]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (mstoreFuel + 1) state'
            EvmYul.Operation.MSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state''
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Store-parametric form of the native primitive sequence used by the
    generated SimpleStorage getter body. The lowered dispatcher executes the
    selected body after adding switch temporaries to the Yul `VarStore`, while
    storage and memory effects are carried by the shared state. -/
def primCall_sload0_then_mstore0_return32_initialState_withStore
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) :
    Except EvmYul.Yul.Exception
      (EvmYul.Yul.State × List EvmYul.Yul.Ast.Literal) := do
  let (state', values) ←
    EvmYul.Yul.primCall (sloadFuel + 1)
      (.Ok (initialState contract tx storage observableSlots).sharedState store)
      EvmYul.Operation.SLOAD [EvmYul.UInt256.ofNat 0]
  match values with
  | [value] =>
      (do
        let (state'', values') ←
          EvmYul.Yul.primCall (mstoreFuel + 1) state'
            EvmYul.Operation.MSTORE [EvmYul.UInt256.ofNat 0, value]
        match values' with
        | [] =>
            EvmYul.Yul.primCall (returnFuel + 1) state''
              EvmYul.Operation.RETURN
              [EvmYul.UInt256.ofNat 0, EvmYul.UInt256.ofNat 32]
        | _ => .error EvmYul.Yul.Exception.InvalidArguments)
  | _ => .error EvmYul.Yul.Exception.InvalidArguments

/-- Native primitive execution of the generated `retrieve()` scalar-return core:
    `sload(0)` reads the materialized slot-zero word, then `mstore(0, value);
    return(0, 32)` returns that exact word through the projected native result.

This composes the real EVMYulLean `SLOAD`, `MSTORE`, and `RETURN` primitive
relations for the SimpleStorage getter body, leaving only dispatcher selection
and oracle comparison around this selected-body path. -/
theorem primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSlot : 0 ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some (uint256ToNat (storage 0)) := by
  unfold primCall_sload0_then_mstore0_return32_initialState
  rw [primCall_sload_initialState_observableSlot_ok sloadFuel contract tx storage
    observableSlots 0 hSlot hRange]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { (initialState contract tx storage observableSlots).toSharedState with
          toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        simp [sharedAfterLoad, initialState, EvmYul.Yul.State.toSharedState,
          YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad ∅
          (storage 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad] using hExec
      · simpa [natToUInt256, EvmYul.UInt256.toNat, uint256ToNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    when slot zero was not materialized into the finite native storage map:
    `sload(0)` returns the EVM zero word, and the following
    `mstore(0, 0); return(0, 32)` projects as return value `0`. -/
theorem primCall_sload0_then_mstore0_return32_initialState_omittedSlot_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hNotSlot : 0 ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some 0 := by
  unfold primCall_sload0_then_mstore0_return32_initialState
  rw [primCall_sload_initialState_omittedSlot_ok sloadFuel contract tx storage
    observableSlots 0 hNotSlot hRange (by norm_num [EvmYul.UInt256.size])]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { (initialState contract tx storage observableSlots).toSharedState with
          toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        simp [sharedAfterLoad, initialState, EvmYul.Yul.State.toSharedState,
          YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad ∅
          (natToUInt256 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad] using hExec
      · simpa [natToUInt256, EvmYul.UInt256.toNat, uint256ToNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core,
    with the slot-zero materialization split discharged internally.

If slot zero was materialized as observable native storage, the getter returns
    the projected Verity storage word. If it was omitted from materialization,
    EVMYulLean's `SLOAD` default-zero behavior is exposed as return value zero.
    This theorem removes the caller-side `0 ∈ observableSlots`/`0 ∉
    observableSlots` premise split from the selected-body dispatcher proof. -/
theorem primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
  by_cases hSlot : 0 ∈ observableSlots
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_pos hSlot]
    simpa using hReturn
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_omittedSlot_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_neg hSlot]
    simpa using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store when slot zero is materialized. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hSlot : 0 ∈ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some (uint256ToNat (storage 0)) := by
  unfold primCall_sload0_then_mstore0_return32_initialState_withStore
  rw [primCall_sload_initialState_observableSlot_ok_withStore sloadFuel
    contract tx storage observableSlots store 0 hSlot hRange]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let initialWithStore : EvmYul.Yul.State :=
        .Ok (initialState contract tx storage observableSlots).sharedState store
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { initialWithStore.toSharedState with toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        change initialWithStore.toSharedState.memory = ByteArray.empty
        simp [initialWithStore, initialState, EvmYul.Yul.State.toSharedState,
          EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad store
          (storage 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad, initialWithStore] using hExec
      · simpa [natToUInt256, EvmYul.UInt256.toNat, uint256ToNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store when slot zero is omitted. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_omittedSlot_projectResult_returnValue
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hNotSlot : 0 ∉ observableSlots)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        some 0 := by
  unfold primCall_sload0_then_mstore0_return32_initialState_withStore
  rw [primCall_sload_initialState_omittedSlot_ok_withStore sloadFuel
    contract tx storage observableSlots store 0 hNotSlot hRange
    (by norm_num [EvmYul.UInt256.size])]
  generalize hload :
      EvmYul.State.sload
        (initialState contract tx storage observableSlots).toState
        (natToUInt256 0) = loaded
  cases loaded with
  | mk stateAfterLoad _ =>
      let initialWithStore : EvmYul.Yul.State :=
        .Ok (initialState contract tx storage observableSlots).sharedState store
      let sharedAfterLoad : EvmYul.SharedState .Yul :=
        { initialWithStore.toSharedState with toState := stateAfterLoad }
      have hMemory : sharedAfterLoad.memory = ByteArray.empty := by
        change initialWithStore.toSharedState.memory = ByteArray.empty
        simp [initialWithStore, initialState, EvmYul.Yul.State.toSharedState,
          EvmYul.Yul.State.sharedState, YulState.initial, toSharedState]
      rcases
        primCall_mstore0_then_return32_emptyMemory_projectResult_returnValue
          mstoreFuel returnFuel tx storage initialEvents sharedAfterLoad store
          (natToUInt256 0) hMemory with
        ⟨haltState, haltValue, hExec, hReturn⟩
      refine ⟨haltState, haltValue, ?_, ?_⟩
      · simpa [sharedAfterLoad, initialWithStore] using hExec
      · simpa [natToUInt256, EvmYul.UInt256.toNat, uint256ToNat] using hReturn

/-- Native primitive execution of the generated `retrieve()` scalar-return core
    from an arbitrary local store, with materialized/omitted slot zero handled
    internally. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      (projectResult tx storage initialEvents
        (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue))).returnValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
  by_cases hSlot : 0 ∈ observableSlots
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots store hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_pos hSlot]
    simpa using hReturn
  · rcases
      primCall_sload0_then_mstore0_return32_initialState_withStore_omittedSlot_projectResult_returnValue
        sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
        observableSlots store hSlot hRange with
      ⟨haltState, haltValue, hExec, hReturn⟩
    refine ⟨haltState, haltValue, hExec, ?_⟩
    rw [if_neg hSlot]
    simpa using hReturn

/-- Exact projected result for the generated `retrieve()` scalar-return core
    from an arbitrary dispatcher local store. This strengthens
    `primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized`
    from a return-value field fact to the full `YulResult` shape produced by the
    native `SLOAD; MSTORE; RETURN` halt. -/
theorem primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_eq_materialized
    (sloadFuel mstoreFuel returnFuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (hRange : ∀ s ∈ observableSlots, s < EvmYul.UInt256.size) :
    ∃ haltState haltValue,
      primCall_sload0_then_mstore0_return32_initialState_withStore
        sloadFuel mstoreFuel returnFuel contract tx storage observableSlots
        store =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        { success := true
          returnValue :=
            if 0 ∈ observableSlots then
              some (uint256ToNat (storage 0))
            else
              some 0
          finalStorage := projectStorageFromState tx haltState
          finalMappings :=
            Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
          events := initialEvents ++ projectLogsFromState haltState } := by
  rcases
    primCall_sload0_then_mstore0_return32_initialState_withStore_projectResult_returnValue_materialized
      sloadFuel mstoreFuel returnFuel contract tx storage initialEvents
      observableSlots store hRange with
    ⟨haltState, haltValue, hExec, hReturn⟩
  refine ⟨haltState, haltValue, hExec, ?_⟩
  have hProjectReturn :
      projectHaltReturn haltState haltValue =
        if 0 ∈ observableSlots then
          some (uint256ToNat (storage 0))
        else
          some 0 := by
    simpa [projectResult] using hReturn
  simp [projectResult, hProjectReturn]

@[simp] theorem projectResult_yulHalt_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalMappings =
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx state) := by
  rfl

@[simp] theorem projectResult_yulHalt_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) =
        slotValue := by
  simp [projectResult, projectStorageFromState_accountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_yulHalt_missingFinalStorageAccountSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (state : EvmYul.Yul.State)
    (value : EvmYul.Yul.Ast.Literal)
    (slot : Nat)
    (hAccount :
      state.sharedState.accountMap.find? (natToAddress tx.thisAddress) =
        none) :
    (projectResult tx initialStorage initialEvents
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  simp [projectResult, projectStorageFromState_missingAccount, hAccount]

@[simp] theorem projectResult_yulHalt_missingFinalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
      (.error (.YulHalt state value))).finalStorage (IRStorageSlot.ofNat slot) = 0 := by
  simp [projectResult, projectStorageFromState_missingAccountStorageSlot,
    hAccount, hSlot]

@[simp] theorem projectResult_stop
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).events =
      initialEvents := by
  rfl

@[simp] theorem projectResult_revert_success
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).success = false := by
  rfl

@[simp] theorem projectResult_revert_returnValue
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).returnValue = none := by
  rfl

@[simp] theorem projectResult_revert_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalMappings =
      Compiler.Proofs.storageAsMappings initialStorage := by
  rfl

@[simp] theorem projectResult_revert_finalStorageSlot
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (slot : Nat) :
    (projectResult tx initialStorage initialEvents
      (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
      initialStorage (IRStorageSlot.ofNat slot) := by
  rfl

@[simp] theorem projectResult_hardError
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (err : EvmYul.Yul.Exception)
    (slot : Nat)
    (hNotHalt : ∀ state value, err ≠ EvmYul.Yul.Exception.YulHalt state value) :
    (projectResult tx initialStorage initialEvents (.error err)).finalStorage (IRStorageSlot.ofNat slot) =
      initialStorage (IRStorageSlot.ofNat slot) := by
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (initialStorage : IRStorageSlot → IRStorageWord)
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

/-- Guarded selector-miss execution for a fully lowered native switch block,
    lifted through Verity's projected native result boundary. The generated
    `revert(0, 0)` default both executes through the actual native step
    relation and projects as a failed call with no return word and rolled-back
    observable storage. -/
theorem exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult
    (fuel selector switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind : cases.find? (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size)
    (hTagsRange :
      ∀ tag body, (tag, body) ∈ cases → tag < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + cases.length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr switchId cases
            [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).success = false ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).returnValue = none ∧
    (∀ slot,
      (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
          storage (IRStorageSlot.ofNat slot)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_fuel
      fuel selector switchId cases contract tx storage observableSlots
      hSelector hFind hSelectorRange hTagsRange
  · simp
  · simp
  · intro slot
    simp

/-- The two generated SimpleStorage selector tags fit in one EVM word. -/
private theorem simpleStorageSelectors_tagsRange
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt) :
    ∀ tag body,
      (tag, body) ∈ [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] →
        tag < EvmYul.UInt256.size := by
  intro tag body hmem
  simp at hmem
  rcases hmem with h | h
  · rcases h with ⟨rfl, rfl⟩
    norm_num [EvmYul.UInt256.size]
  · rcases h with ⟨rfl, rfl⟩
    norm_num [EvmYul.UInt256.size]

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher
    selector set. This specializes the generic lowered-switch miss theorem to
    the two generated SimpleStorage selectors, discharging the selector tag
    word-range premise by computation. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult
    (fuel selector switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind :
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
          (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).success = false ∧
    (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).returnValue = none ∧
    (∀ slot,
      (projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert)).finalStorage (IRStorageSlot.ofNat slot) =
          storage (IRStorageSlot.ofNat slot)) := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_none_with_revert_default_projectResult
      fuel selector switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      contract tx storage initialEvents observableSlots
      hSelector hFind hSelectorRange
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    with the projected revert result exposed as one exact `YulResult`.

This packages the `revert(0, 0)` default branch in the shape needed by the
    dispatcher bridge: native execution reaches EVMYulLean's `Revert`
    exception, and Verity's projection rolls the call back to failed success,
    no return value, unchanged storage/mappings, and unchanged events. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult_eq
    (fuel selector switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelector :
      selector = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hFind :
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
          (fun entry => entry.1 == selector) = none)
    (hSelectorRange : selector < EvmYul.UInt256.size) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      { success := false
        returnValue := none
        finalStorage := storage
        finalMappings := Compiler.Proofs.storageAsMappings storage
        events := initialEvents } := by
  rcases
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult
      fuel selector switchId storeBody retrieveBody contract tx storage
      initialEvents observableSlots hSelector hFind hSelectorRange with
    ⟨hExec, _hSuccess, _hReturn, _hStorage⟩
  exact ⟨hExec, by simp⟩

def simpleStorageRevertProjectedResult
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat)) : YulResult :=
  { success := false
    returnValue := none
    finalStorage := storage
    finalMappings := Compiler.Proofs.storageAsMappings storage
    events := initialEvents }

/-- Concrete lowered native body for the generated SimpleStorage
    `store(uint256)` selector arm. Naming this body lets later dispatcher
    bridge lemmas specialize the selector-switch theorem without carrying
    arbitrary body parameters. -/
def simpleStorageNativeStoreBody : List EvmYul.Yul.Ast.Stmt :=
  [ .If (lowerExprNative (.call "callvalue" [])) [nativeRevertZeroZeroStmt],
    .If (lowerExprNative (.call "lt" [.call "calldatasize" [], .lit 36]))
      [nativeRevertZeroZeroStmt],
    .Let ["value"] (some (lowerExprNative (.call "calldataload" [.lit 4]))),
    .ExprStmtCall (lowerExprNative (.call "sstore" [.lit 0, .ident "value"])),
    .ExprStmtCall (lowerExprNative (.call "stop" [])) ]

/-- Concrete lowered native body for the generated SimpleStorage `retrieve()`
    selector arm. -/
def simpleStorageNativeRetrieveBody : List EvmYul.Yul.Ast.Stmt :=
  [ .If (lowerExprNative (.call "callvalue" [])) [nativeRevertZeroZeroStmt],
    .If (lowerExprNative (.call "lt" [.call "calldatasize" [], .lit 4]))
      [nativeRevertZeroZeroStmt],
    .ExprStmtCall
      (lowerExprNative
        (.call "mstore" [.lit 0, .call "sload" [.lit 0]])),
    .ExprStmtCall (lowerExprNative (.call "return" [.lit 0, .lit 32])) ]

def simpleStorageNativeSelectorCases :
    List (Nat × List EvmYul.Yul.Ast.Stmt) :=
  [(0x6057361d, simpleStorageNativeStoreBody),
    (0x2e64cec1, simpleStorageNativeRetrieveBody)]

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    specialized to the selector carried by the transaction.

This removes two bookkeeping premises from the default-branch bridge case:
callers no longer have to introduce a separate selector witness or prove that
the 4-byte selector fits in an EVM word. Both facts follow from the transaction
selector modulus bound used by the public end-to-end theorem. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_find_none_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hFind : [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].find?
        (fun entry => entry.1 == tx.functionSelector % Compiler.Constants.selectorModulus) = none) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_find_none_with_revert_default_projectResult_eq
      fuel (tx.functionSelector % Compiler.Constants.selectorModulus) switchId
      storeBody retrieveBody contract tx storage initialEvents observableSlots
      rfl hFind
      (by
        have hmod :
            tx.functionSelector % Compiler.Constants.selectorModulus =
              tx.functionSelector :=
          Nat.mod_eq_of_lt hSelectorBound
        have hModulus :
            Compiler.Constants.selectorModulus < EvmYul.UInt256.size := by
          norm_num [Compiler.Constants.selectorModulus, EvmYul.UInt256.size]
        rw [hmod]
        omega) |>.imp_right (by intro h; simp [simpleStorageRevertProjectedResult] at h ⊢)

/-- Guarded selector-miss execution for the concrete SimpleStorage dispatcher,
    using the semantic selector disequalities instead of the raw generated
    selector-table lookup.

This is the branch shape needed by the dispatcher bridge case split: once the
transaction selector is known to be neither generated selector, the concrete
`find? = none` premise is discharged internally before executing the actual
native lowered switch relation. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_miss_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNotStore : tx.functionSelector ≠ 0x6057361d)
    (hNotRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  apply
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_find_none_with_revert_default_projectResult_eq
      fuel switchId storeBody retrieveBody contract tx storage initialEvents
      observableSlots hSelectorBound
  have hMod := Nat.mod_eq_of_lt hSelectorBound
  simp [hMod]
  constructor
  · intro h
    exact hNotStore h.symm
  · intro h
    exact hNotRetrieve h.symm

/-- Guarded selector-miss execution for the concrete lowered SimpleStorage
    selector switch, with both generated selector bodies fixed to their native
    lowered shapes. This is the default branch theorem needed by the bridge
    once the outer dispatcher has exposed the inner selector switch. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_tx_miss_with_revert_default_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hNotStore : tx.functionSelector ≠ 0x6057361d)
    (hNotRetrieve : tx.functionSelector ≠ 0x2e64cec1) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, simpleStorageNativeStoreBody),
          (0x2e64cec1, simpleStorageNativeRetrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, simpleStorageNativeStoreBody),
            (0x2e64cec1, simpleStorageNativeRetrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error EvmYul.Yul.Exception.Revert ∧
    projectResult tx storage initialEvents
        (.error EvmYul.Yul.Exception.Revert) =
      simpleStorageRevertProjectedResult storage initialEvents := by
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_tx_miss_with_revert_default_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots hSelectorBound
      hNotStore hNotRetrieve

/-- Store-selector hit execution for the concrete SimpleStorage dispatcher
    selector set. This specializes the generic lowered-switch hit theorem to
    `store(uint256)`, discharging the computed selector lookup and selector tag
    word-range premises. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block storeBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
      fuel 0x6057361d switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x6057361d storeBody contract tx storage
      observableSlots err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

/-- Store-prefix variant of `_simpleStorageSelectors_store_hit_error_fuel`,
    lifting the SimpleStorage store-hit selector specialization to states
    already carrying additional bindings (e.g. the dispatcher's
    `__has_selector := 1`). -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_store_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (err : EvmYul.Yul.Exception)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block storeBody) (some contract)
          ((((.Ok (initialState contract tx storage observableSlots).sharedState
                  store : EvmYul.Yul.State).insert
                (Backends.nativeSwitchDiscrTempName switchId)
                (EvmYul.UInt256.ofNat
                  (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 0)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_store_fuel
      fuel 0x6057361d switchId 0x6057361d
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] storeBody contract tx storage
      observableSlots store err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

def simpleStorageStoreHaltProjectedResult
    (tx : YulTransaction)
    (initialEvents : List (List Nat))
    (haltState : EvmYul.Yul.State) : YulResult :=
  { success := true
    returnValue := none
    finalStorage := projectStorageFromState tx haltState
    finalMappings :=
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
    events := initialEvents ++ projectLogsFromState haltState }

/-- Store-selector hit execution for the concrete SimpleStorage dispatcher,
    packaged with the exact projected result of the selected setter body.

This removes the switch-case wrapper from later bridge obligations: callers can
prove the selected body once for every possible decomposition, then consume one
exact native `YulResult` equality at the full lowered-switch boundary. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelector : 0x6057361d = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x6057361d, storeBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block storeBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) =
            .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState) :
      EvmYul.Yul.exec
          (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId
            [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
            [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState := by
  refine ⟨?_, hProject⟩
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_error_fuel
      fuel switchId storeBody retrieveBody contract tx storage observableSlots
      (EvmYul.Yul.Exception.YulHalt haltState haltValue) hSelector
      hBody

/-- Concrete SimpleStorage store-selector hit execution. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_store_hit_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelector : tx.functionSelector = 0x6057361d)
    (hBody : ∀ pre suffix,
      simpleStorageNativeSelectorCases =
          pre ++ (0x6057361d, simpleStorageNativeStoreBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block simpleStorageNativeStoreBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) =
            .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState) :
      EvmYul.Yul.exec
          (fuel + simpleStorageNativeSelectorCases.length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId simpleStorageNativeSelectorCases [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageStoreHaltProjectedResult tx initialEvents haltState := by
  have hMod :
      tx.functionSelector % Compiler.Constants.selectorModulus =
        tx.functionSelector :=
    Nat.mod_eq_of_lt hSelectorBound
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_store_hit_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots haltState haltValue
      (by rw [hMod, hSelector])
      (by simpa [simpleStorageNativeSelectorCases] using hBody) hProject

/-- Retrieve-selector hit execution for the concrete SimpleStorage dispatcher. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_error_fuel
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (err : EvmYul.Yul.Exception)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x2e64cec1, retrieveBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block retrieveBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec
        (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
        (Backends.lowerNativeSwitchBlock
          Compiler.Proofs.YulGeneration.selectorExpr
          switchId
          [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
          [nativeRevertZeroZeroStmt])
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      .error err := by
  exact
    exec_lowerNativeSwitchBlock_selector_find_hit_error_fuel
      fuel 0x2e64cec1 switchId
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
      [nativeRevertZeroZeroStmt] 0x2e64cec1 retrieveBody contract tx storage
      observableSlots err hSelector
      (by simp)
      (by norm_num [EvmYul.UInt256.size])
      (simpleStorageSelectors_tagsRange storeBody retrieveBody)
      hBody

def simpleStorageRetrieveHaltProjectedResult
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State) : YulResult :=
  { success := true
    returnValue :=
      if 0 ∈ observableSlots then
        some (uint256ToNat (storage 0))
      else
        some 0
    finalStorage := projectStorageFromState tx haltState
    finalMappings :=
      Compiler.Proofs.storageAsMappings (projectStorageFromState tx haltState)
    events := initialEvents ++ projectLogsFromState haltState }

/-- Retrieve-selector hit execution for the concrete SimpleStorage dispatcher,
    packaged with the exact projected result of the selected getter body. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_projectResult_eq
    (fuel switchId : Nat)
    (storeBody retrieveBody : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelector :
      0x2e64cec1 = tx.functionSelector % Compiler.Constants.selectorModulus)
    (hBody : ∀ pre suffix,
      [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)] =
          pre ++ (0x2e64cec1, retrieveBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block retrieveBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) =
            .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState) :
      EvmYul.Yul.exec
          (fuel + [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)].length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId
            [(0x6057361d, storeBody), (0x2e64cec1, retrieveBody)]
            [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents
          (.error (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState := by
  refine ⟨?_, hProject⟩
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_error_fuel
      fuel switchId storeBody retrieveBody contract tx storage observableSlots
      (EvmYul.Yul.Exception.YulHalt haltState haltValue) hSelector
      hBody

/-- Concrete SimpleStorage retrieve-selector hit execution. -/
theorem exec_lowerNativeSwitchBlock_simpleStorageConcrete_retrieve_hit_projectResult_eq
    (fuel switchId : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (initialEvents : List (List Nat))
    (observableSlots : List Nat)
    (haltState : EvmYul.Yul.State)
    (haltValue : EvmYul.Yul.Ast.Literal)
    (hSelectorBound : tx.functionSelector < Compiler.Constants.selectorModulus)
    (hSelector : tx.functionSelector = 0x2e64cec1)
    (hBody : ∀ pre suffix,
      simpleStorageNativeSelectorCases =
          pre ++ (0x2e64cec1, simpleStorageNativeRetrieveBody) :: suffix →
        EvmYul.Yul.exec ((fuel + 1) + suffix.length + 7)
          (.Block simpleStorageNativeRetrieveBody) (some contract)
          ((nativeSwitchPrefixFinalState contract tx storage observableSlots
            (Backends.nativeSwitchDiscrTempName switchId)
            (Backends.nativeSwitchMatchedTempName switchId)).insert
              (Backends.nativeSwitchMatchedTempName switchId)
              (EvmYul.UInt256.ofNat 1)) =
            .error (EvmYul.Yul.Exception.YulHalt haltState haltValue))
    (hProject :
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState) :
      EvmYul.Yul.exec
          (fuel + simpleStorageNativeSelectorCases.length + 12)
          (Backends.lowerNativeSwitchBlock
            Compiler.Proofs.YulGeneration.selectorExpr
            switchId simpleStorageNativeSelectorCases [nativeRevertZeroZeroStmt])
          (some contract)
          (nativeSwitchInitialOkState contract tx storage observableSlots) =
        .error (EvmYul.Yul.Exception.YulHalt haltState haltValue) ∧
      projectResult tx storage initialEvents (.error
          (EvmYul.Yul.Exception.YulHalt haltState haltValue)) =
        simpleStorageRetrieveHaltProjectedResult tx storage initialEvents
          observableSlots haltState := by
  have hMod := Nat.mod_eq_of_lt hSelectorBound
  exact
    exec_lowerNativeSwitchBlock_simpleStorageSelectors_retrieve_hit_projectResult_eq
      fuel switchId simpleStorageNativeStoreBody simpleStorageNativeRetrieveBody
      contract tx storage initialEvents observableSlots haltState haltValue
      (by rw [hMod, hSelector])
      (by simpa [simpleStorageNativeSelectorCases] using hBody) hProject

@[simp] theorem projectResult_finalMappings
    (tx : YulTransaction)
    (initialStorage : IRStorageSlot → IRStorageWord)
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
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat) := []) :
    Except AdapterError YulResult := do
  validateGeneratedRuntimeNativeFragment runtimeCode
  let contract ← lowerRuntimeContractNative runtimeCode
  validateNativeRuntimeEnvironment runtimeCode tx
  let initial :=
    initialState contract tx storage
      (materializedStorageSlots runtimeCode observableSlots)
  let result := EvmYul.Yul.callDispatcher fuel (some contract) initial
  pure (projectResult tx storage events result)

@[simp] theorem interpretRuntimeNative_loweringError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (err : AdapterError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment, hLower]
  rfl

@[simp] theorem interpretRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (hFragment : generatedRuntimeNativeFragment runtimeCode = false) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_error runtimeCode hFragment]
  rfl

@[simp] theorem interpretRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .ok ()) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .ok (projectResult tx storage events
        (EvmYul.Yul.callDispatcher fuel (some contract)
          (initialState contract tx storage
            (materializedStorageSlots runtimeCode observableSlots)))) := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

@[simp] theorem interpretRuntimeNative_environmentError
    (fuel : Nat)
    (runtimeCode : List YulStmt)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (events : List (List Nat))
    (contract : EvmYul.Yul.Ast.YulContract)
    (err : AdapterError)
    (hFragment : generatedRuntimeNativeFragment runtimeCode = true)
    (hLower : lowerRuntimeContractNative runtimeCode = .ok contract)
    (hEnv : validateNativeRuntimeEnvironment runtimeCode tx = .error err) :
    interpretRuntimeNative fuel runtimeCode tx storage observableSlots events =
      .error err := by
  rw [interpretRuntimeNative, validateGeneratedRuntimeNativeFragment_ok runtimeCode hFragment,
    hLower, hEnv]
  rfl

/-- Native EVMYulLean execution target for emitted IR-contract runtime Yul.

This is the executable target that #1737 will promote into the public theorem
path once the state/result bridge lemmas are proved. It intentionally returns
`Except AdapterError YulResult` today because native lowering can still fail
closed for duplicate helper definitions or unsupported runtime shapes.

The observable slot set is explicit because the public theorem compares only
those final storage (IRStorageSlot.ofNat slot)s. Native execution materializes those slots plus
literal `sload` slots derived from the emitted runtime so storage reads remain
faithful even when callers compare a smaller public projection.
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
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul contract).runtimeCode =
      .error err) :
    interpretIRRuntimeNative fuel contract tx state observableSlots = .error err := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul contract).runtimeCode
      hFragment, hLower]
  rfl

@[simp] theorem interpretIRRuntimeNative_generatedFragmentError
    (fuel : Nat)
    (contract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul contract).runtimeCode = false) :
    interpretIRRuntimeNative fuel contract tx state observableSlots =
      .error unsupportedGeneratedRuntimeNativeFragmentError := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_error (Compiler.emitYul contract).runtimeCode
      hFragment]
  rfl

@[simp] theorem interpretIRRuntimeNative_eq_callDispatcher_of_lowerRuntimeContractNative
    (fuel : Nat)
    (irContract : Compiler.IRContract)
    (tx : Compiler.Proofs.IRGeneration.IRTransaction)
    (state : Compiler.Proofs.IRGeneration.IRState)
    (observableSlots : List Nat)
    (nativeContract : EvmYul.Yul.Ast.YulContract)
    (hFragment :
      generatedRuntimeNativeFragment (Compiler.emitYul irContract).runtimeCode = true)
    (hLower : lowerRuntimeContractNative (Compiler.emitYul irContract).runtimeCode =
      .ok nativeContract)
    (hEnv :
      validateNativeRuntimeEnvironment (Compiler.emitYul irContract).runtimeCode
        (YulTransaction.ofIR tx) = .ok ()) :
    interpretIRRuntimeNative fuel irContract tx state observableSlots =
      .ok (projectResult (YulTransaction.ofIR tx) state.storage state.events
        (EvmYul.Yul.callDispatcher fuel (some nativeContract)
          (initialState nativeContract (YulTransaction.ofIR tx) state.storage
            (materializedStorageSlots (Compiler.emitYul irContract).runtimeCode
              observableSlots)))) := by
  rw [interpretIRRuntimeNative, interpretRuntimeNative,
    validateGeneratedRuntimeNativeFragment_ok (Compiler.emitYul irContract).runtimeCode
      hFragment, hLower, hEnv]
  rfl

end Compiler.Proofs.YulGeneration.Backends.Native
