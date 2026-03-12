import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.MappingSlot
import Compiler.CompilationModel.LayoutValidation

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace SourceSemantics

def wordNormalize (n : Nat) : Nat :=
  ((n : Verity.Core.Uint256) : Nat)

def uint8Modulus : Nat := 2 ^ 8

def addressModulus : Nat := 2 ^ 160

def boolWord (b : Bool) : Nat :=
  if b then 1 else 0

def encodeEvent (ev : Verity.Event) : List Nat :=
  (ev.name.toList.map Char.toNat) ++
    (0 :: (ev.args.map (fun arg => arg.val))) ++
    (0 :: (ev.indexedArgs.map (fun arg => arg.val)))

def encodeEvents (events : List Verity.Event) : List (List Nat) :=
  events.map encodeEvent

def effectiveFields (spec : CompilationModel) : List Field :=
  applySlotAliasRanges spec.fields spec.slotAliasRanges

def fieldUsesAddressStorage (field : Field) : Bool :=
  match field.ty with
  | .address => true
  | _ => false

def fieldUsesDynamicArrayStorage (field : Field) : Bool :=
  match field.ty with
  | .dynamicArray _ => true
  | _ => false

private def findResolvedFieldAtSlot (fields : List Field) (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if resolvedSlot = slot || field.aliasSlots.contains slot then
          some field
        else
          go rest (idx + 1)
  go fields 0

private def findDynamicArrayElementAtSlot
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if Compiler.Proofs.solidityMappingSlot baseSlot idx = targetSlot then
          some value.val
        else
          scanElements baseSlot rest (idx + 1)
  let rec go (remaining : List Field) (idx : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        match field.ty with
        | .dynamicArray _ =>
            match scanElements resolvedSlot (world.storageArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

def encodeStorageAt (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlot fields slot with
  | some field =>
      if fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else if fieldUsesDynamicArrayStorage field then
        (world.storageArray slot).length
      else
        (world.storage slot).val
  | none =>
      match findDynamicArrayElementAtSlot fields world slot with
      | some value => value
      | none => (world.storage slot).val

def encodeStorage (spec : CompilationModel) (world : Verity.ContractState) : Nat → Nat :=
  encodeStorageAt (effectiveFields spec) world

def writeUintSlots (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  { world with
    storage := fun slot =>
      if slots.contains slot then word else world.storage slot }

def writeAddressSlots (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  let addr := Verity.wordToAddress (value : Verity.Core.Uint256)
  { world with
    storageAddr := fun slot =>
      if slots.contains slot then addr else world.storageAddr slot }

def decodeSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 => some word
  | .uint8 => some (word &&& (uint8Modulus - 1))
  | .address => some (word &&& Compiler.Constants.addressMask)
  | .bool =>
      if word = 0 then some 0
      else if word = 1 then some 1
      else none
  | .bytes32 => some word
  | _ => none

def bindValue (bindings : List (String × Nat)) (name : String) (value : Nat) :
    List (String × Nat) :=
  (name, value) :: bindings.filter (fun entry => entry.1 != name)

def lookupValue (bindings : List (String × Nat)) (name : String) : Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd |>.getD 0

def bindInternalArgs (params : List Param) (args : List Nat) :
    Option (List (String × Nat)) :=
  match params, args with
  | [], [] => some []
  | param :: restParams, arg :: restArgs => do
      let bindings ← bindInternalArgs restParams restArgs
      pure ((param.name, arg) :: bindings)
  | _, _ => none

private def findUniqueInternalFunction? (spec : CompilationModel) (calleeName : String) :
    Option FunctionSpec :=
  match spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) with
  | [fn] => some fn
  | _ => none

structure RuntimeState where
  world : Verity.ContractState
  bindings : List (String × Nat)

inductive StmtResult where
  | continue (state : RuntimeState)
  | stop (state : RuntimeState)
  | return (value : Nat) (state : RuntimeState)
  | revert

private def storageArraySetAt : List Verity.Core.Uint256 → Nat → Verity.Core.Uint256 → Option (List Verity.Core.Uint256)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, idx + 1, value => do
      let updatedRest ← storageArraySetAt rest idx value
      some (head :: updatedRest)

private def storageArrayDropLast? : List Verity.Core.Uint256 → Option (List Verity.Core.Uint256)
  | [] => none
  | [_] => some []
  | head :: rest => do
      let updatedRest ← storageArrayDropLast? rest
      some (head :: updatedRest)

private def writeStorageArray (world : Verity.ContractState) (slot : Nat)
    (values : List Verity.Core.Uint256) : Verity.ContractState :=
  { world with
    storageArray := fun s => if s == slot then values else world.storageArray s }

def evalExpr (fields : List Field) (state : RuntimeState) : Expr → Option Nat
  | .literal n => some (wordNormalize n)
  | .param name => some (lookupValue state.bindings name)
  | .storage fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => some (state.world.storage slot).val
      | none => none
  | .storageAddr fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => some (state.world.storageAddr slot).val
      | none => none
  | .storageArrayLength fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
      | _ => none
  | .storageArrayElement fieldName index => do
      let idx ← evalExpr fields state index
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) =>
          match (state.world.storageArray slot)[idx]? with
          | some value => some value.val
          | none => none
      | _ => none
  | .caller => some state.world.sender.val
  | .contractAddress => some state.world.thisAddress.val
  | .chainid => some state.world.chainId.val
  | .msgValue => some state.world.msgValue.val
  | .blockTimestamp => some state.world.blockTimestamp.val
  | .blockNumber => some state.world.blockNumber.val
  | .localVar name => some (lookupValue state.bindings name)
  | .add a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs + rhs).val
  | .sub a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs - rhs).val
  | .mul a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs * rhs).val
  | .div a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs / rhs).val
  | .mod a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs % rhs).val
  | .bitAnd a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.and lhs rhs).val
  | .bitOr a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.or lhs rhs).val
  | .bitXor a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.xor lhs rhs).val
  | .bitNot a => do
      let value ← evalExpr fields state a
      pure (Verity.Core.Uint256.not value).val
  | .eq a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs = rhs)))
  | .ge a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs ≤ lhs)))
  | .gt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs < lhs)))
  | .lt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs < rhs)))
  | .le a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs ≤ rhs)))
  | .logicalAnd a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))
  | .logicalOr a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))
  | .logicalNot a => do
      let value ← evalExpr fields state a
      pure (boolWord (decide (value = 0)))
  | .min a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if lhs ≤ rhs then lhs else rhs)
  | .max a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if rhs ≤ lhs then lhs else rhs)
  | .wMulDown a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure ((lhs * rhs) / wad).val
  | .wDivUp a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure (((lhs * wad) + (rhs - 1)) / rhs).val
  | .mulDivDown a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure ((lhs * rhs) / denom).val
  | .mulDivUp a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure (((lhs * rhs) + (denom - 1)) / denom).val
  | .ite cond thenVal elseVal => do
      let condVal ← evalExpr fields state cond
      if condVal != 0 then
        evalExpr fields state thenVal
      else
        evalExpr fields state elseVal
  | .shl shift value => do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shl shiftVal wordVal).val
  | .shr shift value => do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shr shiftVal wordVal).val
  | _ => none

mutual
  def execStmt (fields : List Field) : RuntimeState → Stmt → StmtResult
    | state, .letVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .assignVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintSlots state.world slots resolved }
        | _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [resolved]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | state, .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | state, .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state index, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | none => .revert
    | state, .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressSlots state.world slots resolved }
        | _, _ => .revert
    | state, .require cond _ =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | state, .return value =>
        match evalExpr fields state value with
        | some resolved => .return resolved state
        | none => .revert
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtList fields state thenBranch
            else
              execStmtList fields state elseBranch
        | none => .revert
    | _, _ => .revert

  def execStmtList (fields : List Field) : RuntimeState → List Stmt → StmtResult
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmt fields state stmt with
        | .continue next => execStmtList fields next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
end

structure SourceContractResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  events : List (List Nat)

structure InternalFunctionResult where
  success : Bool
  returnValue : Option Nat
  world : Verity.ContractState

def revertedResult (spec : CompilationModel) (initialWorld : Verity.ContractState) :
    SourceContractResult :=
  { success := false
    returnValue := none
    finalStorage := encodeStorage spec initialWorld
    events := encodeEvents initialWorld.events }

def successResult (spec : CompilationModel) (world : Verity.ContractState) (ret : Option Nat) :
    SourceContractResult :=
  { success := true
    returnValue := ret
    finalStorage := encodeStorage spec world
    events := encodeEvents world.events }

def revertedInternalResult (initialWorld : Verity.ContractState) :
    InternalFunctionResult :=
  { success := false
    returnValue := none
    world := initialWorld }

def successInternalResult (world : Verity.ContractState) (ret : Option Nat) :
    InternalFunctionResult :=
  { success := true
    returnValue := ret
    world := world }

def bindSupportedParams (params : List Param) (args : List Nat) :
    Option (List (String × Nat)) :=
  match params, args with
  | [], _ => some []
  | _ :: _, [] => none
  | param :: rest, arg :: restArgs => do
      let value ← decodeSupportedParamWord param.ty arg
      let bindings ← bindSupportedParams rest restArgs
      pure ((param.name, value) :: bindings)

def withTransactionContext (world : Verity.ContractState) (tx : IRTransaction) :
    Verity.ContractState :=
  { world with
    sender := Verity.wordToAddress tx.sender
    thisAddress := Verity.wordToAddress tx.thisAddress
    msgValue := tx.msgValue
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId }

def selectorFunctionPairs (spec : CompilationModel) (selectors : List Nat) :
    List (FunctionSpec × Nat) :=
  (selectorDispatchedFunctions spec).zip selectors

def findFunctionBySelector (spec : CompilationModel) (selectors : List Nat) (selector : Nat) :
    Option FunctionSpec :=
  (selectorFunctionPairs spec selectors).find? (fun entry => entry.2 == selector) |>.map Prod.fst

def interpretFunction (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) : SourceContractResult :=
  let worldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  match bindSupportedParams fn.params tx.args with
  | none => revertedResult spec worldWithTx
  | some bindings =>
      match execStmtList fields { world := worldWithTx, bindings := bindings } fn.body with
      | .continue state => successResult spec state.world none
      | .stop state => successResult spec state.world none
      | .return value state => successResult spec state.world (some value)
      | .revert => revertedResult spec worldWithTx

def interpretContract (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) : SourceContractResult :=
  match findFunctionBySelector spec selectors tx.functionSelector with
  | some fn => interpretFunction spec fn tx initialWorld
  | none => revertedResult spec (withTransactionContext initialWorld tx)

mutual
  /-- Spec-aware source semantics for the next helper-proof step.
  This is additive: the current generic theorem still reasons about the
  helper-free `interpretFunction` / `interpretContract` path above. -/
  def evalExprWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : Expr → Option Nat
    | .literal n => some (wordNormalize n)
    | .param name => some (lookupValue state.bindings name)
    | .storage fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some (_, slot) => some (state.world.storage slot).val
        | none => none
    | .storageAddr fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some (_, slot) => some (state.world.storageAddr slot).val
        | none => none
    | .storageArrayLength fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
        | _ => none
    | .storageArrayElement fieldName index => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match (state.world.storageArray slot)[idx]? with
            | some value => some value.val
            | none => none
        | _ => none
    | .caller => some state.world.sender.val
    | .contractAddress => some state.world.thisAddress.val
    | .chainid => some state.world.chainId.val
    | .msgValue => some state.world.msgValue.val
    | .blockTimestamp => some state.world.blockTimestamp.val
    | .blockNumber => some state.world.blockNumber.val
    | .localVar name => some (lookupValue state.bindings name)
    | .add a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs + rhs).val
    | .sub a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs - rhs).val
    | .mul a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs * rhs).val
    | .div a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs / rhs).val
    | .mod a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs % rhs).val
    | .bitAnd a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.and lhs rhs).val
    | .bitOr a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.or lhs rhs).val
    | .bitXor a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.xor lhs rhs).val
    | .bitNot a => do
        let value ← evalExprWithHelpers spec fields fuel state a
        pure (Verity.Core.Uint256.not value).val
    | .eq a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs = rhs)))
    | .ge a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (rhs ≤ lhs)))
    | .gt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (rhs < lhs)))
    | .lt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs < rhs)))
    | .le a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs ≤ rhs)))
    | .logicalAnd a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))
    | .logicalOr a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))
    | .logicalNot a => do
        let value ← evalExprWithHelpers spec fields fuel state a
        pure (boolWord (decide (value = 0)))
    | .min a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (if lhs ≤ rhs then lhs else rhs)
    | .max a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (if rhs ≤ lhs then lhs else rhs)
    | .wMulDown a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let wad : Verity.Core.Uint256 := 1000000000000000000
        pure ((lhs * rhs) / wad).val
    | .wDivUp a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let wad : Verity.Core.Uint256 := 1000000000000000000
        pure (((lhs * wad) + (rhs - 1)) / rhs).val
    | .mulDivDown a b c => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let denom : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state c
        pure ((lhs * rhs) / denom).val
    | .mulDivUp a b c => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let denom : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state c
        pure (((lhs * rhs) + (denom - 1)) / denom).val
    | .ite cond thenVal elseVal => do
        let condVal ← evalExprWithHelpers spec fields fuel state cond
        if condVal != 0 then
          evalExprWithHelpers spec fields fuel state thenVal
        else
          evalExprWithHelpers spec fields fuel state elseVal
    | .shl shift value => do
        let shiftVal ← evalExprWithHelpers spec fields fuel state shift
        let wordVal ← evalExprWithHelpers spec fields fuel state value
        pure (Verity.Core.Uint256.shl shiftVal wordVal).val
    | .shr shift value => do
        let shiftVal ← evalExprWithHelpers spec fields fuel state shift
        let wordVal ← evalExprWithHelpers spec fields fuel state value
        pure (Verity.Core.Uint256.shr shiftVal wordVal).val
    | .internalCall calleeName args =>
        match fuel with
        | 0 => none
        | fuel + 1 => do
            let argVals ← evalExprListWithHelpers spec fields (fuel + 1) state args
            let callee ← findUniqueInternalFunction? spec calleeName
            let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
            if hresult.success then hresult.returnValue else none
    | _ => none

  def evalExprListWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : List Expr → Option (List Nat)
    | [] => some []
    | expr :: rest => do
        let value ← evalExprWithHelpers spec fields fuel state expr
        let values ← evalExprListWithHelpers spec fields fuel state rest
        pure (value :: values)

  def execStmtWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat) : RuntimeState → Stmt → StmtResult
    | state, .letVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .assignVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintSlots state.world slots resolved }
        | _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [resolved]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | state, .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | state, .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName,
            evalExprWithHelpers spec fields fuel state index,
            evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _, _, _ => .revert
    | state, .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressSlots state.world slots resolved }
        | _, _ => .revert
    | state, .require cond _ =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | state, .return value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved => .return resolved state
        | none => .revert
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtListWithHelpers spec fields fuel state thenBranch
            else
              execStmtListWithHelpers spec fields fuel state elseBranch
        | none => .revert
    | state, .internalCall calleeName args =>
        match fuel with
        | 0 => .revert
        | fuel + 1 =>
            match evalExprListWithHelpers spec fields (fuel + 1) state args,
                findUniqueInternalFunction? spec calleeName with
            | some argVals, some callee =>
                let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
                if hresult.success then
                  .continue { state with world := hresult.world }
                else
                  .revert
            | _, _ => .revert
    | state, .internalCallAssign names calleeName args =>
        match fuel with
        | 0 => .revert
        | fuel + 1 =>
            match evalExprListWithHelpers spec fields (fuel + 1) state args,
                findUniqueInternalFunction? spec calleeName with
            | some argVals, some callee =>
                let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
                if hresult.success then
                  match names, hresult.returnValue with
                  | [name], some value =>
                      .continue {
                        world := hresult.world
                        bindings := bindValue state.bindings name value
                      }
                  | _, _ => .revert
                else
                  .revert
            | _, _ => .revert
    | _, _ => .revert

  def execStmtListWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat) : RuntimeState → List Stmt → StmtResult
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmtWithHelpers spec fields fuel state stmt with
        | .continue next => execStmtListWithHelpers spec fields fuel next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert

  def interpretInternalFunctionFuel
      (spec : CompilationModel)
      (fuel : Nat)
      (fn : FunctionSpec)
      (initialWorld : Verity.ContractState)
      (args : List Nat) : InternalFunctionResult :=
    let fields := effectiveFields spec
    match bindInternalArgs fn.params args with
    | none => revertedInternalResult initialWorld
    | some bindings =>
        match execStmtListWithHelpers spec fields fuel { world := initialWorld, bindings := bindings } fn.body with
        | .continue state => successInternalResult state.world none
        | .stop state => successInternalResult state.world none
        | .return value state => successInternalResult state.world (some value)
        | .revert => revertedInternalResult initialWorld
termination_by
  evalExprWithHelpers _ _ fuel _ expr => (fuel, sizeOf expr)
  evalExprListWithHelpers _ _ fuel _ exprs => (fuel, sizeOf exprs)
  execStmtWithHelpers _ _ fuel _ stmt => (fuel, sizeOf stmt)
  execStmtListWithHelpers _ _ fuel _ stmts => (fuel, sizeOf stmts)
  interpretInternalFunctionFuel _ fuel fn _ _ => (fuel, sizeOf fn.body + 1)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Semantic contract attached to an internal-helper summary witness. The summary
is intentionally phrased against the helper-aware source semantics so later
Layer 2 composition lemmas can consume it without changing theorem targets. -/
def InternalHelperSummarySound
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (summary : InternalHelperSummaryContract) : Prop :=
  ∀ fuel initialWorld args,
    let result := interpretInternalFunctionFuel spec fuel fn initialWorld args
    summary.post fuel initialWorld args result.success result.returnValue result.world

/-- The direct-callee summary inventory carried by `SupportedBodyHelperInterface`
becomes a proof interface once each summary contract is proved sound for the
actual helper-aware source semantics. -/
def SupportedBodyHelperSummariesSound
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (hHelpers : SupportedBodyHelperInterface spec fn) : Prop :=
  ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
    InternalHelperSummarySound spec
      (hHelpers.summaryOfCall hmem).callee
      (hHelpers.summaryContractOfCall hmem)

def interpretFunctionWithHelpers
    (spec : CompilationModel)
    (fuel : Nat)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : SourceContractResult :=
  let worldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  match bindSupportedParams fn.params tx.args with
  | none => revertedResult spec worldWithTx
  | some bindings =>
      match execStmtListWithHelpers spec fields fuel { world := worldWithTx, bindings := bindings } fn.body with
      | .continue state => successResult spec state.world none
      | .stop state => successResult spec state.world none
      | .return value state => successResult spec state.world (some value)
      | .revert => revertedResult spec worldWithTx

def interpretContractWithHelpers
    (spec : CompilationModel)
    (selectors : List Nat)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : SourceContractResult :=
  match findFunctionBySelector spec selectors tx.functionSelector with
  | some fn => interpretFunctionWithHelpers spec fuel fn tx initialWorld
  | none => revertedResult spec (withTransactionContext initialWorld tx)

theorem helperSummarySound
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hsound : InternalHelperSummarySound spec fn summary)
    (fuel : Nat)
    (initialWorld : Verity.ContractState)
    (args : List Nat) :
    let result := interpretInternalFunctionFuel spec fuel fn initialWorld args
    summary.post fuel initialWorld args result.success result.returnValue result.world :=
  hsound fuel initialWorld args

theorem helperSummaryPreservesWorldOnSuccess
    {summary : InternalHelperSummaryContract}
    (hpreserve : InternalHelperSummaryPreservesWorldOnSuccess summary)
    {fuel : Nat}
    {initialWorld : Verity.ContractState}
    {args : List Nat}
    {success : Bool}
    {returnValue : Option Nat}
    {finalWorld : Verity.ContractState}
    (hpost : summary.post fuel initialWorld args success returnValue finalWorld)
    (hsuccess : success = true) :
    finalWorld = initialWorld :=
  hpreserve fuel initialWorld args success returnValue finalWorld hpost hsuccess

theorem evalExprWithHelpers_internalCall_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel state.world argVals result.success result.returnValue result.world := by
  simpa [InternalHelperSummarySound] using hsound fuel state.world argVals

theorem evalExprWithHelpers_internalCall_preserves_world
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    (hpreserve : InternalHelperSummaryPreservesWorldOnSuccess summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    result.success = true → result.world = state.world := by
  intro result hsuccess
  exact helperSummaryPreservesWorldOnSuccess hpreserve
    (hpost := evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind) (hsound := hsound) (hargs := hargs))
    hsuccess

theorem execStmtWithHelpers_internalCall_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel state.world argVals result.success result.returnValue result.world := by
  simpa [execStmtWithHelpers, hfind, hargs] using
    evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind)
      (hsound := hsound)
      (hargs := hargs)

theorem execStmtWithHelpers_internalCallAssign_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel state.world argVals result.success result.returnValue result.world := by
  simpa [execStmtWithHelpers, hfind, hargs] using
    evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind)
      (hsound := hsound)
      (hargs := hargs)

theorem SupportedBodyHelperInterface.summarySoundOfCall
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {calleeName : String}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
    (hmem : calleeName ∈ helperCallNames fn) :
    InternalHelperSummarySound spec
      (hHelpers.summaryOfCall hmem).callee
      (hHelpers.summaryContractOfCall hmem) :=
  hsummaries calleeName hmem

theorem SupportedBodyHelperInterface.exprCallSummaryPreservesWorld
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {calleeName : String}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    let hcall : calleeName ∈ helperCallNames fn :=
      exprHelperCallNames_subset_helperCallNames hmem
    InternalHelperSummaryPreservesWorldOnSuccess
      (hHelpers.summaryContractOfCall hcall) :=
  hHelpers.exprSummaryPreservesWorld hmem

structure SupportedFunctionHelperProofs
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (hSupported : SupportedFunction spec fn) : Prop where
  summariesSound :
    SupportedBodyHelperSummariesSound spec fn hSupported.body.calls.helpers

structure SupportedSpecHelperProofs
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) : Prop where
  functionProofs :
    ∀ fn (hfn : fn ∈ selectorDispatchedFunctions spec),
      SupportedFunctionHelperProofs spec fn
        (hSupported.supportedFunctionOfSelectorDispatched hfn)

theorem SupportedSpecHelperProofs.functionSummariesSound
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedBodyHelperSummariesSound spec fn
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers :=
  (hProofs.functionProofs fn hfn).summariesSound

mutual
  theorem evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (expr : Expr)
      (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
      evalExprWithHelpers spec fields fuel state expr = evalExpr fields state expr := by
    induction expr generalizing state with
    | literal n
    | param name
    | storage fieldName
    | storageAddr fieldName
    | storageArrayLength fieldName
    | caller
    | contractAddress
    | chainid
    | msgValue
    | blockTimestamp
    | blockNumber
    | localVar name
    | constructorArg idx
    | blobbasefee
    | calldatasize
    | returndataSize
    | arrayLength name =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface] at *
    | storageArrayElement fieldName index ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface, ih hsurface]
    | add a b ihA ihB
    | sub a b ihA ihB
    | mul a b ihA ihB
    | div a b ihA ihB
    | mod a b ihA ihB
    | bitAnd a b ihA ihB
    | bitOr a b ihA ihB
    | bitXor a b ihA ihB
    | eq a b ihA ihB
    | ge a b ihA ihB
    | gt a b ihA ihB
    | lt a b ihA ihB
    | le a b ihA ihB
    | logicalAnd a b ihA ihB
    | logicalOr a b ihA ihB
    | min a b ihA ihB
    | max a b ihA ihB
    | wMulDown a b ihA ihB
    | wDivUp a b ihA ihB
    | shl a b ihA ihB
    | shr a b ihA ihB =>
        have hA := (Bool.or_eq_false.mp hsurface).1
        have hB := (Bool.or_eq_false.mp hsurface).2
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface,
          ihA hA, ihB hB]
    | bitNot a ih
    | logicalNot a ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface, ih hsurface]
    | mulDivDown a b c ihA ihB ihC
    | mulDivUp a b c ihA ihB ihC =>
        have hAB := (Bool.or_eq_false.mp hsurface).1
        have hC := (Bool.or_eq_false.mp hsurface).2
        have hA := (Bool.or_eq_false.mp hAB).1
        have hB := (Bool.or_eq_false.mp hAB).2
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface,
          ihA hA, ihB hB, ihC hC]
    | ite cond thenVal elseVal ihCond ihThen ihElse =>
        have hCondRest := (Bool.or_eq_false.mp hsurface).1
        have hElse := (Bool.or_eq_false.mp hsurface).2
        have hCond := (Bool.or_eq_false.mp hCondRest).1
        have hThen := (Bool.or_eq_false.mp hCondRest).2
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface,
          ihCond hCond, ihThen hThen, ihElse hElse]
    | mapping field key ih
    | mappingUint field key ih
    | arrayElement field key ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface, ih hsurface]
    | mappingChain field keys ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface] at *
    | mappingWord field key offset ih
    | mappingPackedWord field key offset packed ih
    | structMember field key memberName ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface, ih hsurface]
    | mapping2 field key1 key2 ih1 ih2
    | mapping2Word field key1 key2 offset ih1 ih2
    | structMember2 field key1 key2 memberName ih1 ih2 =>
        have h1 := (Bool.or_eq_false.mp hsurface).1
        have h2 := (Bool.or_eq_false.mp hsurface).2
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface,
          ih1 h1, ih2 h2]
    | internalCall calleeName args ih =>
        cases hsurface
    | externalCall calleeName args ih =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface]
    | dynamicBytesEq lhsName rhsName =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface] at *
    | sdiv a b ihA ihB
    | smod a b ihA ihB
    | sgt a b ihA ihB
    | slt a b ihA ihB
    | sar a b ihA ihB
    | signextend a b ihA ihB
    | staticcall a b c d e f ihA ihB ihC ihD ihE ihF
    | delegatecall a b c d e f ihA ihB ihC ihD ihE ihF
    | call a b c d e f g ihA ihB ihC ihD ihE ihF ihG
    | extcodesize a ihA
    | returndataOptionalBoolAt a ihA
    | mload a ihA
    | tload a ihA
    | calldataload a ihA
    | keccak256 a b ihA ihB =>
        simp [evalExprWithHelpers, evalExpr, exprTouchesUnsupportedHelperSurface] at *

  theorem evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (exprs : List Expr)
      (hsurface : exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true) :
      evalExprListWithHelpers spec fields fuel state exprs =
        exprs.mapM (evalExpr fields state) := by
    induction exprs with
    | nil =>
        simp [evalExprListWithHelpers]
    | cons expr rest ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hsurface
        rcases hsurface with ⟨hexpr, hrest⟩
        simp [evalExprListWithHelpers,
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
            (spec := spec) (fields := fields) (fuel := fuel) (state := state)
            (expr := expr) (by simpa using hexpr),
          ih hrest]

  theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (stmt : Stmt)
      (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
      execStmtWithHelpers spec fields fuel state stmt = execStmt fields state stmt := by
    cases stmt <;>
      simp [execStmtWithHelpers, execStmt, stmtTouchesUnsupportedHelperSurface,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed,
        evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed] at hsurface ⊢
    case ite cond thenBranch elseBranch =>
      have hCondRest := (Bool.or_eq_false.mp hsurface).1
      have hElse := (Bool.or_eq_false.mp hsurface).2
      have hCond := (Bool.or_eq_false.mp hCondRest).1
      have hThen := (Bool.or_eq_false.mp hCondRest).2
      simp [evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
          (spec := spec) (fields := fields) (fuel := fuel) (state := state)
          (expr := cond) hCond,
        execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
          (spec := spec) (fields := fields) (fuel := fuel) (state := state)
          (stmts := thenBranch) hThen,
        execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
          (spec := spec) (fields := fields) (fuel := fuel) (state := state)
          (stmts := elseBranch) hElse,
        execStmtWithHelpers, execStmt, stmtTouchesUnsupportedHelperSurface]

theorem execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (stmts : List Stmt)
      (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
      execStmtListWithHelpers spec fields fuel state stmts = execStmtList fields state stmts := by
    induction stmts generalizing state with
    | nil =>
        simp [execStmtListWithHelpers, execStmtList, stmtListTouchesUnsupportedHelperSurface]
    | cons stmt rest ih =>
        have hStmt := (Bool.or_eq_false.mp hsurface).1
        have hRest := (Bool.or_eq_false.mp hsurface).2
        simp [execStmtListWithHelpers, execStmtList,
          execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
            (spec := spec) (fields := fields) (fuel := fuel) (state := state)
            (stmt := stmt) hStmt]
        cases hstep : execStmt fields state stmt <;> simp [hstep, ih hRest]
end

/-- Exact source-side helper-composition target for a statement list: the
helper-aware source semantics should conservatively extend the legacy
helper-free semantics on the given runtime state. Future helper-summary/rank
consumption should target this proposition directly rather than the temporary
syntactic helper-surface gate. -/
def ExecStmtListWithHelpersConservativeExtensionGoal
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt) : Prop :=
  execStmtListWithHelpers spec fields fuel state stmts =
    execStmtList fields state stmts

theorem execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    ExecStmtListWithHelpersConservativeExtensionGoal spec fields fuel state stmts :=
  execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
    (spec := spec)
    (fields := fields)
    (fuel := fuel)
    (state := state)
    (stmts := stmts)
    hsurface

theorem interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fuel : Nat)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hsurface : stmtListTouchesUnsupportedHelperSurface fn.body = false) :
    interpretFunctionWithHelpers spec fuel fn tx initialWorld =
      interpretFunction spec fn tx initialWorld := by
  simp [interpretFunctionWithHelpers, interpretFunction]
  split <;> simp
  rename_i bindings hbind
  exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
    (spec := spec)
    (fields := effectiveFields spec)
    (fuel := fuel)
    (state := { world := withTransactionContext initialWorld tx, bindings := bindings })
    (stmts := fn.body)
    hsurface

theorem findFunctionBySelector_mem_selectorDispatchedFunctions
    {spec : CompilationModel}
    {selectors : List Nat}
    {selector : Nat}
    {fn : FunctionSpec}
    (hfind : findFunctionBySelector spec selectors selector = some fn) :
    fn ∈ selectorDispatchedFunctions spec := by
  unfold findFunctionBySelector at hfind
  rcases hentry :
      List.find? (fun entry => entry.2 == selector) (selectorFunctionPairs spec selectors) with
    (_ | entry) <;> simp [hentry] at hfind
  cases entry with
  | mk foundFn foundSelector =>
      cases hfind
      simpa [selectorFunctionPairs] using
        (List.mem_map_of_mem Prod.fst (List.mem_of_find?_some hentry))

theorem interpretContractWithHelpers_eq_interpretContract_of_supportedSpec
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    interpretContractWithHelpers spec selectors fuel tx initialWorld =
      interpretContract spec selectors tx initialWorld := by
  unfold interpretContractWithHelpers interpretContract
  split
  · rename_i fn hfind
    have hfn : fn ∈ selectorDispatchedFunctions spec :=
      findFunctionBySelector_mem_selectorDispatchedFunctions hfind
    have hfnModel : fn ∈ spec.functions := List.mem_of_mem_filter hfn
    exact interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := fuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      ((hSupported.functions fn hfnModel).body.calls.helpers.surfaceClosed)
  · rfl

end SourceSemantics

/-- Whole-contract source-side semantics for the first generic Layer 2 fragment.
The observable result intentionally mirrors `interpretIR`: selector dispatch,
scalar parameter decoding, success/revert, rollback on revert, return value,
and encoded storage/event observations. -/
def sourceContractSemantics (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContract spec selectors tx initialWorld

def sourceContractSemanticsWithHelpers (spec : CompilationModel) (selectors : List Nat)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContractWithHelpers spec selectors fuel tx initialWorld

def supportedSourceFunctionSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

def supportedSourceContractSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

theorem sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpec
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    sourceContractSemanticsWithHelpers spec selectors fuel tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpec
    hSupported fuel tx initialWorld

theorem supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceFunctionSemantics spec selectors hSupported fn tx initialWorld =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  unfold supportedSourceFunctionSemantics
  exact SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    (spec := spec)
    (fuel := hSupported.helperFuel)
    (fn := fn)
    (tx := tx)
    (initialWorld := initialWorld)
    ((hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.surfaceClosed)

theorem supportedSourceContractSemantics_eq_sourceContractSemantics
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceContractSemantics spec selectors hSupported tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpec
    hSupported hSupported.helperFuel tx initialWorld

example :
    (sourceContractSemantics simpleStorageSupportedSpecModel [0x2e64cec1]
      { sender := 7, functionSelector := 0x2e64cec1, args := [] }
      Verity.defaultState).success = true := by
  decide

example :
    (sourceContractSemantics counterSupportedSpecModel
      [0xa87d942c]
      { sender := 9, functionSelector := 0xa87d942c, args := [] }
      Verity.defaultState).returnValue = some 42 := by
  decide

private def storageArraySourceSpec : CompilationModel :=
  { name := "StorageArraySource"
    fields := [{ name := "queue", ty := .dynamicArray .uint256, «slot» := some 7 }]
    constructor := none
    functions :=
      [ { name := "length"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayLength "queue")] }
      , { name := "first"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayElement "queue" (.literal 0))] }
      , { name := "push"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.storageArrayPush "queue" (.param "value"), .stop] }
      , { name := "write0"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.setStorageArrayElement "queue" (.literal 0) (.param "value"), .stop] }
      , { name := "pop"
          params := []
          returnType := none
          body := [Stmt.storageArrayPop "queue", .stop] } ] }

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x11111111, args := [] }
      { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }).returnValue = some 2 := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }).returnValue = some 11 := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x33333333, args := [23] }
      { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }).finalStorage
        (Compiler.Proofs.solidityMappingSlot 7 2) = 23 := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x44444444, args := [29] }
      { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }).finalStorage
        (Compiler.Proofs.solidityMappingSlot 7 0) = 29 := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }).finalStorage 7 = 1 := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      Verity.defaultState).success = false := by
  decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      Verity.defaultState).success = false := by
  decide
end Compiler.Proofs.IRGeneration
