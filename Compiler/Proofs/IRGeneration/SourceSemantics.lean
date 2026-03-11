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

end SourceSemantics

/-- Whole-contract source-side semantics for the first generic Layer 2 fragment.
The observable result intentionally mirrors `interpretIR`: selector dispatch,
scalar parameter decoding, success/revert, rollback on revert, return value,
and encoded storage/event observations. -/
def sourceContractSemantics (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContract spec selectors tx initialWorld

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
