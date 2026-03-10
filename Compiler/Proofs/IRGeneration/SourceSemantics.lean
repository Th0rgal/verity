import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.IRInterpreter
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

def encodeStorageAt (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlot fields slot with
  | some field =>
      if fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else
        (world.storage slot).val
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

def evalExpr (fields : List Field) (state : RuntimeState) : Expr → Nat
  | .literal n => wordNormalize n
  | .param name => lookupValue state.bindings name
  | .storage fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => (state.world.storage slot).val
      | none => 0
  | .storageAddr fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => (state.world.storageAddr slot).val
      | none => 0
  | .caller => state.world.sender.val
  | .contractAddress => state.world.thisAddress.val
  | .chainid => state.world.chainId.val
  | .msgValue => state.world.msgValue.val
  | .blockTimestamp => state.world.blockTimestamp.val
  | .blockNumber => state.world.blockNumber.val
  | .localVar name => lookupValue state.bindings name
  | .add a b => (((evalExpr fields state a : Verity.Core.Uint256) +
      (evalExpr fields state b : Verity.Core.Uint256)) : Verity.Core.Uint256).val
  | .sub a b => (((evalExpr fields state a : Verity.Core.Uint256) -
      (evalExpr fields state b : Verity.Core.Uint256)) : Verity.Core.Uint256).val
  | .mul a b => (((evalExpr fields state a : Verity.Core.Uint256) *
      (evalExpr fields state b : Verity.Core.Uint256)) : Verity.Core.Uint256).val
  | .div a b => (((evalExpr fields state a : Verity.Core.Uint256) /
      (evalExpr fields state b : Verity.Core.Uint256)) : Verity.Core.Uint256).val
  | .mod a b => (((evalExpr fields state a : Verity.Core.Uint256) %
      (evalExpr fields state b : Verity.Core.Uint256)) : Verity.Core.Uint256).val
  | .bitAnd a b =>
      (Verity.Core.Uint256.and (evalExpr fields state a) (evalExpr fields state b)).val
  | .bitOr a b =>
      (Verity.Core.Uint256.or (evalExpr fields state a) (evalExpr fields state b)).val
  | .bitXor a b =>
      (Verity.Core.Uint256.xor (evalExpr fields state a) (evalExpr fields state b)).val
  | .bitNot a =>
      (Verity.Core.Uint256.not (evalExpr fields state a)).val
  | .eq a b => boolWord (decide (evalExpr fields state a = evalExpr fields state b))
  | .ge a b => boolWord (decide (evalExpr fields state b ≤ evalExpr fields state a))
  | .gt a b => boolWord (decide (evalExpr fields state b < evalExpr fields state a))
  | .lt a b => boolWord (decide (evalExpr fields state a < evalExpr fields state b))
  | .le a b => boolWord (decide (evalExpr fields state a ≤ evalExpr fields state b))
  | .logicalAnd a b =>
      boolWord (decide (evalExpr fields state a != 0) &&
        decide (evalExpr fields state b != 0))
  | .logicalOr a b =>
      boolWord (decide (evalExpr fields state a != 0) ||
        decide (evalExpr fields state b != 0))
  | .logicalNot a => boolWord (decide (evalExpr fields state a = 0))
  | .min a b =>
      let lhs := evalExpr fields state a
      let rhs := evalExpr fields state b
      if lhs ≤ rhs then lhs else rhs
  | .max a b =>
      let lhs := evalExpr fields state a
      let rhs := evalExpr fields state b
      if rhs ≤ lhs then lhs else rhs
  | .wMulDown a b =>
      let lhs : Verity.Core.Uint256 := evalExpr fields state a
      let rhs : Verity.Core.Uint256 := evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      ((lhs * rhs) / wad).val
  | .wDivUp a b =>
      let lhs : Verity.Core.Uint256 := evalExpr fields state a
      let rhs : Verity.Core.Uint256 := evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      (((lhs * wad) + (rhs - 1)) / rhs).val
  | .mulDivDown a b c =>
      let lhs : Verity.Core.Uint256 := evalExpr fields state a
      let rhs : Verity.Core.Uint256 := evalExpr fields state b
      let denom : Verity.Core.Uint256 := evalExpr fields state c
      ((lhs * rhs) / denom).val
  | .mulDivUp a b c =>
      let lhs : Verity.Core.Uint256 := evalExpr fields state a
      let rhs : Verity.Core.Uint256 := evalExpr fields state b
      let denom : Verity.Core.Uint256 := evalExpr fields state c
      (((lhs * rhs) + (denom - 1)) / denom).val
  | .ite cond thenVal elseVal =>
      if evalExpr fields state cond != 0 then
        evalExpr fields state thenVal
      else
        evalExpr fields state elseVal
  | .shl shift value =>
      (Verity.Core.Uint256.shl (evalExpr fields state shift) (evalExpr fields state value)).val
  | .shr shift value =>
      (Verity.Core.Uint256.shr (evalExpr fields state shift) (evalExpr fields state value)).val
  | _ => 0

mutual
  def execStmt (fields : List Field) : RuntimeState → Stmt → StmtResult
    | state, .letVar name value =>
        .continue { state with bindings := bindValue state.bindings name (evalExpr fields state value) }
    | state, .assignVar name value =>
        .continue { state with bindings := bindValue state.bindings name (evalExpr fields state value) }
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName with
        | some slots =>
            .continue { state with world := writeUintSlots state.world slots (evalExpr fields state value) }
        | none => .revert
    | state, .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName with
        | some slots =>
            .continue { state with world := writeAddressSlots state.world slots (evalExpr fields state value) }
        | none => .revert
    | state, .require cond _ =>
        if evalExpr fields state cond != 0 then .continue state else .revert
    | state, .return value =>
        .return (evalExpr fields state value) state
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        if evalExpr fields state cond != 0 then
          execStmtList fields state thenBranch
        else
          execStmtList fields state elseBranch
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
      { Verity.defaultState with storage := fun slot => if slot = 0 then 11 else 0 }).success = true := by
  decide

example :
    (sourceContractSemantics counterSupportedSpecModel
      [0xd09de08a, 0x2baeceb7, 0xa87d942c]
      { sender := 9, functionSelector := 0xa87d942c, args := [] }
      { Verity.defaultState with storage := fun slot => if slot = 0 then 42 else 0 }).returnValue = some 42 := by
  decide

end Compiler.Proofs.IRGeneration
