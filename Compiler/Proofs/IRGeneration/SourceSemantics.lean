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

def findResolvedFieldAtSlot (fields : List Field) (slot : Nat) : Option Field :=
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

def findDynamicArrayElementAtSlot
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

def writeAddressKeyedMappingSlots
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyAddr := Verity.wordToAddress (key : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let storageNat : Nat → Nat := fun s => (world.storage s).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry current slot key value)
          storageNat
      { world with
        storage := fun s => (storage s : Verity.Core.Uint256)
        storageMap := fun baseSlot addr =>
          if baseSlot == slot && addr == keyAddr then
            word
          else
            world.storageMap baseSlot addr }

def mappingSlotChain (baseSlot : Nat) (keys : List Nat) : Nat :=
  keys.foldl Compiler.Proofs.abstractMappingSlot baseSlot

def writeAddressKeyedMappingChainSlots
    (world : Verity.ContractState) (slots keys : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot => mappingSlotChain slot keys)
  { world with
    storage := fun slot =>
      if targets.contains slot then word else world.storage slot }

def writeAddressKeyedMappingWordSlots
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
  { world with
    storage := fun slot =>
      if targets.contains slot then word else world.storage slot }

def packedWordWrite (current value : Nat) (packed : PackedBits) : Nat :=
  let maskNat := packedMaskNat packed
  let shiftedMaskNat := packedShiftedMaskNat packed
  let packedValue := Verity.Core.Uint256.and value maskNat
  let cleared := Verity.Core.Uint256.and current (Verity.Core.Uint256.not shiftedMaskNat)
  (Verity.Core.Uint256.or cleared (Verity.Core.Uint256.shl packed.offset packedValue)).val

def writeAddressKeyedMappingPackedWordSlots
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
  { world with
    storage := fun slot =>
      if targets.contains slot then
        packedWordWrite (world.storage slot).val value packed
      else
        world.storage slot }

def writeUintKeyedMappingSlots
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyWord : Verity.Core.Uint256 := key
      let word : Verity.Core.Uint256 := value
      let storageNat : Nat → Nat := fun s => (world.storage s).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry current slot key value)
          storageNat
      { world with
        storage := fun s => (storage s : Verity.Core.Uint256)
        storageMapUint := fun baseSlot key' =>
          if baseSlot == slot && key' == keyWord then
            word
          else
            world.storageMapUint baseSlot key' }

def writeAddressKeyedMapping2Slots
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let key1Addr := Verity.wordToAddress (key1 : Verity.Core.Uint256)
      let key2Addr := Verity.wordToAddress (key2 : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let storageNat : Nat → Nat := fun s => (world.storage s).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry
              current
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2
              value)
          storageNat
      { world with
        storage := fun s => (storage s : Verity.Core.Uint256)
        storageMap2 := fun baseSlot addr1 addr2 =>
          if baseSlot == slot && addr1 == key1Addr && addr2 == key2Addr then
            word
          else
            world.storageMap2 baseSlot addr1 addr2 }

def writeAddressKeyedMapping2WordSlots
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot =>
    wordNormalize
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2 + wordOffset))
  { world with
    storage := fun slot =>
      if targets.contains slot then word else world.storage slot }

def decodeSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => some (word &&& (uint8Modulus - 1))
  | .address => some (word &&& Compiler.Constants.addressMask)
  | .bool => some (if word = 0 then 0 else 1)
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

/-- Ceiling-division helper matching Solidity's `Math256.ceilDiv`.
    Factored out so the mutual block's equation-lemma derivation stays simple. -/
private def ceilDivVal (lhs rhs : Verity.Core.Uint256) : Nat :=
  if lhs == 0 then 0 else ((lhs - 1) / rhs + 1).val

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
  | .blobbasefee => some state.world.blobBaseFee.val
  | .calldatasize => some state.world.calldataSize.val
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
  | .ceilDiv a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (ceilDivVal lhs rhs)
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
  | .slt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))
  | .sgt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))
  | .sdiv a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .smod a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .sar a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .signextend a b => do
      let byteIdx ← evalExpr fields state a
      let value ← evalExpr fields state b
      pure (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat byteIdx)
        (Verity.Core.Uint256.ofNat value)).val
  | .mapping field key => do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none
  | .mappingWord field key wordOffset => do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage
            (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
      | none => none
  | .mappingUint field key => do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none
  | .mapping2 field key1 key2 => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field with
      | some slot =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none
  | .mapping2Word field key1 key2 wordOffset => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field with
      | some slot =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
          some (state.world.storage (wordNormalize (outerSlot + wordOffset))).val
      | none => none
  -- mappingChain: deferred — requires List Expr recursion infrastructure
  -- | .mappingChain field keys => ...
  | .structMember field key memberName => do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field, findStructMembers fields field with
      | some slot, some members =>
          match findStructMember members memberName with
          | some member =>
              let targetSlot := wordNormalize
                (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
              let rawWord := (state.world.storage targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none
  | .structMember2 field key1 key2 memberName => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field, findStructMembers fields field with
      | some slot, some members =>
          match findStructMember members memberName with
          | some member =>
              let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
              let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
              let targetSlot := wordNormalize (outerSlot + member.wordOffset)
              let rawWord := (state.world.storage targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none
  | .mappingPackedWord field key wordOffset packed => do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          let targetSlot := wordNormalize
            (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
          let rawWord := (state.world.storage targetSlot).val
          some (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr packed.offset rawWord)
            (packedMaskNat packed)).val
      | none => none
  | _ => none

def evalExprList (fields : List Field) (state : RuntimeState) : List Expr → Option (List Nat)
  | [] => some []
  | expr :: rest => do
      let value ← evalExpr fields state expr
      let values ← evalExprList fields state rest
      pure (value :: values)

private theorem evalExpr_literal
    (fields : List Field)
    (state : RuntimeState)
    (n : Nat) :
    evalExpr fields state (.literal n) = some (wordNormalize n) := rfl

private theorem evalExpr_param
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.param name) = some (lookupValue state.bindings name) := rfl

private theorem evalExpr_localVar
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.localVar name) = some (lookupValue state.bindings name) := rfl

private theorem evalExpr_caller
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .caller = some state.world.sender.val := rfl

private theorem evalExpr_contractAddress
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .contractAddress = some state.world.thisAddress.val := rfl

private theorem evalExpr_chainid
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .chainid = some state.world.chainId.val := rfl

private theorem evalExpr_msgValue
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .msgValue = some state.world.msgValue.val := rfl

private theorem evalExpr_blockTimestamp
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blockTimestamp = some state.world.blockTimestamp.val := rfl

private theorem evalExpr_blockNumber
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blockNumber = some state.world.blockNumber.val := rfl

private theorem evalExpr_storage
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
    evalExpr fields state (.storage fieldName) =
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => some (state.world.storage slot).val
      | none => none := rfl

private theorem evalExpr_storageAddr
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
    evalExpr fields state (.storageAddr fieldName) =
      match findFieldWithResolvedSlot fields fieldName with
      | some (_, slot) => some (state.world.storageAddr slot).val
      | none => none := rfl

private theorem evalExpr_storageArrayLength
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
    evalExpr fields state (.storageArrayLength fieldName) =
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
      | _ => none := rfl

private theorem evalExpr_constructorArg
    (fields : List Field)
    (state : RuntimeState)
    (idx : Nat) :
    evalExpr fields state (.constructorArg idx) = none := rfl

private theorem evalExpr_blobbasefee
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blobbasefee = some state.world.blobBaseFee.val := rfl

private theorem evalExpr_calldatasize
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .calldatasize = some state.world.calldataSize.val := rfl

private theorem evalExpr_returndataSize
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .returndataSize = none := rfl

private theorem evalExpr_arrayLength
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.arrayLength name) = none := rfl

private theorem evalExpr_dynamicBytesEq
    (fields : List Field)
    (state : RuntimeState)
    (lhsName rhsName : String) :
    evalExpr fields state (.dynamicBytesEq lhsName rhsName) = none := rfl

private theorem evalExpr_externalCall
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (args : List Expr) :
    evalExpr fields state (.externalCall name args) = none := rfl

private theorem evalExpr_mload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.mload a) = none := rfl

private theorem evalExpr_tload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.tload a) = none := rfl

private theorem evalExpr_calldataload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.calldataload a) = none := rfl

private theorem evalExpr_extcodesize
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.extcodesize a) = none := rfl

private theorem evalExpr_returndataOptionalBoolAt
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.returndataOptionalBoolAt a) = none := rfl

private theorem evalExpr_keccak256
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.keccak256 a b) = none := rfl

private theorem evalExpr_call
    (fields : List Field)
    (state : RuntimeState)
    (g t v io is oo os : Expr) :
    evalExpr fields state (.call g t v io is oo os) = none := rfl

private theorem evalExpr_staticcall
    (fields : List Field)
    (state : RuntimeState)
    (g t io is oo os : Expr) :
    evalExpr fields state (.staticcall g t io is oo os) = none := rfl

private theorem evalExpr_delegatecall
    (fields : List Field)
    (state : RuntimeState)
    (g t io is oo os : Expr) :
    evalExpr fields state (.delegatecall g t io is oo os) = none := rfl

private theorem evalExpr_add
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.add a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs + rhs).val) := rfl

private theorem evalExpr_sub
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sub a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs - rhs).val) := rfl

private theorem evalExpr_mul
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.mul a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs * rhs).val) := rfl

private theorem evalExpr_div
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.div a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs / rhs).val) := rfl

private theorem evalExpr_mod
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.mod a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs % rhs).val) := rfl

private theorem evalExpr_eq
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.eq a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs = rhs)))) := rfl

private theorem evalExpr_ge
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.ge a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs ≤ lhs)))) := rfl

private theorem evalExpr_gt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.gt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs < lhs)))) := rfl

private theorem evalExpr_lt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.lt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs < rhs)))) := rfl

private theorem evalExpr_le
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.le a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs ≤ rhs)))) := rfl

private theorem evalExpr_logicalAnd
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.logicalAnd a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))) := rfl

private theorem evalExpr_logicalOr
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.logicalOr a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))) := rfl

private theorem evalExpr_sdiv
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sdiv a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_smod
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.smod a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_sgt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sgt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))) := rfl

private theorem evalExpr_slt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.slt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))) := rfl

private theorem evalExpr_bitAnd
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitAnd a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.and lhs rhs).val) := rfl

private theorem evalExpr_bitOr
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitOr a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.or lhs rhs).val) := rfl

private theorem evalExpr_bitXor
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitXor a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.xor lhs rhs).val) := rfl

private theorem evalExpr_bitNot
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.bitNot a) = (do
      let value ← evalExpr fields state a
      pure (Verity.Core.Uint256.not value).val) := rfl

private theorem evalExpr_shl
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.shl shift value) = (do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shl shiftVal wordVal).val) := rfl

private theorem evalExpr_shr
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.shr shift value) = (do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shr shiftVal wordVal).val) := rfl

private theorem evalExpr_sar
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.sar shift value) = (do
      let lhs ← evalExpr fields state shift
      let rhs ← evalExpr fields state value
      pure (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_signextend
    (fields : List Field)
    (state : RuntimeState)
    (byteIndex value : Expr) :
    evalExpr fields state (.signextend byteIndex value) = (do
      let b ← evalExpr fields state byteIndex
      let v ← evalExpr fields state value
      pure (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat b)
        (Verity.Core.Uint256.ofNat v)).val) := rfl

private theorem evalExpr_logicalNot
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.logicalNot a) = (do
      let value ← evalExpr fields state a
      pure (boolWord (decide (value = 0)))) := rfl

private theorem evalExpr_min
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.min a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if lhs ≤ rhs then lhs else rhs)) := rfl

private theorem evalExpr_max
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.max a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if rhs ≤ lhs then lhs else rhs)) := rfl

private theorem evalExpr_wMulDown
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.wMulDown a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure ((lhs * rhs) / wad).val) := rfl

private theorem evalExpr_wDivUp
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.wDivUp a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure (((lhs * wad) + (rhs - 1)) / rhs).val) := rfl

private theorem evalExpr_mapping
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr) :
    evalExpr fields state (.mapping field key) = (do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none) := rfl

private theorem evalExpr_mappingUint
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr) :
    evalExpr fields state (.mappingUint field key) = (do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none) := rfl

private theorem evalExpr_arrayElement
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr) :
    evalExpr fields state (.arrayElement name index) = none := rfl

private theorem evalExpr_mappingWord
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.mappingWord field key wordOffset) = (do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          some (state.world.storage
            (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
      | none => none) := rfl

private theorem evalExpr_mappingPackedWord
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (wordOffset : Nat)
    (packed : PackedBits) :
    evalExpr fields state (.mappingPackedWord field key wordOffset packed) = (do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field with
      | some slot =>
          let targetSlot := wordNormalize
            (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
          let rawWord := (state.world.storage targetSlot).val
          some (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr packed.offset rawWord)
            (packedMaskNat packed)).val
      | none => none) := rfl

private theorem evalExpr_structMember
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (memberName : String) :
    evalExpr fields state (.structMember field key memberName) = (do
      let keyVal ← evalExpr fields state key
      match findFieldSlot fields field, findStructMembers fields field with
      | some slot, some members =>
          match findStructMember members memberName with
          | some member =>
              let targetSlot := wordNormalize
                (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
              let rawWord := (state.world.storage targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none) := rfl

private theorem evalExpr_storageArrayElement
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String)
    (index : Expr) :
    evalExpr fields state (.storageArrayElement fieldName index) = (do
      let idx ← evalExpr fields state index
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) =>
          match (state.world.storageArray slot)[idx]? with
          | some value => some value.val
          | none => none
      | _ => none) := rfl

private theorem evalExpr_mapping2
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr) :
    evalExpr fields state (.mapping2 field key1 key2) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field with
      | some slot =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (state.world.storage (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none) := rfl

private theorem evalExpr_mapping2Word
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.mapping2Word field key1 key2 wordOffset) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field with
      | some slot =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
          some (state.world.storage (wordNormalize (outerSlot + wordOffset))).val
      | none => none) := rfl

private theorem evalExpr_structMember2
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr)
    (memberName : String) :
    evalExpr fields state (.structMember2 field key1 key2 memberName) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldSlot fields field, findStructMembers fields field with
      | some slot, some members =>
          match findStructMember members memberName with
          | some member =>
              let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
              let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
              let targetSlot := wordNormalize (outerSlot + member.wordOffset)
              let rawWord := (state.world.storage targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none) := rfl

private theorem evalExpr_ceilDiv
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.ceilDiv a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (ceilDivVal lhs rhs)) := rfl

private theorem evalExpr_mulDivDown
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDivDown a b c) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure ((lhs * rhs) / denom).val) := rfl

private theorem evalExpr_mulDivUp
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDivUp a b c) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure (((lhs * rhs) + (denom - 1)) / denom).val) := rfl

private theorem evalExpr_ite
    (fields : List Field)
    (state : RuntimeState)
    (cond thenVal elseVal : Expr) :
    evalExpr fields state (.ite cond thenVal elseVal) = (do
      let condVal ← evalExpr fields state cond
      if condVal != 0 then
        evalExpr fields state thenVal
      else
        evalExpr fields state elseVal) := rfl

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
    | state, .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingSlots state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordSlots
                     state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | state, .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordSlots
                      state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | state, .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordSlots
                        state.world slots resolvedKey wordOffset resolved }
            | _ => .revert
        | _, _, _, _ => .revert
    | state, .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2Slots
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      resolved }
        | _, _, _, _ => .revert
    | state, .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordSlots
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      wordOffset
                      resolved }
        | _, _, _, _ => .revert
    | state, .setStructMember2 fieldName key1 key2 memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordSlots
                        state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | _ => .revert
        | _, _, _, _, _ => .revert
    | state, .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingSlots state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprList fields state keys,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainSlots
                    state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [(resolved : Verity.Core.Uint256)]
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
        | _, _, _ => .revert
    | state, .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressSlots state.world slots resolved }
        | _, _ => .revert
    | state, .mstore offset value =>
        match evalExpr fields state offset, evalExpr fields state value with
        | some _, some _ => .continue state
        | _, _ => .revert
    | state, .tstore offset value =>
        match evalExpr fields state offset, evalExpr fields state value with
        | some resolvedOffset, some resolvedValue =>
            .continue {
              state with
              world := {
                state.world with
                transientStorage := fun o =>
                  if o = resolvedOffset then resolvedValue else state.world.transientStorage o
              }
            }
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
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    calldataSize := Verity.Core.Uint256.ofNat (4 + tx.args.length * 32) }

theorem findDynamicArrayElementAtSlot_withTransactionContext
    (fields : List Field)
    (world : Verity.ContractState)
    (tx : IRTransaction)
    (slot : Nat) :
    findDynamicArrayElementAtSlot fields (withTransactionContext world tx) slot =
      findDynamicArrayElementAtSlot fields world slot := by
  unfold findDynamicArrayElementAtSlot
  suffices
      ∀ remaining idx,
        findDynamicArrayElementAtSlot.go (withTransactionContext world tx) slot remaining idx =
          findDynamicArrayElementAtSlot.go world slot remaining idx by
    simpa using this fields 0
  intro remaining idx
  induction remaining generalizing idx with
  | nil =>
      rfl
  | cons field rest ih =>
      cases hty : field.ty with
      | uint256 =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | address =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | dynamicArray elemType =>
          cases hscan :
              findDynamicArrayElementAtSlot.scanElements slot
                (field.slot.getD idx)
                (world.storageArray (field.slot.getD idx)) 0 with
          | none =>
              simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty, hscan] using
                ih (idx + 1)
          | some value =>
              simp [findDynamicArrayElementAtSlot.go, withTransactionContext, hty, hscan]
      | mappingTyped mt =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | mappingStruct keyType members =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | mappingStruct2 outerKey innerKey members =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)

theorem findDynamicArrayElementAtSlot_congr_storageArray
    (fields : List Field)
    (world1 world2 : Verity.ContractState)
    (slot : Nat)
    (h_storageArray : world1.storageArray = world2.storageArray) :
    findDynamicArrayElementAtSlot fields world1 slot =
      findDynamicArrayElementAtSlot fields world2 slot := by
  unfold findDynamicArrayElementAtSlot
  suffices
      ∀ remaining idx,
        findDynamicArrayElementAtSlot.go world1 slot remaining idx =
          findDynamicArrayElementAtSlot.go world2 slot remaining idx by
    simpa using this fields 0
  intro remaining idx
  induction remaining generalizing idx with
  | nil =>
      rfl
  | cons field rest ih =>
      cases hty : field.ty with
      | uint256 =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | address =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | dynamicArray elemType =>
          cases hscan :
              findDynamicArrayElementAtSlot.scanElements slot
                (field.slot.getD idx)
                (world2.storageArray (field.slot.getD idx)) 0 with
          | none =>
              simp only [findDynamicArrayElementAtSlot.go, hty, h_storageArray, hscan]
              exact ih (idx + 1)
          | some value =>
              simp [findDynamicArrayElementAtSlot.go, hty, h_storageArray, hscan]
      | mappingTyped mt =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | mappingStruct keyType members =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | mappingStruct2 outerKey innerKey members =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)

theorem encodeStorageAt_congr
    {fields : List Field}
    {world1 world2 : Verity.ContractState}
    {slot : Nat}
    (h_storage : world1.storage slot = world2.storage slot)
    (h_storageAddr : world1.storageAddr slot = world2.storageAddr slot)
    (h_storageArray : world1.storageArray = world2.storageArray) :
    encodeStorageAt fields world1 slot = encodeStorageAt fields world2 slot := by
  unfold encodeStorageAt
  split
  · simp [h_storage, h_storageAddr, h_storageArray]
  · rw [findDynamicArrayElementAtSlot_congr_storageArray fields world1 world2 slot h_storageArray]
    simp [h_storage]

@[simp] theorem encodeStorageAt_withTransactionContext
    (fields : List Field)
    (world : Verity.ContractState)
    (tx : IRTransaction)
    (slot : Nat) :
    encodeStorageAt fields (withTransactionContext world tx) slot =
      encodeStorageAt fields world slot := by
  unfold encodeStorageAt
  split
  · simp [withTransactionContext]
  · rw [findDynamicArrayElementAtSlot_withTransactionContext]
    simp [withTransactionContext]

@[simp] theorem encodeStorage_withTransactionContext
    (spec : CompilationModel)
    (world : Verity.ContractState)
    (tx : IRTransaction) :
    encodeStorage spec (withTransactionContext world tx) =
      encodeStorage spec world := by
  funext slot
  simpa [encodeStorage] using
    encodeStorageAt_withTransactionContext (effectiveFields spec) world tx slot

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

-- The ceilDiv case pushes the equation-compiler's `simp` past 200 000 heartbeats.
set_option maxHeartbeats 400000 in
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
    | .blobbasefee => some state.world.blobBaseFee.val
    | .calldatasize => some state.world.calldataSize.val
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
    | .ceilDiv a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (ceilDivVal lhs rhs)
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
    | .slt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))
    | .sgt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))
    | .sdiv a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.div
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .smod a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.mod
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .sar a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.sar
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .signextend a b => do
        let byteIdx ← evalExprWithHelpers spec fields fuel state a
        let value ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.signextend
          (Verity.Core.Uint256.ofNat byteIdx)
          (Verity.Core.Uint256.ofNat value)).val
    | .mapping field key => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldSlot fields field with
        | some slot =>
            some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
        | none => none
    | .mappingWord field key wordOffset => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldSlot fields field with
        | some slot =>
            some (state.world.storage
              (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
        | none => none
    | .mappingUint field key => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldSlot fields field with
        | some slot =>
            some (state.world.storage (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
        | none => none
    | .mapping2 field key1 key2 => do
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldSlot fields field with
        | some slot =>
            let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
            some (state.world.storage (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
        | none => none
    | .mapping2Word field key1 key2 wordOffset => do
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldSlot fields field with
        | some slot =>
            let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
            let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
            some (state.world.storage (wordNormalize (outerSlot + wordOffset))).val
        | none => none
    | .mappingPackedWord field key wordOffset packed => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldSlot fields field with
        | some slot =>
            let targetSlot := wordNormalize
              (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
            let rawWord := (state.world.storage targetSlot).val
            some (Verity.Core.Uint256.and
              (Verity.Core.Uint256.shr packed.offset rawWord)
              (packedMaskNat packed)).val
        | none => none
    | .structMember field key memberName => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldSlot fields field, findStructMembers fields field with
        | some slot, some members =>
            match findStructMember members memberName with
            | some member =>
                let targetSlot := wordNormalize
                  (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
                let rawWord := (state.world.storage targetSlot).val
                match member.packed with
                | none => some rawWord
                | some packed =>
                    some (Verity.Core.Uint256.and
                      (Verity.Core.Uint256.shr packed.offset rawWord)
                      (packedMaskNat packed)).val
            | none => none
        | _, _ => none
    | .structMember2 field key1 key2 memberName => do
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldSlot fields field, findStructMembers fields field with
        | some slot, some members =>
            match findStructMember members memberName with
            | some member =>
                let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
                let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
                let targetSlot := wordNormalize (outerSlot + member.wordOffset)
                let rawWord := (state.world.storage targetSlot).val
                match member.packed with
                | none => some rawWord
                | some packed =>
                    some (Verity.Core.Uint256.and
                      (Verity.Core.Uint256.shr packed.offset rawWord)
                      (packedMaskNat packed)).val
            | none => none
        | _, _ => none
    | .internalCall calleeName args =>
        match fuel with
        | 0 => none
        | fuel + 1 => do
            let argVals ← evalExprListWithHelpers spec fields (fuel + 1) state args
            let callee ← findUniqueInternalFunction? spec calleeName
            let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
            if hresult.success then hresult.returnValue else none
    | _ => none
  termination_by expr => (fuel, sizeOf expr)
  decreasing_by all_goals (simp_wf; omega)
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
  termination_by exprs => (fuel, sizeOf exprs)
  decreasing_by all_goals (simp_wf; omega)
  def execStmtWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : Stmt → StmtResult
    | .letVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | .assignVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintSlots state.world slots resolved }
        | _, _ => .revert
    | .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingSlots state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordSlots
                     state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordSlots
                      state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordSlots
                        state.world slots resolvedKey wordOffset resolved }
            | _ => .revert
        | _, _, _, _ => .revert
    | .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2Slots
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      resolved }
        | _, _, _, _ => .revert
    | .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordSlots
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      wordOffset
                      resolved }
        | _, _, _, _ => .revert
    | .setStructMember2 fieldName key1 key2 memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordSlots
                        state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | _ => .revert
        | _, _, _, _, _ => .revert
    | .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingSlots state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprListWithHelpers spec fields fuel state keys,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainSlots
                    state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [(resolved : Verity.Core.Uint256)]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName,
            evalExprWithHelpers spec fields fuel state index,
            evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _, _, _ => .revert
    | .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressSlots state.world slots resolved }
        | _, _ => .revert
    | .mstore offset value =>
        match evalExprWithHelpers spec fields fuel state offset,
            evalExprWithHelpers spec fields fuel state value with
        | some _, some _ => .continue state
        | _, _ => .revert
    | .tstore offset value =>
        match evalExprWithHelpers spec fields fuel state offset,
            evalExprWithHelpers spec fields fuel state value with
        | some resolvedOffset, some resolvedValue =>
            .continue {
              state with
              world := {
                state.world with
                transientStorage := fun o =>
                  if o = resolvedOffset then resolvedValue else state.world.transientStorage o
              }
            }
        | _, _ => .revert
    | .require cond _ =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | .return value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved => .return resolved state
        | none => .revert
    | .stop => .stop state
    | .ite cond thenBranch elseBranch =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtListWithHelpers spec fields fuel state thenBranch
            else
              execStmtListWithHelpers spec fields fuel state elseBranch
        | none => .revert
    | .internalCall calleeName args =>
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
    | .internalCallAssign names calleeName args =>
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
    | _ => .revert
  termination_by stmt => (fuel, sizeOf stmt)
  decreasing_by all_goals (simp_wf; omega)
  def execStmtListWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : List Stmt → StmtResult
    | [] => .continue state
    | stmt :: rest =>
        match execStmtWithHelpers spec fields fuel state stmt with
        | .continue next => execStmtListWithHelpers spec fields fuel next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
  termination_by stmts => (fuel, sizeOf stmts)
  decreasing_by all_goals (simp_wf; omega)
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
  termination_by (fuel, sizeOf fn.body + 1)
  decreasing_by all_goals (simp_wf; omega)
end

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

/-- Bridge from `SupportedInternalHelperWitness` conditions to
`findUniqueInternalFunction?` success.  The uniqueness premise
(`(spec.functions.map (·.name)).Nodup`) ensures the filter in
`findUniqueInternalFunction?` produces exactly one match. -/
private theorem findUniqueInternalFunction?_of_witness
    {spec : CompilationModel}
    {calleeName : String}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    findUniqueInternalFunction? spec calleeName = some witness.callee := by
  unfold findUniqueInternalFunction?
  have hmem := witness.summary.present
  have hinternal := witness.summary.internal
  have hname := witness.nameEq
  -- Show that witness.callee passes the filter predicate
  have hpass : (fun fn => fn.isInternal && fn.name == calleeName) witness.callee = true := by
    simp [hinternal, hname, BEq.beq, decide_eq_true_eq]
  -- The filter contains witness.callee
  have hin_filter : witness.callee ∈ spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) :=
    List.mem_filter.mpr ⟨hmem, hpass⟩
  -- Any element in the filter equals witness.callee (by name-nodup + name equality)
  have hfilter_eq : ∀ fn ∈ spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName),
      fn = witness.callee := by
    intro fn hfn
    have ⟨hfn_mem, hfn_pred⟩ := List.mem_filter.mp hfn
    simp [Bool.and_eq_true, BEq.beq, decide_eq_true_eq] at hfn_pred
    have hfn_name : fn.name = calleeName := hfn_pred.2
    have hname_eq : fn.name = witness.callee.name := by
      rw [hfn_name, hname]
    exact List.inj_on_of_nodup_map hnodup hfn_mem hmem hname_eq
  -- The filter of spec.functions is Nodup (sublist of a Nodup list)
  have hfilt_nodup : (spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName)).Nodup :=
    List.Nodup.filter _ (List.Nodup.of_map _ hnodup)
  -- The filter is nonempty, Nodup, and all elements equal witness.callee → it's [witness.callee]
  match hfilt : spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) with
  | [fn] =>
      have hfn : fn = witness.callee := by
        apply hfilter_eq
        simpa [hfilt] using hin_filter
      simp [findUniqueInternalFunction?, hfilt, hfn]
  | [] =>
      cases (by simpa [hfilt] using hin_filter : False)
  | fn₁ :: fn₂ :: rest =>
      exfalso
      have hnd : (fn₁ :: fn₂ :: rest).Nodup := by
        simpa [hfilt] using hfilt_nodup
      have h1 : fn₁ = witness.callee := by
        apply hfilter_eq
        rw [hfilt]
        simp
      have h2 : fn₂ = witness.callee := by
        apply hfilter_eq
        rw [hfilt]
        simp
      rw [h1, h2] at hnd
      exact (List.nodup_cons.mp hnd).1 (by simp)

/-- Public characterization of `execStmtWithHelpers` for `Stmt.internalCallAssign`
when the callee is identified by a `SupportedInternalHelperWitness` and function
names are unique.  This avoids exposing the private `findUniqueInternalFunction?`
while giving external proofs full access to the semantic structure. -/
theorem execStmtWithHelpers_internalCallAssign_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    execStmtWithHelpers spec fields (fuel + 1) state
      (Stmt.internalCallAssign names calleeName args) =
    match evalExprListWithHelpers spec fields (fuel + 1) state args with
    | some argVals =>
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
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
    | none => .revert := by
  cases hargs : evalExprListWithHelpers spec fields (fuel + 1) state args <;>
    simp [execStmtWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup, hargs]

/-- Version of `execStmtWithHelpers_internalCallAssign_obeys_summary` that takes
a `SupportedInternalHelperWitness` instead of the private `findUniqueInternalFunction?`
hypothesis, enabling use from files that cannot reference the private definition. -/
theorem execStmtWithHelpers_internalCallAssign_obeys_summary_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (hsound : InternalHelperSummarySound spec witness.callee witness.summary.contract)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    witness.summary.contract.post fuel state.world argVals
      result.success result.returnValue result.world :=
  execStmtWithHelpers_internalCallAssign_obeys_summary
    (names := names)
    (hfind := findUniqueInternalFunction?_of_witness witness hnodup)
    (hsound := hsound)
    (hargs := hargs)

/-- Public characterization of `execStmtWithHelpers` for `Stmt.internalCall`
(void call) via a `SupportedInternalHelperWitness` and function-name uniqueness. -/
theorem execStmtWithHelpers_internalCall_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    execStmtWithHelpers spec fields (fuel + 1) state
      (Stmt.internalCall calleeName args) =
    match evalExprListWithHelpers spec fields (fuel + 1) state args with
    | some argVals =>
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
        if hresult.success then
          .continue { state with world := hresult.world }
        else
          .revert
    | none => .revert := by
  cases hargs : evalExprListWithHelpers spec fields (fuel + 1) state args <;>
    simp [execStmtWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup, hargs]

/-- Public characterization of `evalExprWithHelpers` for `Expr.internalCall`
(expression-position helper call) via a `SupportedInternalHelperWitness` and
function-name uniqueness. -/
theorem evalExprWithHelpers_internalCall_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    evalExprWithHelpers spec fields (fuel + 1) state
      (Expr.internalCall calleeName args) =
    (do let argVals ← evalExprListWithHelpers spec fields (fuel + 1) state args
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
        if hresult.success then hresult.returnValue else none) := by
  simpa [evalExprWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup]

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

/-- Reusable global helper-summary proof inventory. This is the proof-carrying
counterpart to the positive helper witness inventory in `SupportedSpec.lean`:
each internal helper summary is proved once and can then be reused across every
caller that references the same witness. -/
structure SupportedHelperSummaryProofCatalog
    (spec : CompilationModel) : Prop where
  sound :
    ∀ calleeName (witness : SupportedInternalHelperWitness spec calleeName),
      InternalHelperSummarySound spec witness.callee witness.summary.contract

theorem SupportedHelperSummaryProofCatalog.soundOfWitness
    {spec : CompilationModel}
    (hCatalog : SupportedHelperSummaryProofCatalog spec)
    {calleeName : String}
    (witness : SupportedInternalHelperWitness spec calleeName) :
    InternalHelperSummarySound spec witness.callee witness.summary.contract :=
  hCatalog.sound calleeName witness

theorem SupportedBodyHelperSummariesSound_of_proofCatalog
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hCatalog : SupportedHelperSummaryProofCatalog spec) :
    SupportedBodyHelperSummariesSound spec fn hHelpers := by
  intro calleeName hmem
  exact hCatalog.soundOfWitness (hHelpers.summaryOfCall hmem)

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
  helperCatalog :
    SupportedHelperSummaryProofCatalog spec

theorem SupportedSpecHelperProofs.functionProofs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    (fn : FunctionSpec)
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionHelperProofs spec fn
      (hSupported.supportedFunctionOfSelectorDispatched hfn) := by
  refine
    { summariesSound :=
        SupportedBodyHelperSummariesSound_of_proofCatalog
          (hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers)
          hProofs.helperCatalog }

theorem SupportedSpecHelperProofs.functionSummariesSound
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedBodyHelperSummariesSound spec fn
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers :=
  (SupportedSpecHelperProofs.functionProofs hSupported hProofs fn hfn).summariesSound

mutual
  private theorem exprList_all_helperSurfaceClosed
      {exprs : List Expr}
      (hsurface : exprListTouchesUnsupportedHelperSurface exprs = false) :
      exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
    induction exprs with
    | nil =>
        rfl
    | cons expr rest ih =>
        simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have hrest := ih hsurface.2
        simp only [List.all_cons, hsurface.1, hrest]
        rfl

  theorem evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (expr : Expr)
      (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
      evalExprWithHelpers spec fields fuel state expr = evalExpr fields state expr := by
    cases expr with
    | internalCall _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | mappingChain _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | literal _ =>
        simpa [evalExprWithHelpers, evalExpr_literal]
    | param _ =>
        simpa [evalExprWithHelpers, evalExpr_param]
    | localVar _ =>
        simpa [evalExprWithHelpers, evalExpr_localVar]
    | caller | contractAddress | chainid | msgValue | blockTimestamp | blockNumber | blobbasefee
    | calldatasize =>
        simp [evalExprWithHelpers, evalExpr_caller, evalExpr_contractAddress, evalExpr_chainid,
          evalExpr_msgValue, evalExpr_blockTimestamp, evalExpr_blockNumber, evalExpr_blobbasefee,
          evalExpr_calldatasize]
    | storage _ =>
        simpa [evalExprWithHelpers, evalExpr_storage]
    | storageAddr _ =>
        simpa [evalExprWithHelpers, evalExpr_storageAddr]
    | storageArrayLength _ =>
        simpa [evalExprWithHelpers, evalExpr_storageArrayLength]
    | constructorArg _ | returndataSize =>
        simp [evalExprWithHelpers, evalExpr_constructorArg,
          evalExpr_returndataSize]
    | arrayLength _ =>
        simpa [evalExprWithHelpers, evalExpr_arrayLength]
    | dynamicBytesEq _ _ =>
        simpa [evalExprWithHelpers, evalExpr_dynamicBytesEq]
    | externalCall _ _ =>
        simpa [evalExprWithHelpers, evalExpr_externalCall]
    | mload a | tload a =>
        simp [evalExprWithHelpers, evalExpr_mload, evalExpr_tload]
    | calldataload a | extcodesize a | returndataOptionalBoolAt a =>
        simp [evalExprWithHelpers, evalExpr_calldataload, evalExpr_extcodesize,
          evalExpr_returndataOptionalBoolAt]
    | keccak256 a b =>
        simpa [evalExprWithHelpers, evalExpr_keccak256]
    | call g t v io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_call]
    | staticcall g t io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_staticcall]
    | delegatecall g t io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_delegatecall]
    | add a b | sub a b | mul a b | div a b | mod a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_add, evalExpr_sub, evalExpr_mul, evalExpr_div,
          evalExpr_mod, ha, hb]
    | eq a b | ge a b | gt a b | lt a b | le a b
    | logicalAnd a b | logicalOr a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_eq, evalExpr_ge, evalExpr_gt, evalExpr_lt,
          evalExpr_le, evalExpr_logicalAnd, evalExpr_logicalOr, ha, hb]
    | sdiv a b | smod a b | sgt a b | slt a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_sdiv, evalExpr_smod, evalExpr_sgt, evalExpr_slt, ha, hb]
    | bitAnd a b | bitOr a b | bitXor a b | min a b | max a b | wMulDown a b | wDivUp a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_bitAnd, evalExpr_bitOr, evalExpr_bitXor,
          evalExpr_min, evalExpr_max, evalExpr_wMulDown, evalExpr_wDivUp, ha, hb]
    | shl a b | shr a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_shl, evalExpr_shr, ha, hb]
    | sar a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_sar, ha, hb]
    | signextend a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_signextend, ha, hb]
    | bitNot a | logicalNot a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simpa [evalExprWithHelpers, evalExpr_bitNot, evalExpr_logicalNot, ha]
    | mapping _ b | mappingUint _ b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_mapping, evalExpr_mappingUint, hb]
    | arrayElement _ b =>
        simp [evalExprWithHelpers, evalExpr_arrayElement]
    | mappingWord _ b _ | mappingPackedWord _ b _ _ | structMember _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_mappingWord, evalExpr_mappingPackedWord,
          evalExpr_structMember, hb]
    | storageArrayElement fieldName b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_storageArrayElement, hb]
    | mapping2 _ a b | mapping2Word _ a b _ | structMember2 _ a b _ =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_mapping2, evalExpr_mapping2Word,
          evalExpr_structMember2, ha, hb]
    | ceilDiv a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_ceilDiv, ha, hb]
    | mulDivDown a b c | mulDivUp a b c =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.1.2
        have hc :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state c hsurface.2
        simpa [evalExprWithHelpers, evalExpr_mulDivDown, evalExpr_mulDivUp, ha, hb, hc]
    | ite cond thenVal elseVal =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have hcond :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hsurface.1.1
        have hthen :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state thenVal hsurface.1.2
        have helse :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state elseVal hsurface.2
        simpa [evalExprWithHelpers, evalExpr_ite, hcond, hthen, helse]

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
        simp [evalExprListWithHelpers,
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
            spec fields fuel state expr (by simpa using hsurface.1),
          ih hsurface.2]

  private theorem evalExprList_eq_mapM
      (fields : List Field)
      (state : RuntimeState)
      (exprs : List Expr) :
      evalExprList fields state exprs = exprs.mapM (evalExpr fields state) := by
    induction exprs with
    | nil =>
        rfl
    | cons expr rest ih =>
        simp [evalExprList, ih]
  
  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping fieldName key value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping fieldName key value) =
        execStmt fields state (.setMapping fieldName key value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingWord
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (wordOffset : Nat)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingWord fieldName key wordOffset value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingWord fieldName key wordOffset value) =
        execStmt fields state (.setMappingWord fieldName key wordOffset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingPackedWord
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (wordOffset : Nat)
      (packed : PackedBits)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.setMappingPackedWord fieldName key wordOffset packed value) = false) :
      execStmtWithHelpers spec fields fuel state
          (.setMappingPackedWord fieldName key wordOffset packed value) =
        execStmt fields state (.setMappingPackedWord fieldName key wordOffset packed value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingUint
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingUint fieldName key value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingUint fieldName key value) =
        execStmt fields state (.setMappingUint fieldName key value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName memberName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setStructMember fieldName key memberName value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStructMember fieldName key memberName value) =
        execStmt fields state (.setStructMember fieldName key memberName value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_keyListValue
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (keys : List Expr)
      (value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingChain fieldName keys value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingChain fieldName keys value) =
        execStmt fields state (.setMappingChain fieldName keys value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    have hkeys :
        keys.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true :=
      exprList_all_helperSurfaceClosed hsurface.1
    have hvalue :=
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2
    unfold execStmtWithHelpers execStmt
    rw [evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state keys hkeys, hvalue]
    rw [evalExprList_eq_mapM]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key1 key2 value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping2 fieldName key1 key2 value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping2 fieldName key1 key2 value) =
        execStmt fields state (.setMapping2 fieldName key1 key2 value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2Word
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key1 key2 value : Expr)
      (wordOffset : Nat)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping2Word fieldName key1 key2 wordOffset value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping2Word fieldName key1 key2 wordOffset value) =
        execStmt fields state (.setMapping2Word fieldName key1 key2 wordOffset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember2
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName memberName : String)
      (key1 key2 value : Expr)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.setStructMember2 fieldName key1 key2 memberName value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStructMember2 fieldName key1 key2 memberName value) =
        execStmt fields state (.setStructMember2 fieldName key1 key2 memberName value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStorageArrayElement
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (index value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setStorageArrayElement fieldName index value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStorageArrayElement fieldName index value) =
        execStmt fields state (.setStorageArrayElement fieldName index value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state index hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_mstore
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (offset value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.mstore offset value) = false) :
      execStmtWithHelpers spec fields fuel state (.mstore offset value) =
        execStmt fields state (.mstore offset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state offset hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_tstore
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (offset value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.tstore offset value) = false) :
      execStmtWithHelpers spec fields fuel state (.tstore offset value) =
        execStmt fields state (.tstore offset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmt,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state offset hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem expr_sizeOf_pos (expr : Expr) : 0 < sizeOf expr := by
    cases expr <;> simp

  private theorem stmt_sizeOf_lt_ite_then (cond : Expr) (thenBranch elseBranch : List Stmt) :
      sizeOf thenBranch + 1 < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
    have hcond : 0 < sizeOf cond := expr_sizeOf_pos cond
    simp [Stmt.ite.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_ite_else (cond : Expr) (thenBranch elseBranch : List Stmt) :
      sizeOf elseBranch + 1 < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
    have hcond : 0 < sizeOf cond := expr_sizeOf_pos cond
    simp [Stmt.ite.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_cons (stmt : Stmt) (rest : List Stmt) :
      sizeOf stmt + 1 < sizeOf (stmt :: rest) := by
    cases rest with
    | nil =>
        simp [List.cons.sizeOf_spec]
    | cons head tail =>
        simp [List.cons.sizeOf_spec]
        omega

end -- close the mutual block that started at line 2214

private theorem execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hstmt : ∀ (st : RuntimeState) (s : Stmt),
      sizeOf s < sizeOf stmts →
      stmtTouchesUnsupportedHelperSurface s = false →
      execStmtWithHelpers spec fields fuel st s =
        execStmt fields st s) :
    execStmtListWithHelpers spec fields fuel state stmts =
      execStmtList fields state stmts := by
  match stmts with
  | [] => simp [execStmtListWithHelpers, execStmtList]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      have hlt : sizeOf stmt < sizeOf (stmt :: rest) := by
        have := stmt_sizeOf_lt_cons stmt rest; omega
      rw [execStmtListWithHelpers,
        hstmt state stmt hlt hsurface.1]
      rw [execStmtList]
      cases hexec : execStmt fields state stmt with
      | «continue» next =>
          have hrest_lt : sizeOf rest < sizeOf (stmt :: rest) := by
            simp [List.cons.sizeOf_spec]
          exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
            spec fields fuel next rest hsurface.2
            (fun st s hs hsf => hstmt st s (Nat.lt_trans hs hrest_lt) hsf)
      | stop next => rfl
      | «return» value next => rfl
      | revert => rfl
termination_by sizeOf stmts

private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmt : Stmt)
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    execStmtWithHelpers spec fields fuel state stmt = execStmt fields state stmt := by
  match stmt with
  | .letVar _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .assignVar _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setStorage _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setStorageAddr _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .storageArrayPush _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .require cond _ =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hsurface]
  | .return value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .stop =>
      simp [execStmtWithHelpers, execStmt]
  | .setMapping fieldName key value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping
        spec fields fuel state fieldName key value hsurface
  | .setMappingWord fieldName key wordOffset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingWord
        spec fields fuel state fieldName key value wordOffset hsurface
  | .setMappingPackedWord fieldName key wordOffset packed value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingPackedWord
        spec fields fuel state fieldName key value wordOffset packed hsurface
  | .setMappingUint fieldName key value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingUint
        spec fields fuel state fieldName key value hsurface
  | .setStructMember fieldName key memberName value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember
        spec fields fuel state fieldName memberName key value hsurface
  | .setMapping2 fieldName key1 key2 value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2
        spec fields fuel state fieldName key1 key2 value hsurface
  | .setMapping2Word fieldName key1 key2 wordOffset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2Word
        spec fields fuel state fieldName key1 key2 value wordOffset hsurface
  | .setStructMember2 fieldName key1 key2 memberName value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember2
        spec fields fuel state fieldName memberName key1 key2 value hsurface
  | .setStorageArrayElement fieldName index value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStorageArrayElement
        spec fields fuel state fieldName index value hsurface
  | .mstore offset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_mstore
        spec fields fuel state offset value hsurface
  | .tstore offset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_tstore
        spec fields fuel state offset value hsurface
  | .ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rcases hsurface with ⟨⟨hcondSurface, hthenSurface⟩, helseSurface⟩
      simp only [execStmtWithHelpers, execStmt,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hcondSurface]
      cases evalExpr fields state cond with
      | none => rfl
      | some resolved =>
          by_cases hcond : resolved != 0
          · simp [hcond]
            exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
              spec fields fuel state thenBranch hthenSurface
              (fun st s hs hsf =>
                have : sizeOf s < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
                  have := stmt_sizeOf_lt_ite_then cond thenBranch elseBranch; omega
                execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                  spec fields fuel st s hsf)
          · simp [hcond]
            exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
              spec fields fuel state elseBranch helseSurface
              (fun st s hs hsf =>
                have : sizeOf s < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
                  have := stmt_sizeOf_lt_ite_else cond thenBranch elseBranch; omega
                execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                  spec fields fuel st s hsf)
  | .setMappingChain fieldName keys value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_keyListValue
        spec fields fuel state fieldName keys value hsurface
  | .internalCall _ _ => cases hsurface
  | .internalCallAssign _ _ _ => cases hsurface
  | .storageArrayPop _ => simp [execStmtWithHelpers, execStmt]
  | .requireError _ _ _ => simp [execStmtWithHelpers, execStmt]
  | .revertError _ _ => simp [execStmtWithHelpers, execStmt]
  | .returnValues _ => simp [execStmtWithHelpers, execStmt]
  | .returnArray _ => simp [execStmtWithHelpers, execStmt]
  | .returnBytes _ => simp [execStmtWithHelpers, execStmt]
  | .returnStorageWords _ => simp [execStmtWithHelpers, execStmt]
  | .calldatacopy _ _ _ => simp [execStmtWithHelpers, execStmt]
  | .returndataCopy _ _ _ => simp [execStmtWithHelpers, execStmt]
  | .revertReturndata => simp [execStmtWithHelpers, execStmt]
  | .emit _ _ => simp [execStmtWithHelpers, execStmt]
  | .rawLog _ _ _ => simp [execStmtWithHelpers, execStmt]
  | .externalCallBind _ _ _ => simp [execStmtWithHelpers, execStmt]
  | .ecm _ _ => simp [execStmtWithHelpers, execStmt]
  | .forEach _ _ _ =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [execStmtWithHelpers, execStmt]
termination_by sizeOf stmt

theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmt : Stmt)
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    execStmtWithHelpers spec fields fuel state stmt = execStmt fields state stmt := by
  exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
    spec fields fuel state stmt hsurface

theorem execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    execStmtListWithHelpers spec fields fuel state stmts = execStmtList fields state stmts := by
  exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
    spec fields fuel state stmts hsurface
    (fun st s _ hsf => execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
      spec fields fuel st s hsf)

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
  unfold interpretFunctionWithHelpers interpretFunction
  simp only
  cases hbind : bindSupportedParams fn.params tx.args with
  | none =>
      simp
  | some bindings =>
      have hbody :
          execStmtListWithHelpers spec (effectiveFields spec) fuel
              { world := withTransactionContext initialWorld tx, bindings := bindings } fn.body =
            execStmtList (effectiveFields spec)
              { world := withTransactionContext initialWorld tx, bindings := bindings } fn.body :=
        execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
          (spec := spec)
          (fields := effectiveFields spec)
          (fuel := fuel)
          (state := { world := withTransactionContext initialWorld tx, bindings := bindings })
          (stmts := fn.body)
          hsurface
      simp [hbody]

private theorem mem_of_find?_some_local
    {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, List.find? p xs = some x → x ∈ xs
  | [], _, h => by
      simp at h
  | y :: ys, x, h => by
      by_cases hp : p y
      · simp [List.find?, hp] at h
        cases h
        simp
      · simp [List.find?, hp] at h
        exact List.mem_cons.2 (Or.inr (mem_of_find?_some_local p h))

private theorem mem_left_of_mem_zip_local
    {α β : Type} :
    ∀ {xs : List α} {ys : List β} {x : α} {y : β}, (x, y) ∈ xs.zip ys → x ∈ xs
  | [], _, _, _, h => by
      simp at h
  | _ :: _, [], _, _, h => by
      simp at h
  | x0 :: xs, y0 :: ys, x, y, h => by
      simp [List.zip] at h ⊢
      rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        simp
      · exact Or.inr (mem_left_of_mem_zip_local h)

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
      have hmem :
          (foundFn, foundSelector) ∈ (selectorDispatchedFunctions spec).zip selectors := by
        simpa [selectorFunctionPairs] using
          mem_of_find?_some_local (fun entry => entry.2 == selector) hentry
      exact mem_left_of_mem_zip_local hmem

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
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
  · rfl

theorem interpretContractWithHelpers_eq_interpretContract_of_supportedSpecExceptMappingWrites
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
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
    exact interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := fuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
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

noncomputable def sourceContractSemanticsWithHelpers (spec : CompilationModel) (selectors : List Nat)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContractWithHelpers spec selectors fuel tx initialWorld

noncomputable def supportedSourceFunctionSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceFunctionSemanticsExceptMappingWrites
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceContractSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

noncomputable def supportedSourceContractSemanticsExceptMappingWrites
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
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
  simpa [sourceContractSemanticsWithHelpers, sourceContractSemantics] using
    SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpec
      hSupported fuel tx initialWorld

theorem sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecExceptMappingWrites
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    sourceContractSemanticsWithHelpers spec selectors fuel tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  simpa [sourceContractSemanticsWithHelpers, sourceContractSemantics] using
    SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpecExceptMappingWrites
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
  simpa [supportedSourceFunctionSemantics] using
    SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := hSupported.helperFuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed

theorem supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceFunctionSemanticsExceptMappingWrites spec selectors hSupported fn tx initialWorld =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites] using
    SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := hSupported.helperFuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed

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

theorem supportedSourceContractSemanticsExceptMappingWrites_eq_sourceContractSemantics
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceContractSemanticsExceptMappingWrites spec selectors hSupported tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecExceptMappingWrites
    hSupported hSupported.helperFuel tx initialWorld

-- Concrete executable smoke checks for these semantics live in
-- `SourceSemanticsFeatureTest.lean`, where runtime normalization is allowed
-- without making the proof/audit import path depend on large `decide` reductions.

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

private def storageArrayInitialWorld : Verity.ContractState :=
  { Verity.defaultState with storageArray := fun slot => if slot = 7 then [11, 17] else [] }

end Compiler.Proofs.IRGeneration
