import Compiler.CompilationModel.Types
import Compiler.CompilationModel.DynamicData
import Compiler.CompilationModel.InternalNaming
import Compiler.CompilationModel.ValidationHelpers

namespace Compiler.CompilationModel

open Compiler
open Compiler.Yul

-- Helpers for building common Yul patterns (defined outside mutual block for termination)
private def yulBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call op [a, b]

private def yulNegatedBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call op [a, b]]

def yulToBool (e : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call "iszero" [e]]

private def compileMappingSlotRead (fields : List Field) (field : String) (keyExpr : YulExpr)
    (label : String) (wordOffset : Nat := 0) : Except String YulExpr :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldSlot fields field with
    | some slot =>
      let mappingBase := YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]
      let finalSlot := if wordOffset == 0 then mappingBase else YulExpr.call "add" [mappingBase, YulExpr.lit wordOffset]
      pure (YulExpr.call "sload" [finalSlot])
    | none => throw s!"Compilation error: unknown mapping field '{field}' in {label}"

-- Compile expression to Yul (using mutual recursion for lists)
mutual
def compileExprList (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) :
    List Expr → Except String (List YulExpr)
  | [] => pure []
  | e :: es => do
      let head ← compileExpr fields dynamicSource e
      let tail ← compileExprList fields dynamicSource es
      pure (head :: tail)

def compileExpr (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) :
    Expr → Except String YulExpr
  | Expr.literal n => pure (YulExpr.lit (n % uint256Modulus))
  | Expr.param name => pure (YulExpr.ident name)
  | Expr.constructorArg idx => pure (YulExpr.ident s!"arg{idx}")
  | Expr.storage field =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping, Expr.mappingWord, or Expr.mappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          match f.packedBits with
          | none =>
              pure (YulExpr.call "sload" [YulExpr.lit slot])
          | some packed =>
              pure (YulExpr.call "and" [
                YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call "sload" [YulExpr.lit slot]],
                YulExpr.lit (packedMaskNat packed)
              ])
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.storageAddr field =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping, Expr.mappingWord, or Expr.mappingPackedWord"
    else
      match findFieldWithResolvedSlot fields field with
      | some (f, slot) =>
          match f.ty with
          | .address =>
              match f.packedBits with
              | none =>
                  pure (YulExpr.call "sload" [YulExpr.lit slot])
              | some packed =>
                  pure (YulExpr.call "and" [
                    YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call "sload" [YulExpr.lit slot]],
                    YulExpr.lit (packedMaskNat packed)
                  ])
          | _ =>
              throw s!"Compilation error: field '{field}' is not address-typed; use Expr.storage instead"
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.mapping field key => do
      compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mapping"
  | Expr.mappingWord field key wordOffset => do
      compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mappingWord" wordOffset
  | Expr.mappingPackedWord field key wordOffset packed => do
      if !packedBitsValid packed then
        throw s!"Compilation error: Expr.mappingPackedWord for field '{field}' has invalid packed range offset={packed.offset} width={packed.width}. Require 0 < width <= 256, offset < 256, and offset + width <= 256."
      else
        let slotWord ← compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mappingPackedWord" wordOffset
        pure (YulExpr.call "and" [
          YulExpr.call "shr" [YulExpr.lit packed.offset, slotWord],
          YulExpr.lit (packedMaskNat packed)
        ])
  | Expr.mapping2 field key1 key2 =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let key1Expr ← compileExpr fields dynamicSource key1
        let key2Expr ← compileExpr fields dynamicSource key2
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [innerSlot, key2Expr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mapping2Word field key1 key2 wordOffset =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let key1Expr ← compileExpr fields dynamicSource key1
        let key2Expr ← compileExpr fields dynamicSource key2
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
        let finalSlot := if wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit wordOffset]
        pure (YulExpr.call "sload" [finalSlot])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mappingUint field key => do
      compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mappingUint"
  | Expr.structMember field key memberName => do
      if isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is a double mapping; use Expr.structMember2 instead of Expr.structMember"
      match findStructMembers fields field with
      | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
      | some members =>
        match findStructMember members memberName with
        | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
        | some member =>
          match member.packed with
          | none =>
            compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) s!"structMember.{memberName}" member.wordOffset
          | some packed =>
            let slotWord ← compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) s!"structMember.{memberName}" member.wordOffset
            pure (YulExpr.call "and" [
              YulExpr.call "shr" [YulExpr.lit packed.offset, slotWord],
              YulExpr.lit (packedMaskNat packed)
            ])
  | Expr.structMember2 field key1 key2 memberName =>
      if !isMapping2 fields field then
        throw s!"Compilation error: field '{field}' is not a double mapping; use Expr.structMember instead of Expr.structMember2"
      else
        match findStructMembers fields field with
        | none => throw s!"Compilation error: field '{field}' is not a mappingStruct"
        | some members =>
          match findStructMember members memberName with
          | none => throw s!"Compilation error: struct field '{field}' has no member '{memberName}'"
          | some member =>
            match findFieldSlot fields field with
            | some slot => do
              let key1Expr ← compileExpr fields dynamicSource key1
              let key2Expr ← compileExpr fields dynamicSource key2
              let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
              let outerSlot := YulExpr.call "mappingSlot" [innerSlot, key2Expr]
              let finalSlot := if member.wordOffset == 0 then outerSlot else YulExpr.call "add" [outerSlot, YulExpr.lit member.wordOffset]
              match member.packed with
              | none =>
                pure (YulExpr.call "sload" [finalSlot])
              | some packed =>
                pure (YulExpr.call "and" [
                  YulExpr.call "shr" [YulExpr.lit packed.offset, YulExpr.call "sload" [finalSlot]],
                  YulExpr.lit (packedMaskNat packed)
                ])
            | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.caller => pure (YulExpr.call "caller" [])
  | Expr.contractAddress => pure (YulExpr.call "address" [])
  | Expr.chainid => pure (YulExpr.call "chainid" [])
  | Expr.extcodesize addr => do
      pure (YulExpr.call "extcodesize" [← compileExpr fields dynamicSource addr])
  | Expr.msgValue => pure (YulExpr.call "callvalue" [])
  | Expr.blockTimestamp => pure (YulExpr.call "timestamp" [])
  | Expr.blockNumber => pure (YulExpr.call "number" [])
  | Expr.blobbasefee => pure (YulExpr.call "blobbasefee" [])
  | Expr.mload offset => do
      pure (YulExpr.call "mload" [← compileExpr fields dynamicSource offset])
  | Expr.tload offset => do
      pure (YulExpr.call "tload" [← compileExpr fields dynamicSource offset])
  | Expr.keccak256 offset size => do
      pure (YulExpr.call "keccak256" [
        ← compileExpr fields dynamicSource offset,
        ← compileExpr fields dynamicSource size
      ])
  | Expr.call gas target value inOffset inSize outOffset outSize => do
      pure (YulExpr.call "call" [
        ← compileExpr fields dynamicSource gas,
        ← compileExpr fields dynamicSource target,
        ← compileExpr fields dynamicSource value,
        ← compileExpr fields dynamicSource inOffset,
        ← compileExpr fields dynamicSource inSize,
        ← compileExpr fields dynamicSource outOffset,
        ← compileExpr fields dynamicSource outSize
      ])
  | Expr.staticcall gas target inOffset inSize outOffset outSize => do
      pure (YulExpr.call "staticcall" [
        ← compileExpr fields dynamicSource gas,
        ← compileExpr fields dynamicSource target,
        ← compileExpr fields dynamicSource inOffset,
        ← compileExpr fields dynamicSource inSize,
        ← compileExpr fields dynamicSource outOffset,
        ← compileExpr fields dynamicSource outSize
      ])
  | Expr.delegatecall gas target inOffset inSize outOffset outSize => do
      pure (YulExpr.call "delegatecall" [
        ← compileExpr fields dynamicSource gas,
        ← compileExpr fields dynamicSource target,
        ← compileExpr fields dynamicSource inOffset,
        ← compileExpr fields dynamicSource inSize,
        ← compileExpr fields dynamicSource outOffset,
        ← compileExpr fields dynamicSource outSize
      ])
  | Expr.calldatasize => pure (YulExpr.call "calldatasize" [])
  | Expr.calldataload offset => do
      pure (YulExpr.call "calldataload" [← compileExpr fields dynamicSource offset])
  | Expr.returndataSize => pure (YulExpr.call "returndatasize" [])
  | Expr.returndataOptionalBoolAt outOffset => do
      let outOffsetExpr ← compileExpr fields dynamicSource outOffset
      let rdSize := YulExpr.call "returndatasize" []
      pure (YulExpr.call "or" [
        YulExpr.call "eq" [rdSize, YulExpr.lit 0],
        YulExpr.call "and" [
          YulExpr.call "eq" [rdSize, YulExpr.lit 32],
          YulExpr.call "eq" [YulExpr.call "mload" [outOffsetExpr], YulExpr.lit 1]
        ]
      ])
  | Expr.localVar name => pure (YulExpr.ident name)
  | Expr.externalCall name args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure (YulExpr.call name argExprs)
  | Expr.internalCall functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure (YulExpr.call (internalFunctionYulName functionName) argExprs)
  | Expr.arrayLength name => pure (YulExpr.ident s!"{name}_length")
  | Expr.arrayElement name index => do
      let indexExpr ← compileExpr fields dynamicSource index
      let helperName := match dynamicSource with
        | .calldata => checkedArrayElementCalldataHelperName
        | .memory => checkedArrayElementMemoryHelperName
      pure (YulExpr.call helperName [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.ident s!"{name}_length",
        indexExpr
      ])
  | Expr.add a b     => return yulBinOp "add" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.sub a b     => return yulBinOp "sub" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.mul a b     => return yulBinOp "mul" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.div a b     => return yulBinOp "div" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.mod a b     => return yulBinOp "mod" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.bitAnd a b  => return yulBinOp "and" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.bitOr a b   => return yulBinOp "or"  (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.bitXor a b  => return yulBinOp "xor" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.bitNot a    => return YulExpr.call "not" [← compileExpr fields dynamicSource a]
  | Expr.shl s v     => return yulBinOp "shl" (← compileExpr fields dynamicSource s) (← compileExpr fields dynamicSource v)
  | Expr.shr s v     => return yulBinOp "shr" (← compileExpr fields dynamicSource s) (← compileExpr fields dynamicSource v)
  | Expr.eq a b      => return yulBinOp "eq"  (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.gt a b      => return yulBinOp "gt"  (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.lt a b      => return yulBinOp "lt"  (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.ge a b      => return yulNegatedBinOp "lt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.le a b      => return yulNegatedBinOp "gt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.logicalAnd a b => return yulBinOp "and" (yulToBool (← compileExpr fields dynamicSource a)) (yulToBool (← compileExpr fields dynamicSource b))
  | Expr.logicalOr a b  => return yulBinOp "or"  (yulToBool (← compileExpr fields dynamicSource a)) (yulToBool (← compileExpr fields dynamicSource b))
  | Expr.logicalNot a   => return YulExpr.call "iszero" [← compileExpr fields dynamicSource a]
  | Expr.mulDivDown a b c => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      let cc ← compileExpr fields dynamicSource c
      -- div(mul(a, b), c)
      pure (YulExpr.call "div" [YulExpr.call "mul" [ca, cb], cc])
  | Expr.mulDivUp a b c => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      let cc ← compileExpr fields dynamicSource c
      -- div(add(mul(a, b), sub(c, 1)), c)
      pure (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [ca, cb],
          YulExpr.call "sub" [cc, YulExpr.lit 1]
        ],
        cc
      ])
  | Expr.wMulDown a b => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      -- div(mul(a, b), 1000000000000000000)
      pure (YulExpr.call "div" [YulExpr.call "mul" [ca, cb], YulExpr.lit 1000000000000000000])
  | Expr.wDivUp a b => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      -- div(add(mul(a, 1000000000000000000), sub(b, 1)), b)
      pure (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [ca, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [cb, YulExpr.lit 1]
        ],
        cb
      ])
  | Expr.min a b => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      -- sub(a, mul(sub(a, b), gt(a, b)))
      pure (YulExpr.call "sub" [ca,
        YulExpr.call "mul" [
          YulExpr.call "sub" [ca, cb],
          YulExpr.call "gt" [ca, cb]
        ]
      ])
  | Expr.max a b => do
      let ca ← compileExpr fields dynamicSource a
      let cb ← compileExpr fields dynamicSource b
      -- add(a, mul(sub(b, a), gt(b, a)))
      pure (YulExpr.call "add" [ca,
        YulExpr.call "mul" [
          YulExpr.call "sub" [cb, ca],
          YulExpr.call "gt" [cb, ca]
        ]
      ])
  | Expr.ite cond thenVal elseVal => do
      let condExpr ← compileExpr fields dynamicSource cond
      let thenExpr ← compileExpr fields dynamicSource thenVal
      let elseExpr ← compileExpr fields dynamicSource elseVal
      -- Branchless ternary: add(mul(iszero(iszero(cond)), thenVal), mul(iszero(cond), elseVal))
      let condBool := YulExpr.call "iszero" [YulExpr.call "iszero" [condExpr]]
      let condNeg := YulExpr.call "iszero" [condExpr]
      pure (YulExpr.call "add" [
        YulExpr.call "mul" [condBool, thenExpr],
        YulExpr.call "mul" [condNeg, elseExpr]
      ])
end

-- Compile require condition to a "failure" predicate to avoid double-negation.
def compileRequireFailCond (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) :
    Expr → Except String YulExpr
  | Expr.ge a b => return yulBinOp "lt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.le a b => return yulBinOp "gt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | cond => return YulExpr.call "iszero" [← compileExpr fields dynamicSource cond]

end Compiler.CompilationModel
