/-
  Compiler.ContractSpec: Declarative Contract Specification

  This module defines a declarative way to specify contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management
-/

import Compiler.IR
import Compiler.Yul.Ast

namespace Compiler.ContractSpec

open Compiler
open Compiler.Yul

/-!
## Contract Specification DSL

Instead of manually writing IR, contracts provide a high-level specification:
- Storage fields with automatic slot assignment
- Functions with automatic selector computation
- Guards and access control patterns
-/

inductive FieldType
  | uint256
  | address
  | mapping   -- Address → Uint256 for now
  deriving Repr, BEq

structure Field where
  name : String
  ty : FieldType
  deriving Repr

inductive ParamType
  | uint256
  | address
  deriving Repr, BEq

structure Param where
  name : String
  ty : ParamType
  deriving Repr

-- Convert to IR types
def FieldType.toIRType : FieldType → IRType
  | uint256 => IRType.uint256
  | address => IRType.address
  | mapping => IRType.uint256  -- Mappings return uint256

def ParamType.toIRType : ParamType → IRType
  | uint256 => IRType.uint256
  | address => IRType.address

def Param.toIRParam (p : Param) : IRParam :=
  { name := p.name, ty := p.ty.toIRType }

/-!
## Function Body DSL

Simple DSL for expressing common contract operations without manual Yul.
-/

inductive Expr
  | literal (n : Nat)
  | param (name : String)
  | constructorArg (index : Nat)  -- Access constructor argument (loaded from bytecode)
  | storage (field : String)
  | mapping (field : String) (key : Expr)
  | caller
  | msgValue
  | blockTimestamp
  | localVar (name : String)  -- Reference to local variable
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | mod (a b : Expr)
  | bitAnd (a b : Expr)
  | bitOr (a b : Expr)
  | bitXor (a b : Expr)
  | bitNot (a : Expr)
  | shl (shift value : Expr)
  | shr (shift value : Expr)
  | eq (a b : Expr)
  | ge (a b : Expr)
  | gt (a b : Expr)  -- Greater than (strict)
  | lt (a b : Expr)
  | le (a b : Expr)  -- Less than or equal
  deriving Repr

inductive Stmt
  | letVar (name : String) (value : Expr)  -- Declare local variable
  | setStorage (field : String) (value : Expr)
  | setMapping (field : String) (key : Expr) (value : Expr)
  | require (cond : Expr) (message : String)
  | return (value : Expr)
  | stop
  deriving Repr

structure FunctionSpec where
  name : String
  params : List Param
  returnType : Option FieldType  -- None for unit/void
  body : List Stmt
  deriving Repr

structure ConstructorSpec where
  params : List Param  -- Constructor parameters (passed at deployment)
  body : List Stmt     -- Initialization code
  deriving Repr

structure ContractSpec where
  name : String
  fields : List Field
  constructor : Option ConstructorSpec  -- Deploy-time initialization with params
  functions : List FunctionSpec
  deriving Repr

/-!
## IR Generation from Spec

Automatically compile a ContractSpec to IRContract.
-/

-- Helper: Find field slot number
private def findFieldSlot (fields : List Field) (name : String) : Option Nat :=
  fields.findIdx? (·.name == name)

-- Helper: Is field a mapping?
private def isMapping (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any (·.ty == FieldType.mapping)

-- Keep compiler literals aligned with Uint256 semantics (mod 2^256).
private def uint256Modulus : Nat := 2 ^ 256

-- Compile expression to Yul
private def compileExpr (fields : List Field) : Expr → Except String YulExpr
  | Expr.literal n => pure (YulExpr.lit (n % uint256Modulus))
  | Expr.param name => pure (YulExpr.ident name)
  | Expr.constructorArg idx => pure (YulExpr.ident s!"arg{idx}")  -- Constructor args loaded as argN
  | Expr.storage field =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping"
    else
      match findFieldSlot fields field with
      | some slot => pure (YulExpr.call "sload" [YulExpr.lit slot])
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.mapping field key =>
    if !isMapping fields field then
      throw s!"Compilation error: field '{field}' is not a mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let keyExpr ← compileExpr fields key
        pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.caller => pure (YulExpr.call "caller" [])
  | Expr.msgValue => pure (YulExpr.call "callvalue" [])
  | Expr.blockTimestamp => pure (YulExpr.call "timestamp" [])
  | Expr.localVar name => pure (YulExpr.ident name)
  | Expr.add a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "add" [aExpr, bExpr])
  | Expr.sub a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "sub" [aExpr, bExpr])
  | Expr.mul a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "mul" [aExpr, bExpr])
  | Expr.div a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "div" [aExpr, bExpr])
  | Expr.mod a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "mod" [aExpr, bExpr])
  | Expr.bitAnd a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "and" [aExpr, bExpr])
  | Expr.bitOr a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "or" [aExpr, bExpr])
  | Expr.bitXor a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "xor" [aExpr, bExpr])
  | Expr.bitNot a => do
      let aExpr ← compileExpr fields a
      pure (YulExpr.call "not" [aExpr])
  | Expr.shl shift value => do
      let shiftExpr ← compileExpr fields shift
      let valueExpr ← compileExpr fields value
      pure (YulExpr.call "shl" [shiftExpr, valueExpr])
  | Expr.shr shift value => do
      let shiftExpr ← compileExpr fields shift
      let valueExpr ← compileExpr fields value
      pure (YulExpr.call "shr" [shiftExpr, valueExpr])
  | Expr.eq a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "eq" [aExpr, bExpr])
  | Expr.ge a b =>
    do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "iszero" [YulExpr.call "lt" [aExpr, bExpr]])
  | Expr.gt a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "gt" [aExpr, bExpr])
  | Expr.lt a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "lt" [aExpr, bExpr])
  | Expr.le a b =>
    do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "iszero" [YulExpr.call "gt" [aExpr, bExpr]])
termination_by e => sizeOf e

-- Compile require condition to a "failure" predicate to avoid double-negation.
private def compileRequireFailCond (fields : List Field) : Expr → Except String YulExpr
  | Expr.ge a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "lt" [aExpr, bExpr])
  | Expr.le a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "gt" [aExpr, bExpr])
  | cond => do
      let condExpr ← compileExpr fields cond
      pure (YulExpr.call "iszero" [condExpr])

private def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

private def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
  if bs.isEmpty then
    []
  else
    let chunk := bs.take 32
    chunk :: chunkBytes32 (bs.drop 32)
termination_by bs.length
decreasing_by
  simp_wf
  cases bs with
  | nil => simp at *
  | cons head tail => simp [List.length_drop]; omega

private def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

private def revertWithMessage (message : String) : List YulStmt :=
  let bytes := bytesFromString message
  let len := bytes.length
  let paddedLen := ((len + 31) / 32) * 32
  let selectorShifted : Nat := 0x08c379a0 * (2 ^ 224)
  let header := [
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.hex selectorShifted]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 4, YulExpr.lit 32]),
    YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 36, YulExpr.lit len])
  ]
  let dataStmts :=
    (chunkBytes32 bytes).enum.map fun (idx, chunk) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

-- Compile statement to Yul
private def compileStmt (fields : List Field) : Stmt → Except String (List YulStmt)
  | Stmt.letVar name value =>
    do
      let valueExpr ← compileExpr fields value
      pure [YulStmt.let_ name valueExpr]
  | Stmt.setStorage field value =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use setMapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          let valueExpr ← compileExpr fields value
          pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, valueExpr])]
      | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value =>
    if !isMapping fields field then
      throw s!"Compilation error: field '{field}' is not a mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          let keyExpr ← compileExpr fields key
          let valueExpr ← compileExpr fields value
          pure [
            YulStmt.expr (YulExpr.call "sstore" [
              YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr],
              valueExpr
            ])
          ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping"
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields value
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
      ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

-- Generate parameter loading code (from calldata)
private def genParamLoads (params : List Param) : List YulStmt :=
  params.enum.flatMap fun (idx, param) =>
    let offset := 4 + idx * 32  -- 4-byte selector + 32 bytes per param
    match param.ty with
    | ParamType.uint256 =>
      [YulStmt.let_ param.name (YulExpr.call "calldataload" [YulExpr.lit offset])]
    | ParamType.address =>
      [YulStmt.let_ param.name (YulExpr.call "and" [
        YulExpr.call "calldataload" [YulExpr.lit offset],
        YulExpr.hex ((2^160) - 1)
      ])]

-- Compile function spec to IR function
private def compileFunctionSpec (fields : List Field) (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  let paramLoads := genParamLoads spec.params
  let bodyChunks ← spec.body.mapM (compileStmt fields)
  let allStmts := paramLoads ++ bodyChunks.flatten
  return {
    name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := spec.returnType.map FieldType.toIRType |>.getD IRType.unit
    body := allStmts
  }

-- Check if contract uses mappings
private def usesMapping (fields : List Field) : Bool :=
  fields.any (·.ty == FieldType.mapping)

-- Generate constructor argument loading code (from end of bytecode)
private def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let totalBytes := params.length * 32
    let argsOffset := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.lit totalBytes]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit totalBytes])
    ]
    let loadArgs := params.enum.flatMap fun (idx, param) =>
      let offset := idx * 32
      match param.ty with
      | ParamType.uint256 =>
        [YulStmt.let_ s!"arg{idx}" (YulExpr.call "mload" [YulExpr.lit offset])]
      | ParamType.address =>
        [YulStmt.let_ s!"arg{idx}" (YulExpr.call "and" [
          YulExpr.call "mload" [YulExpr.lit offset],
          YulExpr.hex ((2^160) - 1)
        ])]
    argsOffset ++ loadArgs

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
private def compileConstructor (fields : List Field) (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← spec.body.mapM (compileStmt fields)
    return argLoads ++ bodyChunks.flatten

-- Main compilation function
-- SAFETY REQUIREMENTS (enforced by #guard in Specs.lean):
--   1. selectors.length == spec.functions.length
--   2. selectors[i] matches the Solidity signature of spec.functions[i]
-- WARNING: Order matters! If selector list is reordered but function list isn't,
--          functions will be mapped to wrong selectors with no runtime error.
private def firstDuplicateSelector (selectors : List Nat) : Option Nat :=
  let rec go (seen : List Nat) : List Nat → Option Nat
    | [] => none
    | sel :: rest =>
      if seen.contains sel then
        some sel
      else
        go (sel :: seen) rest
  go [] selectors

private def selectorNames (spec : ContractSpec) (selectors : List Nat) (sel : Nat) : List String :=
  (spec.functions.zip selectors).foldl (fun acc (fn, s) =>
    if s == sel then acc ++ [fn.name] else acc
  ) []

def compile (spec : ContractSpec) (selectors : List Nat) : Except String IRContract := do
  if spec.functions.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {spec.functions.length} functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (spec.functions.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec spec.fields sel fnSpec
  return {
    name := spec.name
    deploy := (← compileConstructor spec.fields spec.constructor)
    functions := functions
    usesMapping := usesMapping spec.fields
  }

end Compiler.ContractSpec
