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
  | localVar (name : String)  -- Reference to local variable
  | add (a b : Expr)
  | sub (a b : Expr)
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

-- Compile expression to Yul
private def compileExpr (fields : List Field) : Expr → YulExpr
  | Expr.literal n => YulExpr.lit n
  | Expr.param name => YulExpr.ident name
  | Expr.constructorArg idx => YulExpr.ident s!"arg{idx}"  -- Constructor args loaded as argN
  | Expr.storage field =>
    match findFieldSlot fields field with
    | some slot => YulExpr.call "sload" [YulExpr.lit slot]
    | none => panic! s!"Compilation error: unknown storage field '{field}'"
  | Expr.mapping field key =>
    match findFieldSlot fields field with
    | some slot => YulExpr.call "sload" [YulExpr.call "mappingSlot" [YulExpr.lit slot, compileExpr fields key]]
    | none => panic! s!"Compilation error: unknown mapping field '{field}'"
  | Expr.caller => YulExpr.call "caller" []
  | Expr.localVar name => YulExpr.ident name
  | Expr.add a b => YulExpr.call "add" [compileExpr fields a, compileExpr fields b]
  | Expr.sub a b => YulExpr.call "sub" [compileExpr fields a, compileExpr fields b]
  | Expr.eq a b => YulExpr.call "eq" [compileExpr fields a, compileExpr fields b]
  | Expr.ge a b => YulExpr.call "iszero" [YulExpr.call "lt" [compileExpr fields a, compileExpr fields b]]
  | Expr.gt a b => YulExpr.call "gt" [compileExpr fields a, compileExpr fields b]
  | Expr.lt a b => YulExpr.call "lt" [compileExpr fields a, compileExpr fields b]
  | Expr.le a b => YulExpr.call "iszero" [YulExpr.call "gt" [compileExpr fields a, compileExpr fields b]]
termination_by e => sizeOf e

-- Compile statement to Yul
private def compileStmt (fields : List Field) : Stmt → List YulStmt
  | Stmt.letVar name value =>
    [YulStmt.let_ name (compileExpr fields value)]
  | Stmt.setStorage field value =>
    match findFieldSlot fields field with
    | some slot => [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, compileExpr fields value])]
    | none => panic! s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value =>
    match findFieldSlot fields field with
    | some slot =>
      [ YulStmt.expr (YulExpr.call "sstore" [
          YulExpr.call "mappingSlot" [YulExpr.lit slot, compileExpr fields key],
          compileExpr fields value
        ])
      ]
    | none => panic! s!"Compilation error: unknown mapping field '{field}' in setMapping"
  | Stmt.require cond message =>
    [ YulStmt.if_ (YulExpr.call "iszero" [compileExpr fields cond]) [
        YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
      ]
    ]
  | Stmt.return value =>
    [ YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, compileExpr fields value])
    , YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
    ]
  | Stmt.stop => [YulStmt.expr (YulExpr.call "stop" [])]

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
private def compileFunctionSpec (fields : List Field) (selector : Nat) (spec : FunctionSpec) : IRFunction :=
  let paramLoads := genParamLoads spec.params
  let bodyStmts := spec.body.flatMap (compileStmt fields)
  let allStmts := paramLoads ++ bodyStmts
  { name := spec.name
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
private def compileConstructor (fields : List Field) (ctor : Option ConstructorSpec) : List YulStmt :=
  match ctor with
  | none => []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let body := spec.body.flatMap (compileStmt fields)
    argLoads ++ body

-- Main compilation function
-- SAFETY REQUIREMENTS (enforced by #guard in Specs.lean):
--   1. selectors.length == spec.functions.length
--   2. selectors[i] matches the Solidity signature of spec.functions[i]
-- WARNING: Order matters! If selector list is reordered but function list isn't,
--          functions will be mapped to wrong selectors with no runtime error.
def compile (spec : ContractSpec) (selectors : List Nat) : IRContract :=
  -- Validate selector count matches function count
  if spec.functions.length != selectors.length then
    panic! s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {spec.functions.length} functions"
  else
    { name := spec.name
      deploy := compileConstructor spec.fields spec.constructor
      functions := spec.functions.zip selectors |>.map fun (fnSpec, sel) =>
        compileFunctionSpec spec.fields sel fnSpec
      usesMapping := usesMapping spec.fields
    }

end Compiler.ContractSpec
