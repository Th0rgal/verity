/-
  Compiler.ContractSpec: Declarative Contract Specification

  This module defines a declarative way to specify contracts for compilation,
  eliminating manual IR writing while keeping the system simple and maintainable.

  Philosophy:
  - Contracts specify their structure declaratively
  - Compiler generates IR automatically from the spec
  - Reduces boilerplate and eliminates manual slot/selector management

  Features:
  - Storage fields with automatic slot assignment (uint256, address, mapping)
  - Flexible mapping types: Address→Uint256, Uint256→Uint256, nested mappings (#154)
  - Functions with automatic selector computation
  - Guards and access control patterns
  - If/else branching and bounded loops (#179)
  - Array/bytes parameter types and dynamic calldata (#180)
  - Internal function composition (#181)
  - Event emission (#153)
  - Verified external library integration (#184)
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
- Control flow: if/else branching, bounded loops
- Array parameters and dynamic calldata
- Internal function calls for modular composition
- Event emission for standards compliance
-/

/-!
### Mapping Key Types (#154)

Support flexible mapping types: single-key, double-key (nested), and uint256 keys.
-/

inductive MappingKeyType
  | address    -- mapping(address => ...)
  | uint256    -- mapping(uint256 => ...)
  deriving Repr, BEq

inductive MappingType
  | simple (keyType : MappingKeyType)                          -- mapping(K => uint256)
  | nested (outerKey : MappingKeyType) (innerKey : MappingKeyType)  -- mapping(K1 => mapping(K2 => uint256))
  deriving Repr, BEq

inductive FieldType
  | uint256
  | address
  | mappingTyped (mt : MappingType)  -- Flexible mapping types (#154)
  deriving Repr, BEq

structure Field where
  name : String
  ty : FieldType
  deriving Repr

/-!
### Parameter Types (#180)

Extended parameter types supporting arrays, bytes, and bytes32.
-/

inductive ParamType
  | uint256
  | address
  | bool                                   -- Solidity bool (ABI-encoded as 32-byte 0/1)
  | bytes32                                -- Fixed 32-byte value
  | tuple (elemTypes : List ParamType)     -- ABI tuple
  | array (elemType : ParamType)           -- Dynamic array: uint256[], address[]
  | fixedArray (elemType : ParamType) (size : Nat)  -- Fixed array: uint256[3]
  | bytes                                  -- Dynamic bytes
  deriving Repr, BEq

structure Param where
  name : String
  ty : ParamType
  deriving Repr

-- Convert to IR types
def FieldType.toIRType : FieldType → IRType
  | uint256 => IRType.uint256
  | address => IRType.address
  | mappingTyped _ => IRType.uint256  -- All mappings return uint256

def ParamType.toIRType : ParamType → IRType
  | uint256 => IRType.uint256
  | address => IRType.address
  | bool => IRType.uint256
  | bytes32 => IRType.uint256  -- bytes32 is a 256-bit value
  | tuple _ => IRType.uint256  -- Tuples are represented as ABI offsets for now
  | array _ => IRType.uint256  -- Arrays are represented as calldata offsets
  | fixedArray _ _ => IRType.uint256
  | bytes => IRType.uint256

def Param.toIRParam (p : Param) : IRParam :=
  { name := p.name, ty := p.ty.toIRType }

/-!
### Event Definitions (#153)

Events for ERC20/ERC721 compliance and general logging.
-/

inductive EventParamKind
  | indexed     -- Goes into LOG topic (max 3 indexed params per event)
  | unindexed   -- Goes into LOG data
  deriving Repr, BEq

structure EventParam where
  name : String
  ty : ParamType
  kind : EventParamKind
  deriving Repr

structure EventDef where
  name : String
  params : List EventParam
  deriving Repr

structure ErrorDef where
  name : String
  params : List ParamType
  deriving Repr

/-!
### External Function Declarations (#184)

Verified external library integration with axiom documentation.
-/

structure ExternalFunction where
  name : String
  params : List ParamType
  returnType : Option ParamType := none  -- backward compatibility
  returns : List ParamType := []  -- empty for void functions
  /-- Names of axioms assumed about this function.
      The actual Lean propositions are stated separately;
      these names are for documentation and audit purposes. -/
  axiomNames : List String
  deriving Repr

/-!
## Function Body DSL

DSL for expressing contract operations including control flow,
internal calls, and event emission.
-/

inductive Expr
  | literal (n : Nat)
  | param (name : String)
  | constructorArg (index : Nat)  -- Access constructor argument (loaded from bytecode)
  | storage (field : String)
  | mapping (field : String) (key : Expr)
  | mapping2 (field : String) (key1 key2 : Expr)  -- Double mapping (#154)
  | mappingUint (field : String) (key : Expr)  -- Uint256-keyed mapping (#154)
  | caller
  | msgValue
  | blockTimestamp
  | localVar (name : String)  -- Reference to local variable
  | externalCall (name : String) (args : List Expr)  -- External function call (linked at compile time)
  | internalCall (functionName : String) (args : List Expr)  -- Internal function call (#181)
  | arrayLength (name : String)  -- Length of a dynamic array parameter (#180)
  | arrayElement (name : String) (index : Expr)  -- Element of a dynamic array parameter (#180)
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
  | logicalAnd (a b : Expr)  -- Short-circuit logical AND
  | logicalOr (a b : Expr)   -- Short-circuit logical OR
  | logicalNot (a : Expr)    -- Logical NOT
  deriving Repr

inductive Stmt
  | letVar (name : String) (value : Expr)  -- Declare local variable
  | assignVar (name : String) (value : Expr)  -- Reassign existing variable
  | setStorage (field : String) (value : Expr)
  | setMapping (field : String) (key : Expr) (value : Expr)
  | setMapping2 (field : String) (key1 key2 : Expr) (value : Expr)  -- Double mapping write (#154)
  | setMappingUint (field : String) (key : Expr) (value : Expr)  -- Uint256-keyed mapping write (#154)
  | require (cond : Expr) (message : String)
  | requireError (cond : Expr) (errorName : String) (args : List Expr)
  | revertError (errorName : String) (args : List Expr)
  | return (value : Expr)
  | returnValues (values : List Expr)  -- ABI-encode multiple static return words
  | returnArray (name : String)        -- ABI-encode dynamic uint256[] parameter loaded from calldata
  | returnBytes (name : String)        -- ABI-encode dynamic bytes parameter loaded from calldata
  | returnStorageWords (name : String) -- ABI-encode dynamic uint256[] from sload over a dynamic word-array parameter
  | stop
  | ite (cond : Expr) (thenBranch : List Stmt) (elseBranch : List Stmt)  -- If/else (#179)
  | forEach (varName : String) (count : Expr) (body : List Stmt)  -- Bounded loop (#179)
  | emit (eventName : String) (args : List Expr)  -- Emit event (#153)
  | internalCall (functionName : String) (args : List Expr)  -- Internal call as statement (#181)
  | internalCallAssign (names : List String) (functionName : String) (args : List Expr)
  deriving Repr

structure FunctionSpec where
  name : String
  params : List Param
  returnType : Option FieldType  -- None for unit/void
  returns : List ParamType := []  -- preferred ABI return model; falls back to returnType when empty
  /-- Whether this entrypoint accepts non-zero msg.value. -/
  isPayable : Bool := false
  body : List Stmt
  /-- Whether this is an internal-only function (not exposed via selector dispatch) -/
  isInternal : Bool := false
  deriving Repr

structure ConstructorSpec where
  params : List Param  -- Constructor parameters (passed at deployment)
  /-- Whether deployment is allowed with non-zero msg.value. -/
  isPayable : Bool := false
  body : List Stmt     -- Initialization code
  deriving Repr

structure ContractSpec where
  name : String
  fields : List Field
  constructor : Option ConstructorSpec  -- Deploy-time initialization with params
  functions : List FunctionSpec
  events : List EventDef := []  -- Event definitions (#153)
  errors : List ErrorDef := []  -- Custom errors (#586)
  externals : List ExternalFunction := []  -- External function declarations (#184)
  deriving Repr

/-!
## IR Generation from Spec

Automatically compile a ContractSpec to IRContract.
-/

-- Helper: Find field slot number
def findFieldSlot (fields : List Field) (name : String) : Option Nat :=
  fields.findIdx? (·.name == name)

-- Helper: Is field a mapping?
def isMapping (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.mappingTyped _ => true
    | _ => false

-- Helper: Is field a double mapping?
def isMapping2 (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.mappingTyped (MappingType.nested _ _) => true
    | _ => false

-- Keep compiler literals aligned with Uint256 semantics (mod 2^256).
def uint256Modulus : Nat := 2 ^ 256

-- Helpers for building common Yul patterns (defined outside mutual block for termination)
private def yulBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call op [a, b]

private def yulNegatedBinOp (op : String) (a b : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call op [a, b]]

private def yulToBool (e : YulExpr) : YulExpr :=
  YulExpr.call "iszero" [YulExpr.call "iszero" [e]]

private inductive DynamicDataSource where
  | calldata
  | memory
  deriving DecidableEq

private def dynamicWordLoad (source : DynamicDataSource) (offset : YulExpr) : YulExpr :=
  match source with
  | .calldata => YulExpr.call "calldataload" [offset]
  | .memory => YulExpr.call "mload" [offset]

private def dynamicCopyData (source : DynamicDataSource)
    (destOffset sourceOffset len : YulExpr) : List YulStmt :=
  match source with
  | .calldata =>
      [YulStmt.expr (YulExpr.call "calldatacopy" [destOffset, sourceOffset, len])]
  | .memory =>
      [YulStmt.for_
        [YulStmt.let_ "__copy_i" (YulExpr.lit 0)]
        (YulExpr.call "lt" [YulExpr.ident "__copy_i", len])
        [YulStmt.assign "__copy_i" (YulExpr.call "add" [YulExpr.ident "__copy_i", YulExpr.lit 32])]
        [YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [destOffset, YulExpr.ident "__copy_i"],
          YulExpr.call "mload" [YulExpr.call "add" [sourceOffset, YulExpr.ident "__copy_i"]]
        ])]]

private def compileMappingSlotRead (fields : List Field) (field : String) (keyExpr : YulExpr)
    (label : String) : Except String YulExpr :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldSlot fields field with
    | some slot =>
      pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]])
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
      throw s!"Compilation error: field '{field}' is a mapping; use Expr.mapping"
    else
      match findFieldSlot fields field with
      | some slot => pure (YulExpr.call "sload" [YulExpr.lit slot])
      | none => throw s!"Compilation error: unknown storage field '{field}'"
  | Expr.mapping field key => do
      compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mapping"
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
  | Expr.mappingUint field key => do
      compileMappingSlotRead fields field (← compileExpr fields dynamicSource key) "mappingUint"
  | Expr.caller => pure (YulExpr.call "caller" [])
  | Expr.msgValue => pure (YulExpr.call "callvalue" [])
  | Expr.blockTimestamp => pure (YulExpr.call "timestamp" [])
  | Expr.localVar name => pure (YulExpr.ident name)
  | Expr.externalCall name args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure (YulExpr.call name argExprs)
  | Expr.internalCall functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure (YulExpr.call s!"internal_{functionName}" argExprs)
  | Expr.arrayLength name => pure (YulExpr.ident s!"{name}_length")
  | Expr.arrayElement name index => do
      let indexExpr ← compileExpr fields dynamicSource index
      pure (dynamicWordLoad dynamicSource (YulExpr.call "add" [
        YulExpr.ident s!"{name}_data_offset",
        YulExpr.call "mul" [indexExpr, YulExpr.lit 32]
      ]))
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
end

-- Compile require condition to a "failure" predicate to avoid double-negation.
def compileRequireFailCond (fields : List Field)
    (dynamicSource : DynamicDataSource := .calldata) :
    Expr → Except String YulExpr
  | Expr.ge a b => return yulBinOp "lt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | Expr.le a b => return yulBinOp "gt" (← compileExpr fields dynamicSource a) (← compileExpr fields dynamicSource b)
  | cond => return YulExpr.call "iszero" [← compileExpr fields dynamicSource cond]

def bytesFromString (s : String) : List UInt8 :=
  s.toUTF8.data.toList

def chunkBytes32 (bs : List UInt8) : List (List UInt8) :=
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
  | cons head tail => simp; omega

def wordFromBytes (bs : List UInt8) : Nat :=
  let padded := bs ++ List.replicate (32 - bs.length) (0 : UInt8)
  padded.foldl (fun acc b => acc * 256 + b.toNat) 0

def revertWithMessage (message : String) : List YulStmt :=
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
    (chunkBytes32 bytes).zipIdx.map fun (chunk, idx) =>
      let offset := 68 + idx * 32
      let word := wordFromBytes chunk
      YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit offset, YulExpr.hex word])
  let totalSize := 68 + paddedLen
  header ++ dataStmts ++ [YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit totalSize])]

/-!
### Event Topic Computation (#153)

Compute the event signature hash (topic 0) from the event name and parameter types.
This mirrors how Solidity computes event signatures: keccak256("EventName(type1,type2,...)").
At compile time we use a placeholder; CI validates the selector matches solc output.
-/

-- Map ParamType to its Solidity type string (used for event and function signatures)
partial def paramTypeToSolidityString : ParamType → String
  | ParamType.uint256 => "uint256"
  | ParamType.address => "address"
  | ParamType.bool => "bool"
  | ParamType.bytes32 => "bytes32"
  | ParamType.tuple ts =>
      "(" ++ String.intercalate "," (ts.map paramTypeToSolidityString) ++ ")"
  | ParamType.array t => paramTypeToSolidityString t ++ "[]"
  | ParamType.fixedArray t n => paramTypeToSolidityString t ++ "[" ++ toString n ++ "]"
  | ParamType.bytes => "bytes"

def eventSignature (eventDef : EventDef) : String :=
  let params := eventDef.params.map (fun p => paramTypeToSolidityString p.ty)
  s!"{eventDef.name}(" ++ String.intercalate "," params ++ ")"

def errorSignature (errorDef : ErrorDef) : String :=
  s!"{errorDef.name}(" ++ String.intercalate "," (errorDef.params.map paramTypeToSolidityString) ++ ")"

def fieldTypeToParamType : FieldType → ParamType
  | FieldType.uint256 => ParamType.uint256
  | FieldType.address => ParamType.address
  | FieldType.mappingTyped _ => ParamType.uint256

private def resolveReturns (context : String) (legacy : Option ParamType)
    (returns : List ParamType) : Except String (List ParamType) := do
  if returns.isEmpty then
    pure (legacy.map (fun ty => [ty]) |>.getD [])
  else
    match legacy with
    | none => pure returns
    | some ty =>
        if returns == [ty] then
          pure returns
        else
          throw s!"Compilation error: {context} has conflicting return declarations (returnType vs returns)"

def functionReturns (spec : FunctionSpec) : Except String (List ParamType) :=
  resolveReturns s!"function '{spec.name}'"
    (spec.returnType.map fieldTypeToParamType) spec.returns

def externalFunctionReturns (spec : ExternalFunction) : Except String (List ParamType) :=
  resolveReturns s!"external declaration '{spec.name}'" spec.returnType spec.returns

private def findParamType (params : List Param) (name : String) : Option ParamType :=
  (params.find? (fun p => p.name == name)).map (·.ty)

private def isStorageWordArrayParam : ParamType → Bool
  | ParamType.array ParamType.bytes32 => true
  | ParamType.array ParamType.uint256 => true
  | _ => false

private partial def validateStmtParamReferences (fnName : String) (params : List Param) :
    Stmt → Except String Unit
  | Stmt.returnArray name =>
      match findParamType params name with
      | some (ParamType.array _) =>
          pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnArray '{name}' requires array parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnArray references unknown parameter '{name}'"
  | Stmt.returnBytes name =>
      match findParamType params name with
      | some ParamType.bytes => pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' returnBytes '{name}' requires bytes parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnBytes references unknown parameter '{name}'"
  | Stmt.returnStorageWords name =>
      match findParamType params name with
      | some ty =>
          if isStorageWordArrayParam ty then
            pure ()
          else
            throw s!"Compilation error: function '{fnName}' returnStorageWords '{name}' requires bytes32[] or uint256[] parameter, got {repr ty}"
      | none =>
          throw s!"Compilation error: function '{fnName}' returnStorageWords references unknown parameter '{name}'"
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateStmtParamReferences fnName params)
      elseBranch.forM (validateStmtParamReferences fnName params)
  | Stmt.forEach _ _ body => do
      body.forM (validateStmtParamReferences fnName params)
  | _ => pure ()

private partial def validateReturnShapesInStmt (fnName : String)
    (expectedReturns : List ParamType) (isInternal : Bool) : Stmt → Except String Unit
  | Stmt.return _ =>
      if isInternal then
        match expectedReturns with
        | [_] => pure ()
        | [] =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares no return values"
        | _ =>
            throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else if expectedReturns.length > 1 then
        throw s!"Compilation error: function '{fnName}' uses Stmt.return but declares multiple return values; use Stmt.returnValues"
      else
        pure ()
  | Stmt.returnValues values =>
      if expectedReturns.isEmpty then
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnValues but declares no return values"
      else if values.length != expectedReturns.length then
        throw s!"Compilation error: function '{fnName}' returnValues count mismatch: expected {expectedReturns.length}, got {values.length}"
      else
        pure ()
  | Stmt.returnArray _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnArray; only static returns via Stmt.return/Stmt.returnValues are supported (Issue #625)."
      else if expectedReturns == [ParamType.array ParamType.uint256] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnArray but declared returns are {repr expectedReturns}"
  | Stmt.returnBytes _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnBytes; only static returns via Stmt.return/Stmt.returnValues are supported (Issue #625)."
      else if expectedReturns == [ParamType.bytes] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnBytes but declared returns are {repr expectedReturns}"
  | Stmt.returnStorageWords _ =>
      if isInternal then
        throw s!"Compilation error: internal function '{fnName}' cannot use Stmt.returnStorageWords; only static returns via Stmt.return/Stmt.returnValues are supported (Issue #625)."
      else if expectedReturns == [ParamType.array ParamType.uint256] then
        pure ()
      else
        throw s!"Compilation error: function '{fnName}' uses Stmt.returnStorageWords but declared returns are {repr expectedReturns}"
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateReturnShapesInStmt fnName expectedReturns isInternal)
      elseBranch.forM (validateReturnShapesInStmt fnName expectedReturns isInternal)
  | Stmt.forEach _ _ body =>
      body.forM (validateReturnShapesInStmt fnName expectedReturns isInternal)
  | _ => pure ()

private def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  let returns ← functionReturns spec
  spec.body.forM (validateReturnShapesInStmt spec.name returns spec.isInternal)
  spec.body.forM (validateStmtParamReferences spec.name spec.params)

private def issue586Ref : String :=
  "Issue #586 (Solidity interop profile)"

private def validateConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateStmtParamReferences "constructor" spec.params)

private def validateBytesCustomErrorArg (fnName errorName : String) (params : List Param)
    (arg : Expr) : Except String Unit := do
  match arg with
  | Expr.param name =>
      match findParamType params name with
      | some ParamType.bytes => pure ()
      | some ty =>
          throw s!"Compilation error: function '{fnName}' custom error '{errorName}' expects bytes arg to reference a bytes parameter, got {repr ty} ({issue586Ref})."
      | none =>
          throw s!"Compilation error: function '{fnName}' custom error '{errorName}' references unknown parameter '{name}' ({issue586Ref})."
  | _ =>
      throw s!"Compilation error: function '{fnName}' custom error '{errorName}' bytes parameter currently requires direct bytes parameter reference ({issue586Ref})."

private partial def validateCustomErrorArgShapesInStmt (fnName : String) (params : List Param)
    (errors : List ErrorDef) : Stmt → Except String Unit
  | Stmt.requireError _ errorName args | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      if errorDef.params.length != args.length then
        throw s!"Compilation error: custom error '{errorName}' expects {errorDef.params.length} args, got {args.length}"
      for (ty, arg) in errorDef.params.zip args do
        if ty == ParamType.bytes then
          validateBytesCustomErrorArg fnName errorName params arg
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateCustomErrorArgShapesInStmt fnName params errors)
      elseBranch.forM (validateCustomErrorArgShapesInStmt fnName params errors)
  | Stmt.forEach _ _ body =>
      body.forM (validateCustomErrorArgShapesInStmt fnName params errors)
  | _ => pure ()

private def validateCustomErrorArgShapesInFunction (spec : FunctionSpec) (errors : List ErrorDef) :
    Except String Unit := do
  spec.body.forM (validateCustomErrorArgShapesInStmt spec.name spec.params errors)

private partial def eventIsDynamicType : ParamType → Bool
  | ParamType.uint256 => false
  | ParamType.address => false
  | ParamType.bool => false
  | ParamType.bytes32 => false
  | ParamType.array _ => true
  | ParamType.bytes => true
  | ParamType.fixedArray elemTy _ => eventIsDynamicType elemTy
  | ParamType.tuple elemTys => elemTys.any eventIsDynamicType

private partial def eventHeadWordSize : ParamType → Nat
  | ty =>
      if eventIsDynamicType ty then
        32
      else
        match ty with
        | ParamType.fixedArray elemTy n => n * eventHeadWordSize elemTy
        | ParamType.tuple elemTys => (elemTys.map eventHeadWordSize).foldl (· + ·) 0
        | _ => 32

private def indexedDynamicArrayElemSupported (elemTy : ParamType) : Bool :=
  !eventIsDynamicType elemTy &&
    eventHeadWordSize elemTy > 0

private partial def validateEventArgShapesInStmt (fnName : String) (params : List Param)
    (events : List EventDef) : Stmt → Except String Unit
  | Stmt.emit eventName args => do
      let eventDef ←
        match events.find? (·.name == eventName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if eventDef.params.length != args.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      for (eventParam, arg) in eventDef.params.zip args do
        match arg with
        | Expr.param name =>
            match findParamType params name with
            | some ty =>
                if ty != eventParam.ty then
                  throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
            | none =>
                throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
        | _ => pure ()
        if eventParam.kind == EventParamKind.unindexed then
          match eventParam.ty with
          | ParamType.array elemTy =>
              if indexedDynamicArrayElemSupported elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else
                throw s!"Compilation error: function '{fnName}' event '{eventName}' unindexed array param '{eventParam.name}' has unsupported element type {repr elemTy} ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
              if eventIsDynamicType eventParam.ty then
                throw s!"Compilation error: function '{fnName}' event '{eventName}' unindexed param '{eventParam.name}' has dynamic composite type {repr eventParam.ty}, which is not supported yet ({issue586Ref}). For now, use scalar fields/static tuples/static fixed arrays or bytes payloads."
              else
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed static composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | ParamType.bytes =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' expects bytes arg to reference a bytes parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' unindexed bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
          | _ => pure ()
        if eventParam.kind == EventParamKind.indexed then
          match eventParam.ty with
          | ParamType.bytes =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' expects bytes arg to reference a bytes parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' indexed bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
          | ParamType.array elemTy =>
              if indexedDynamicArrayElemSupported elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' indexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else
                throw s!"Compilation error: function '{fnName}' event '{eventName}' indexed array param '{eventParam.name}' has unsupported element type {repr elemTy} ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
              if eventIsDynamicType eventParam.ty then
                throw s!"Compilation error: function '{fnName}' event '{eventName}' indexed param '{eventParam.name}' has dynamic composite type {repr eventParam.ty}, which is not supported yet ({issue586Ref})."
              else
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' indexed static composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | _ => pure ()
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateEventArgShapesInStmt fnName params events)
      elseBranch.forM (validateEventArgShapesInStmt fnName params events)
  | Stmt.forEach _ _ body =>
      body.forM (validateEventArgShapesInStmt fnName params events)
  | _ => pure ()

private def validateEventArgShapesInFunction (spec : FunctionSpec) (events : List EventDef) :
    Except String Unit := do
  spec.body.forM (validateEventArgShapesInStmt spec.name spec.params events)

private def normalizeEventWord (ty : ParamType) (expr : YulExpr) : YulExpr :=
  match ty with
  | ParamType.address => YulExpr.call "and" [expr, YulExpr.hex ((2^160) - 1)]
  | ParamType.bool => yulToBool expr
  | _ => expr

private partial def staticCompositeLeaves (baseName : String) (ty : ParamType) :
    List (ParamType × YulExpr) :=
  match ty with
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(ty, YulExpr.ident baseName)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeaves s!"{baseName}_{i}" elemTy
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) : List (ParamType × YulExpr) :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeaves s!"{baseName}_{idx}" elemTy ++ go rest (idx + 1)
      go elemTys 0
  | _ => []

private partial def staticCompositeLeafTypeOffsets
    (baseOffset : Nat) (ty : ParamType) : List (Nat × ParamType) :=
  match ty with
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [(baseOffset, ty)]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        staticCompositeLeafTypeOffsets (baseOffset + i * eventHeadWordSize elemTy) elemTy
  | ParamType.tuple elemTys =>
      let rec go (remaining : List ParamType) (curOffset : Nat) : List (Nat × ParamType) :=
        match remaining with
        | [] => []
        | elemTy :: rest =>
            staticCompositeLeafTypeOffsets curOffset elemTy ++
              go rest (curOffset + eventHeadWordSize elemTy)
      go elemTys baseOffset
  | _ => []

private def isLowLevelCallName (name : String) : Bool :=
  ["call", "staticcall", "delegatecall", "callcode"].contains name

private def isInteropBuiltinCallName (name : String) : Bool :=
  (isLowLevelCallName name) ||
    ["create", "create2", "balance", "selfbalance", "origin", "caller", "callvalue",
     "gasprice", "blockhash", "coinbase", "timestamp", "number", "difficulty",
     "prevrandao", "gaslimit", "chainid", "basefee", "blobbasefee", "blobhash", "gas",
     "extcodesize", "extcodecopy", "extcodehash", "returndatasize", "returndatacopy",
     "selfdestruct", "invalid"].contains name

private def isInteropEntrypointName (name : String) : Bool :=
  ["fallback", "receive"].contains name

private def lowLevelCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported low-level call '{name}' ({issue586Ref}). Use a verified linked external function wrapper instead of raw call/staticcall/delegatecall/callcode."

private def interopBuiltinCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported interop builtin call '{name}' ({issue586Ref}). Use a verified linked external wrapper or pass the required value through explicit function parameters."

private def unsupportedInteropCallError (context : String) (name : String) : Except String Unit :=
  if isLowLevelCallName name then
    lowLevelCallUnsupportedError context name
  else
    interopBuiltinCallUnsupportedError context name

private partial def validateInteropExpr (context : String) : Expr → Except String Unit
  | Expr.msgValue =>
      pure ()
  | Expr.externalCall name args => do
      if isInteropBuiltinCallName name then
        unsupportedInteropCallError context name
      args.forM (validateInteropExpr context)
  | Expr.mapping _ key => validateInteropExpr context key
  | Expr.mapping2 _ key1 key2 => do
      validateInteropExpr context key1
      validateInteropExpr context key2
  | Expr.mappingUint _ key => validateInteropExpr context key
  | Expr.internalCall _ args =>
      args.forM (validateInteropExpr context)
  | Expr.arrayElement _ index =>
      validateInteropExpr context index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b => do
      validateInteropExpr context a
      validateInteropExpr context b
  | Expr.bitNot a | Expr.logicalNot a =>
      validateInteropExpr context a
  | _ =>
      pure ()

private partial def validateInteropStmt (context : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInteropExpr context value
  | Stmt.requireError cond _ args => do
      validateInteropExpr context cond
      args.forM (validateInteropExpr context)
  | Stmt.revertError _ args =>
      args.forM (validateInteropExpr context)
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value => do
      validateInteropExpr context key
      validateInteropExpr context value
  | Stmt.setMapping2 _ key1 key2 value => do
      validateInteropExpr context key1
      validateInteropExpr context key2
      validateInteropExpr context value
  | Stmt.ite cond thenBranch elseBranch => do
      validateInteropExpr context cond
      thenBranch.forM (validateInteropStmt context)
      elseBranch.forM (validateInteropStmt context)
  | Stmt.forEach _ count body => do
      validateInteropExpr context count
      body.forM (validateInteropStmt context)
  | Stmt.emit _ args =>
      args.forM (validateInteropExpr context)
  | Stmt.internalCall _ args =>
      args.forM (validateInteropExpr context)
  | Stmt.internalCallAssign _ _ args =>
      args.forM (validateInteropExpr context)
  | Stmt.returnValues values =>
      values.forM (validateInteropExpr context)
  | _ =>
      pure ()

private def validateInteropFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInteropStmt s!"function '{spec.name}'")

private def validateInteropExternalSpec (spec : ExternalFunction) : Except String Unit := do
  if isInteropBuiltinCallName spec.name then
    unsupportedInteropCallError s!"external declaration '{spec.name}'" spec.name

private def validateInteropConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateInteropStmt "constructor")

private def validateSpecialEntrypointSpec (spec : FunctionSpec) : Except String Unit := do
  if !isInteropEntrypointName spec.name then
    pure ()
  else
    if spec.isInternal then
      throw s!"Compilation error: function '{spec.name}' cannot be marked internal ({issue586Ref})"
    if !spec.params.isEmpty then
      throw s!"Compilation error: function '{spec.name}' must not declare parameters ({issue586Ref})"
    let returns ← functionReturns spec
    if !returns.isEmpty then
      throw s!"Compilation error: function '{spec.name}' must not return values ({issue586Ref})"
    if spec.name == "receive" && !spec.isPayable then
      throw s!"Compilation error: function 'receive' must be payable ({issue586Ref})"

private def issue625Ref : String :=
  "Issue #625 (internal function multi-return support)"

private def findInternalFunctionByName (functions : List FunctionSpec)
    (callerName calleeName : String) : Except String FunctionSpec := do
  let candidates := functions.filter (fun fn => fn.isInternal && fn.name == calleeName)
  match candidates with
  | [fn] => pure fn
  | [] =>
      throw s!"Compilation error: function '{callerName}' references unknown internal function '{calleeName}' ({issue625Ref})."
  | _ =>
      throw s!"Compilation error: function '{callerName}' references ambiguous internal function '{calleeName}' ({issue625Ref})."

private partial def validateInternalCallShapesInExpr
    (functions : List FunctionSpec) (callerName : String) : Expr → Except String Unit
  | Expr.internalCall calleeName args => do
      args.forM (validateInternalCallShapesInExpr functions callerName)
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if returns.length != 1 then
        throw s!"Compilation error: function '{callerName}' uses Expr.internalCall '{calleeName}' but callee returns {returns.length} values; use Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | Expr.mapping _ key =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.mapping2 _ key1 key2 => do
      validateInternalCallShapesInExpr functions callerName key1
      validateInternalCallShapesInExpr functions callerName key2
  | Expr.mappingUint _ key =>
      validateInternalCallShapesInExpr functions callerName key
  | Expr.arrayElement _ index =>
      validateInternalCallShapesInExpr functions callerName index
  | Expr.add a b | Expr.sub a b | Expr.mul a b | Expr.div a b | Expr.mod a b |
    Expr.bitAnd a b | Expr.bitOr a b | Expr.bitXor a b | Expr.shl a b | Expr.shr a b |
    Expr.eq a b | Expr.ge a b | Expr.gt a b | Expr.lt a b | Expr.le a b |
    Expr.logicalAnd a b | Expr.logicalOr a b => do
      validateInternalCallShapesInExpr functions callerName a
      validateInternalCallShapesInExpr functions callerName b
  | Expr.bitNot a | Expr.logicalNot a =>
      validateInternalCallShapesInExpr functions callerName a
  | _ =>
      pure ()

private partial def validateInternalCallShapesInStmt
    (functions : List FunctionSpec) (callerName : String) : Stmt → Except String Unit
  | Stmt.letVar _ value | Stmt.assignVar _ value | Stmt.setStorage _ value |
    Stmt.return value | Stmt.require value _ =>
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.requireError cond _ args => do
      validateInternalCallShapesInExpr functions callerName cond
      args.forM (validateInternalCallShapesInExpr functions callerName)
  | Stmt.revertError _ args =>
      args.forM (validateInternalCallShapesInExpr functions callerName)
  | Stmt.setMapping _ key value | Stmt.setMappingUint _ key value => do
      validateInternalCallShapesInExpr functions callerName key
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.setMapping2 _ key1 key2 value => do
      validateInternalCallShapesInExpr functions callerName key1
      validateInternalCallShapesInExpr functions callerName key2
      validateInternalCallShapesInExpr functions callerName value
  | Stmt.ite cond thenBranch elseBranch => do
      validateInternalCallShapesInExpr functions callerName cond
      thenBranch.forM (validateInternalCallShapesInStmt functions callerName)
      elseBranch.forM (validateInternalCallShapesInStmt functions callerName)
  | Stmt.forEach _ count body => do
      validateInternalCallShapesInExpr functions callerName count
      body.forM (validateInternalCallShapesInStmt functions callerName)
  | Stmt.emit _ args =>
      args.forM (validateInternalCallShapesInExpr functions callerName)
  | Stmt.returnValues values =>
      values.forM (validateInternalCallShapesInExpr functions callerName)
  | Stmt.internalCall calleeName args => do
      args.forM (validateInternalCallShapesInExpr functions callerName)
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if !returns.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCall '{calleeName}' but callee returns {returns.length} values; use Expr.internalCall for single-return or Stmt.internalCallAssign for multi-return calls ({issue625Ref})."
  | Stmt.internalCallAssign names calleeName args => do
      if names.isEmpty then
        throw s!"Compilation error: function '{callerName}' uses Stmt.internalCallAssign with no target variables ({issue625Ref})."
      args.forM (validateInternalCallShapesInExpr functions callerName)
      let callee ← findInternalFunctionByName functions callerName calleeName
      if args.length != callee.params.length then
        throw s!"Compilation error: function '{callerName}' calls internal function '{calleeName}' with {args.length} args, expected {callee.params.length} ({issue625Ref})."
      let returns ← functionReturns callee
      if returns.length != names.length then
        throw s!"Compilation error: function '{callerName}' binds {names.length} values from internal function '{calleeName}', but callee returns {returns.length} ({issue625Ref})."
  | _ =>
      pure ()

private def validateInternalCallShapesInFunction (functions : List FunctionSpec)
    (spec : FunctionSpec) : Except String Unit := do
  spec.body.forM (validateInternalCallShapesInStmt functions spec.name)

private def compileMappingSlotWrite (fields : List Field) (field : String)
    (keyExpr valueExpr : YulExpr) (label : String) : Except String (List YulStmt) :=
  if !isMapping fields field then
    throw s!"Compilation error: field '{field}' is not a mapping"
  else
    match findFieldSlot fields field with
    | some slot =>
        pure [
          YulStmt.expr (YulExpr.call "sstore" [
            YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr],
            valueExpr
          ])
        ]
    | none => throw s!"Compilation error: unknown mapping field '{field}' in {label}"

private def supportedCustomErrorParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 | ParamType.bytes => true
  | _ => false

private def encodeStaticCustomErrorArg (errorName : String) (ty : ParamType) (argExpr : YulExpr) :
    Except String YulExpr :=
  match ty with
  | ParamType.uint256 | ParamType.bytes32 =>
      pure argExpr
  | ParamType.address =>
      pure (YulExpr.call "and" [argExpr, YulExpr.hex ((2^160) - 1)])
  | ParamType.bool =>
      pure (yulToBool argExpr)
  | _ =>
      throw s!"Compilation error: custom error '{errorName}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref})."

private def revertWithCustomError (dynamicSource : DynamicDataSource)
    (errorDef : ErrorDef) (sourceArgs : List Expr) (args : List YulExpr) :
    Except String (List YulStmt) := do
  if errorDef.params.length != args.length || sourceArgs.length != args.length then
    throw s!"Compilation error: custom error '{errorDef.name}' expects {errorDef.params.length} args, got {args.length}"
  let sigBytes := bytesFromString (errorSignature errorDef)
  let storePtr := YulStmt.let_ "__err_ptr" (YulExpr.call "mload" [YulExpr.lit 0x40])
  let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
    YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [YulExpr.ident "__err_ptr", YulExpr.lit (idx * 32)],
      YulExpr.hex (wordFromBytes chunk)
    ])
  let hashStmt := YulStmt.let_ "__err_hash"
    (YulExpr.call "keccak256" [YulExpr.ident "__err_ptr", YulExpr.lit sigBytes.length])
  let selectorStmt := YulStmt.let_ "__err_selector"
    (YulExpr.call "shl" [YulExpr.lit 224, YulExpr.call "shr" [YulExpr.lit 224, YulExpr.ident "__err_hash"]])
  let selectorStore := YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.ident "__err_selector"])
  let headSize := errorDef.params.length * 32
  let tailInit := YulStmt.let_ "__err_tail" (YulExpr.lit headSize)
  let argsWithSources := (errorDef.params.zip sourceArgs).zip args |>.map (fun ((ty, srcExpr), argExpr) =>
    (ty, srcExpr, argExpr))
  let argStores ← argsWithSources.zipIdx.mapM fun ((ty, srcExpr, argExpr), idx) => do
    let headOffset := 4 + idx * 32
    match ty with
    | ParamType.bytes =>
        match srcExpr with
        | Expr.param name =>
            let lenName := s!"__err_arg{idx}_len"
            let dstName := s!"__err_arg{idx}_dst"
            let paddedName := s!"__err_arg{idx}_padded"
            pure ([
              YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, YulExpr.ident "__err_tail"]),
              YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
              YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]),
              YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
            ] ++ dynamicCopyData dynamicSource
              (YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32])
              (YulExpr.ident s!"{name}_data_offset")
              (YulExpr.ident lenName) ++ [
              YulStmt.let_ paddedName (YulExpr.call "and" [
                YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
                YulExpr.call "not" [YulExpr.lit 31]
              ]),
              YulStmt.expr (YulExpr.call "mstore" [
                YulExpr.call "add" [
                  YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                  YulExpr.ident lenName
                ],
                YulExpr.lit 0
              ]),
              YulStmt.assign "__err_tail" (YulExpr.call "add" [
                YulExpr.ident "__err_tail",
                YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
              ])
            ])
        | _ =>
            throw s!"Compilation error: custom error '{errorDef.name}' bytes parameter currently requires direct bytes parameter reference ({issue586Ref})."
    | _ =>
        let encoded ← encodeStaticCustomErrorArg errorDef.name ty argExpr
        pure [YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit headOffset, encoded])]
  let revertStmt := YulStmt.expr (YulExpr.call "revert" [
    YulExpr.lit 0,
    YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident "__err_tail"]
  ])
  pure [YulStmt.block ([storePtr] ++ sigStores ++ [hashStmt, selectorStmt, selectorStore, tailInit] ++ argStores.flatten ++ [revertStmt])]

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value` (for internal Yul functions)
-- instead of EVM RETURN which terminates the entire call.
mutual
def compileStmtList (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false) :
    List Stmt → Except String (List YulStmt)
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields events errors dynamicSource internalRetNames isInternal s
      let tail ← compileStmtList fields events errors dynamicSource internalRetNames isInternal ss
      pure (head ++ tail)

def compileStmt (fields : List Field) (events : List EventDef := [])
    (errors : List ErrorDef := [])
    (dynamicSource : DynamicDataSource := .calldata)
    (internalRetNames : List String := [])
    (isInternal : Bool := false) :
    Stmt → Except String (List YulStmt)
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExpr fields dynamicSource value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExpr fields dynamicSource value)]
  | Stmt.setStorage field value =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use setMapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, ← compileExpr fields dynamicSource value])]
      | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMapping"
  | Stmt.setMapping2 field key1 key2 value =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          let key1Expr ← compileExpr fields dynamicSource key1
          let key2Expr ← compileExpr fields dynamicSource key2
          let valueExpr ← compileExpr fields dynamicSource value
          let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
          pure [
            YulStmt.expr (YulExpr.call "sstore" [
              YulExpr.call "mappingSlot" [innerSlot, key2Expr],
              valueExpr
            ])
          ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2"
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field
        (← compileExpr fields dynamicSource key)
        (← compileExpr fields dynamicSource value)
        "setMappingUint"
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.requireError cond errorName args => do
      let failCond ← compileRequireFailCond fields dynamicSource cond
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      let revertStmts ← revertWithCustomError dynamicSource errorDef args argExprs
      pure [YulStmt.if_ failCond revertStmts]
  | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      let argExprs ← compileExprList fields dynamicSource args
      revertWithCustomError dynamicSource errorDef args argExprs
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields dynamicSource value
      if isInternal then
        match internalRetNames with
        | retName :: _ => pure [YulStmt.assign retName valueExpr]
        | [] => throw s!"Compilation error: internal return target is missing"
      else
        pure [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExpr fields dynamicSource cond
      let thenStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal thenBranch
      let elseStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal elseBranch
      if elseBranch.isEmpty then
        -- Simple if (no else)
        pure [YulStmt.if_ condExpr thenStmts]
      else
        -- If/else: cache condition in a block-scoped local to avoid re-evaluation
        -- after then-branch may have mutated state.
        -- Wrapped in block { } so __ite_cond doesn't collide with other ite statements.
        pure [YulStmt.block [
          YulStmt.let_ "__ite_cond" condExpr,
          YulStmt.if_ (YulExpr.ident "__ite_cond") thenStmts,
          YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ite_cond"]) elseStmts
        ]]

  | Stmt.forEach varName count body => do
      -- Bounded loop: for { let i := 0 } lt(i, count) { i := add(i, 1) } { body } (#179)
      let countExpr ← compileExpr fields dynamicSource count
      let bodyStmts ← compileStmtList fields events errors dynamicSource internalRetNames isInternal body
      let initStmts := [YulStmt.let_ varName (YulExpr.lit 0)]
      let condExpr := YulExpr.call "lt" [YulExpr.ident varName, countExpr]
      let postStmts := [YulStmt.assign varName (YulExpr.call "add" [YulExpr.ident varName, YulExpr.lit 1])]
      pure [YulStmt.for_ initStmts condExpr postStmts bodyStmts]

  | Stmt.emit eventName args => do
      let eventDef? := events.find? (·.name == eventName)
      let eventDef ←
        match eventDef? with
        | some e => pure e
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if args.length != eventDef.params.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      let compiledArgs ← compileExprList fields dynamicSource args
      let zippedWithSource := (eventDef.params.zip args).zip compiledArgs |>.map (fun ((p, srcExpr), argExpr) =>
        (p, srcExpr, argExpr))
      let indexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.indexed)
      let unindexed := zippedWithSource.filter (fun (p, _, _) => p.kind == EventParamKind.unindexed)
      if indexed.length > 3 then
        throw s!"Compilation error: event '{eventName}' has {indexed.length} indexed params; max is 3"
      let sig := eventSignature eventDef
      let sigBytes := bytesFromString sig
      let freeMemPtr := YulExpr.call "mload" [YulExpr.lit 0x40]
      let storePtr := YulStmt.let_ "__evt_ptr" freeMemPtr
      let sigStores := (chunkBytes32 sigBytes).zipIdx.map fun (chunk, idx) =>
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (idx * 32)],
          YulExpr.hex (wordFromBytes chunk)
        ])
      let topic0Expr := YulExpr.call "keccak256" [YulExpr.ident "__evt_ptr", YulExpr.lit sigBytes.length]
      let topic0Store := YulStmt.let_ "__evt_topic0" topic0Expr
      let unindexedHeadSize := (unindexed.map (fun (p, _, _) => eventHeadWordSize p.ty)).foldl (· + ·) 0
      let hasUnindexedDynamicData := unindexed.any (fun (p, _, _) => eventIsDynamicType p.ty)
      let unindexedTailInit :=
        if hasUnindexedDynamicData then
          [YulStmt.let_ "__evt_data_tail" (YulExpr.lit unindexedHeadSize)]
        else
          []
      let rec compileUnindexedStores
          (remaining : List (EventParam × Expr × YulExpr)) (argIdx : Nat) (headOffset : Nat) :
          Except String (List YulStmt) := do
        match remaining with
        | [] => pure []
        | (p, srcExpr, argExpr) :: rest =>
            let curHeadPtr := YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit headOffset]
            let current ←
              match p.ty with
              | ParamType.bytes =>
                  match srcExpr with
                  | Expr.param name =>
                      let lenName := s!"__evt_arg{argIdx}_len"
                      let dstName := s!"__evt_arg{argIdx}_dst"
                      let paddedName := s!"__evt_arg{argIdx}_padded"
                      pure ([
                        YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                        YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                        YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                        YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                      ] ++ dynamicCopyData dynamicSource
                        (YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32])
                        (YulExpr.ident s!"{name}_data_offset")
                        (YulExpr.ident lenName) ++ [
                        YulStmt.let_ paddedName (YulExpr.call "and" [
                          YulExpr.call "add" [YulExpr.ident lenName, YulExpr.lit 31],
                          YulExpr.call "not" [YulExpr.lit 31]
                        ]),
                        YulStmt.expr (YulExpr.call "mstore" [
                          YulExpr.call "add" [
                            YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                            YulExpr.ident lenName
                          ],
                          YulExpr.lit 0
                        ]),
                        YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                          YulExpr.ident "__evt_data_tail",
                          YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                        ])
                      ])
                  | _ =>
                      throw s!"Compilation error: unindexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
              | ParamType.array elemTy =>
                  if indexedDynamicArrayElemSupported elemTy then
                    match srcExpr with
                    | Expr.param name =>
                        let lenName := s!"__evt_arg{argIdx}_len"
                        let dstName := s!"__evt_arg{argIdx}_dst"
                        let elemWordSize := eventHeadWordSize elemTy
                        let byteLenName := s!"__evt_arg{argIdx}_byte_len"
                        let paddedName := s!"__evt_arg{argIdx}_padded"
                        let elemBaseName := s!"__evt_arg{argIdx}_elem_base"
                        let elemOutBaseName := s!"__evt_arg{argIdx}_out_base"
                        let loopIndexName := s!"__evt_arg{argIdx}_i"
                        let leafStores :=
                          (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                            let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                              YulExpr.ident elemBaseName,
                              YulExpr.lit leafOffset
                            ])
                            YulStmt.expr (YulExpr.call "mstore" [
                              YulExpr.call "add" [YulExpr.ident elemOutBaseName, YulExpr.lit leafOffset],
                              normalizeEventWord leafTy loadExpr
                            ])
                        pure ([
                          YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, YulExpr.ident "__evt_data_tail"]),
                          YulStmt.let_ lenName (YulExpr.ident s!"{name}_length"),
                          YulStmt.let_ dstName (YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.ident "__evt_data_tail"]),
                          YulStmt.expr (YulExpr.call "mstore" [YulExpr.ident dstName, YulExpr.ident lenName]),
                          YulStmt.let_ byteLenName (YulExpr.call "mul" [YulExpr.ident lenName, YulExpr.lit elemWordSize]),
                          YulStmt.for_
                            [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                            (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident lenName])
                            [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                            ([
                              YulStmt.let_ elemBaseName (YulExpr.call "add" [
                                YulExpr.ident s!"{name}_data_offset",
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ]),
                              YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                                YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                                YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                              ])
                            ] ++ leafStores),
                          YulStmt.let_ paddedName (YulExpr.call "and" [
                            YulExpr.call "add" [YulExpr.ident byteLenName, YulExpr.lit 31],
                            YulExpr.call "not" [YulExpr.lit 31]
                          ]),
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [
                              YulExpr.call "add" [YulExpr.ident dstName, YulExpr.lit 32],
                              YulExpr.ident byteLenName
                            ],
                            YulExpr.lit 0
                          ]),
                          YulStmt.assign "__evt_data_tail" (YulExpr.call "add" [
                            YulExpr.ident "__evt_data_tail",
                            YulExpr.call "add" [YulExpr.lit 32, YulExpr.ident paddedName]
                          ])
                        ])
                    | _ =>
                        throw s!"Compilation error: unindexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
                  else
                    throw s!"Compilation error: unindexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
              | ParamType.fixedArray _ _ | ParamType.tuple _ =>
                  if eventIsDynamicType p.ty then
                    throw s!"Compilation error: unindexed dynamic composite event param '{p.name}' in event '{eventName}' is not supported yet ({issue586Ref})."
                  else
                    match srcExpr with
                    | Expr.param name =>
                        let leaves := staticCompositeLeaves name p.ty
                        let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                          YulStmt.expr (YulExpr.call "mstore" [
                            YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (headOffset + wordIdx * 32)],
                            normalizeEventWord leafTy leafExpr
                          ])
                        pure stores
                    | _ =>
                        throw s!"Compilation error: unindexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              | _ =>
                  pure [YulStmt.expr (YulExpr.call "mstore" [curHeadPtr, normalizeEventWord p.ty argExpr])]
            let tail ← compileUnindexedStores rest (argIdx + 1) (headOffset + eventHeadWordSize p.ty)
            pure (current ++ tail)
      let unindexedStores ← compileUnindexedStores unindexed 0 0
      let dataSizeExpr :=
        if hasUnindexedDynamicData then YulExpr.ident "__evt_data_tail" else YulExpr.lit unindexedHeadSize
      let indexedTopicParts ← indexed.zipIdx.mapM fun ((p, srcExpr, argExpr), idx) => do
        match p.ty with
        | ParamType.bytes =>
            match srcExpr with
            | Expr.param name =>
                let topicName := s!"__evt_topic{idx + 1}"
                let hashStmts :=
                  dynamicCopyData dynamicSource
                    (YulExpr.ident "__evt_ptr")
                    (YulExpr.ident s!"{name}_data_offset")
                    (YulExpr.ident s!"{name}_length") ++ [
                  YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.ident s!"{name}_length"
                  ])
                ]
                pure (hashStmts, YulExpr.ident topicName)
            | _ =>
                throw s!"Compilation error: indexed bytes event param '{p.name}' in event '{eventName}' currently requires direct bytes parameter reference ({issue586Ref})."
        | ParamType.array elemTy =>
            if indexedDynamicArrayElemSupported elemTy then
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let byteLenName := s!"__evt_arg{idx}_byte_len"
                  let elemWordSize := eventHeadWordSize elemTy
                  let elemBaseName := s!"__evt_arg{idx}_elem_base"
                  let elemOutBaseName := s!"__evt_arg{idx}_out_base"
                  let loopIndexName := s!"__evt_arg{idx}_i"
                  let leafStores :=
                    (staticCompositeLeafTypeOffsets 0 elemTy).map fun (leafOffset, leafTy) =>
                      let loadExpr := dynamicWordLoad dynamicSource (YulExpr.call "add" [
                        YulExpr.ident elemBaseName,
                        YulExpr.lit leafOffset
                      ])
                      YulStmt.expr (YulExpr.call "mstore" [
                        YulExpr.call "add" [
                          YulExpr.ident elemOutBaseName,
                          YulExpr.lit leafOffset
                        ],
                        normalizeEventWord leafTy loadExpr
                      ])
                  let hashStmts := [
                    YulStmt.let_ byteLenName (YulExpr.call "mul" [
                      YulExpr.ident s!"{name}_length",
                      YulExpr.lit elemWordSize
                    ]),
                    YulStmt.for_
                      [YulStmt.let_ loopIndexName (YulExpr.lit 0)]
                      (YulExpr.call "lt" [YulExpr.ident loopIndexName, YulExpr.ident s!"{name}_length"])
                      [YulStmt.assign loopIndexName (YulExpr.call "add" [YulExpr.ident loopIndexName, YulExpr.lit 1])]
                      ([
                        YulStmt.let_ elemBaseName (YulExpr.call "add" [
                          YulExpr.ident s!"{name}_data_offset",
                          YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                        ]),
                        YulStmt.let_ elemOutBaseName (YulExpr.call "add" [
                          YulExpr.ident "__evt_ptr",
                          YulExpr.call "mul" [YulExpr.ident loopIndexName, YulExpr.lit elemWordSize]
                        ])
                      ] ++ leafStores),
                    YulStmt.let_ topicName (YulExpr.call "keccak256" [
                      YulExpr.ident "__evt_ptr",
                      YulExpr.ident byteLenName
                    ])
                  ]
                  pure (hashStmts, YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed dynamic array event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
            else
              throw s!"Compilation error: indexed array event param '{p.name}' in event '{eventName}' has unsupported element type {repr elemTy} ({issue586Ref})."
        | ParamType.fixedArray _ _ | ParamType.tuple _ =>
            if eventIsDynamicType p.ty then
              throw s!"Compilation error: indexed dynamic composite event param '{p.name}' in event '{eventName}' is not supported yet ({issue586Ref})."
            else
              match srcExpr with
              | Expr.param name =>
                  let topicName := s!"__evt_topic{idx + 1}"
                  let leaves := staticCompositeLeaves name p.ty
                  let stores := leaves.zipIdx.map fun ((leafTy, leafExpr), wordIdx) =>
                    YulStmt.expr (YulExpr.call "mstore" [
                      YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (wordIdx * 32)],
                      normalizeEventWord leafTy leafExpr
                    ])
                  pure (stores ++ [YulStmt.let_ topicName (YulExpr.call "keccak256" [
                    YulExpr.ident "__evt_ptr",
                    YulExpr.lit (eventHeadWordSize p.ty)
                  ])], YulExpr.ident topicName)
              | _ =>
                  throw s!"Compilation error: indexed static composite event param '{p.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
        | ParamType.address =>
            pure ([], YulExpr.call "and" [argExpr, YulExpr.hex ((2^160) - 1)])
        | ParamType.bool =>
            pure ([], yulToBool argExpr)
        | _ =>
            pure ([], argExpr)
      let indexedTopicStmts := indexedTopicParts.flatMap (·.1)
      let topicExprs := [YulExpr.ident "__evt_topic0"] ++ indexedTopicParts.map (·.2)
      let logFn := match indexed.length with
        | 0 => "log1"
        | 1 => "log2"
        | 2 => "log3"
        | _ => "log4"
      let logArgs := [YulExpr.ident "__evt_ptr", dataSizeExpr] ++ topicExprs
      let logStmt := YulStmt.expr (YulExpr.call logFn logArgs)
      pure [YulStmt.block ([storePtr] ++ sigStores ++ [topic0Store] ++ indexedTopicStmts ++ unindexedTailInit ++ unindexedStores ++ [logStmt])]

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.expr (YulExpr.call s!"internal_{functionName}" argExprs)]
  | Stmt.internalCallAssign names functionName args => do
      let argExprs ← compileExprList fields dynamicSource args
      pure [YulStmt.letMany names (YulExpr.call s!"internal_{functionName}" argExprs)]
  | Stmt.returnValues values => do
      if isInternal then
        if values.length != internalRetNames.length then
          throw s!"Compilation error: internal return arity mismatch: expected {internalRetNames.length}, got {values.length}"
        else
          let compiled ← compileExprList fields dynamicSource values
          pure ((internalRetNames.zip compiled).map fun (name, valueExpr) =>
            YulStmt.assign name valueExpr)
      else if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprList fields dynamicSource values
        let stores := (compiled.zipIdx.map fun (valueExpr, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), valueExpr]))
        pure (stores ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit (values.length * 32)])])
  | Stmt.returnArray name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let byteLen := YulExpr.call "mul" [lenIdent, YulExpr.lit 32]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset byteLen ++ [
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, byteLen]])
      ])
  | Stmt.returnBytes name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let tailOffset := YulExpr.call "add" [YulExpr.lit 64, lenIdent]
      let paddedLen :=
        YulExpr.call "and" [
          YulExpr.call "add" [lenIdent, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      pure ([
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
      ] ++ dynamicCopyData dynamicSource (YulExpr.lit 64) dataOffset lenIdent ++ [
        YulStmt.expr (YulExpr.call "mstore" [tailOffset, YulExpr.lit 0]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, paddedLen]])
      ])
  | Stmt.returnStorageWords name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.for_
          [YulStmt.let_ "__i" (YulExpr.lit 0)]
          (YulExpr.call "lt" [YulExpr.ident "__i", lenIdent])
          [YulStmt.assign "__i" (YulExpr.call "add" [YulExpr.ident "__i", YulExpr.lit 1])]
          [
            YulStmt.let_ "__slot" (dynamicWordLoad dynamicSource (YulExpr.call "add" [
              dataOffset,
              YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]
            ])),
            YulStmt.expr (YulExpr.call "mstore" [
              YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]],
              YulExpr.call "sload" [YulExpr.ident "__slot"]
            ])
          ],
        YulStmt.expr (YulExpr.call "return" [
          YulExpr.lit 0,
          YulExpr.call "add" [YulExpr.lit 64, YulExpr.call "mul" [lenIdent, YulExpr.lit 32]]
        ])
      ]
end

private def isScalarParamType : ParamType → Bool
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 => true
  | _ => false

partial def isDynamicParamType : ParamType → Bool
  | ParamType.uint256 => false
  | ParamType.address => false
  | ParamType.bool => false
  | ParamType.bytes32 => false
  | ParamType.array _ => true
  | ParamType.bytes => true
  | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
  | ParamType.tuple elemTys =>
      elemTys.any isDynamicParamType

-- ABI head size for top-level parameters.
partial def paramHeadSize : ParamType → Nat
  | ty =>
      if isDynamicParamType ty then
        32
      else
        match ty with
        | ParamType.fixedArray elemTy n => n * paramHeadSize elemTy
        | ParamType.tuple elemTys => (elemTys.map paramHeadSize).foldl (· + ·) 0
        | _ => 32

private def genDynamicParamLoads
    (loadWord : YulExpr → YulExpr) (baseOffset : Nat) (name : String) (headOffset : Nat) :
    List YulStmt :=
  let offsetLoad := YulStmt.let_ s!"{name}_offset"
    (loadWord (YulExpr.lit headOffset))
  let relativeOffset := YulExpr.ident s!"{name}_offset"
  let absoluteOffset :=
    if baseOffset == 0 then
      relativeOffset
    else
      YulExpr.call "add" [YulExpr.lit baseOffset, relativeOffset]
  let lengthLoad := YulStmt.let_ s!"{name}_length"
    (loadWord absoluteOffset)
  let dataOffsetLoad := YulStmt.let_ s!"{name}_data_offset"
    (YulExpr.call "add" [absoluteOffset, YulExpr.lit 32])
  [offsetLoad, lengthLoad, dataOffsetLoad]

private def genScalarLoad
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  let load := loadWord (YulExpr.lit offset)
  match ty with
  | ParamType.uint256 =>
      [YulStmt.let_ name load]
  | ParamType.bytes32 =>
      [YulStmt.let_ name load]
  | ParamType.address =>
      [YulStmt.let_ name (YulExpr.call "and" [
        load,
        YulExpr.hex ((2^160) - 1)
      ])]
  | ParamType.bool =>
      [YulStmt.let_ name (YulExpr.call "iszero" [YulExpr.call "iszero" [
        load
      ]])]
  | _ => []

private partial def genStaticTypeLoads
    (loadWord : YulExpr → YulExpr) (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  match ty with
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      genScalarLoad loadWord name ty offset
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        genStaticTypeLoads loadWord s!"{name}_{i}" elemTy (offset + i * paramHeadSize elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) (curOffset : Nat) : List YulStmt :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            let elemName := s!"{name}_{idx}"
            let here := genStaticTypeLoads loadWord elemName elemTy curOffset
            here ++ go rest (idx + 1) (curOffset + paramHeadSize elemTy)
      go elemTys 0 offset
  | _ => []

private def genParamLoadsFrom
    (loadWord : YulExpr → YulExpr) (headStart : Nat) (baseOffset : Nat) (params : List Param) :
    List YulStmt :=
  let rec go (paramList : List Param) (headOffset : Nat) : List YulStmt :=
    match paramList with
    | [] => []
    | param :: rest =>
      let stmts := match param.ty with
        | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
          genScalarLoad loadWord param.name param.ty headOffset
        | ParamType.tuple elemTypes =>
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord baseOffset param.name headOffset
          else
            genStaticTypeLoads loadWord param.name (ParamType.tuple elemTypes) headOffset
        | ParamType.array _ =>
          genDynamicParamLoads loadWord baseOffset param.name headOffset
        | ParamType.fixedArray _ n =>
          -- Static fixed arrays are decoded inline recursively (including nested tuple members).
          -- For scalar element arrays we preserve `<name>` as an alias to `<name>_0`.
          if isDynamicParamType param.ty then
            genDynamicParamLoads loadWord baseOffset param.name headOffset
          else
            let staticLoads := genStaticTypeLoads loadWord param.name param.ty headOffset
            if n == 0 then staticLoads else
              -- Backward compatibility: keep `<name>` bound to first element for scalar fixed arrays.
              let firstAlias := match param.ty with
                | ParamType.fixedArray elemTy _ =>
                    if isScalarParamType elemTy then
                      [YulStmt.let_ param.name (YulExpr.ident s!"{param.name}_0")]
                    else
                      []
                | _ => []
              staticLoads ++ firstAlias
        | ParamType.bytes =>
          genDynamicParamLoads loadWord baseOffset param.name headOffset
      stmts ++ go rest (headOffset + paramHeadSize param.ty)
  go params headStart

-- Generate parameter loading code (from calldata)
def genParamLoads (params : List Param) : List YulStmt :=
  genParamLoadsFrom (fun pos => YulExpr.call "calldataload" [pos]) 4 4 params

-- Compile internal function to a Yul function definition (#181)
def compileInternalFunction (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (spec : FunctionSpec) :
    Except String YulStmt := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramNames := spec.params.map (·.name)
  let retNames := returns.zipIdx.map (fun (_, idx) => s!"__ret{idx}")
  let bodyStmts ← compileStmtList fields events errors
    (dynamicSource := .calldata) (internalRetNames := retNames) (isInternal := true) spec.body
  pure (YulStmt.funcDef s!"internal_{spec.name}" paramNames retNames bodyStmts)

-- Compile function spec to IR function
def compileFunctionSpec (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramLoads := genParamLoads spec.params
  let bodyChunks ← spec.body.mapM (compileStmt fields events errors)
  let allStmts := paramLoads ++ bodyChunks.flatten
  let retType := match returns with
    | [single] => single.toIRType
    | _ => IRType.unit
  return {
    name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := retType
    payable := spec.isPayable
    body := allStmts
  }

private def compileSpecialEntrypoint (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (spec : FunctionSpec) :
    Except String IREntrypoint := do
  let bodyChunks ← spec.body.mapM (compileStmt fields events errors)
  pure {
    payable := spec.isPayable
    body := bodyChunks.flatten
  }

private def pickUniqueFunctionByName (name : String) (funcs : List FunctionSpec) :
    Except String (Option FunctionSpec) :=
  match funcs.filter (·.name == name) with
  | [] => pure none
  | [single] => pure (some single)
  | _ => throw s!"Compilation error: multiple '{name}' entrypoints are not allowed ({issue586Ref})"

-- Check if contract uses mappings
def usesMapping (fields : List Field) : Bool :=
  fields.any fun f => isMapping fields f.name

private def constructorArgAliases (params : List Param) : List YulStmt :=
  let rec go (ps : List Param) (idx : Nat) (headOffset : Nat) : List YulStmt :=
    match ps with
    | [] => []
    | param :: rest =>
        let source := if isDynamicParamType param.ty then
          YulExpr.ident s!"{param.name}_offset"
        else
          match param.ty with
          | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
              YulExpr.ident param.name
          | _ =>
              YulExpr.call "mload" [YulExpr.lit headOffset]
        let alias := YulStmt.let_ s!"arg{idx}" source
        alias :: go rest (idx + 1) (headOffset + paramHeadSize param.ty)
  go params 0 0

-- Generate constructor argument loading code (from appended initcode args)
def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let argsOffset := YulExpr.call "add" [
      YulExpr.call "dataoffset" [YulExpr.str "runtime"],
      YulExpr.call "datasize" [YulExpr.str "runtime"]
    ]
    let initcodeArgCopy := [
      YulStmt.let_ "argsOffset" argsOffset,
      YulStmt.let_ "argsSize"
        (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.ident "argsOffset"]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.ident "argsSize"])
    ]
    let paramLoads := genParamLoadsFrom (fun pos => YulExpr.call "mload" [pos]) 0 0 params
    initcodeArgCopy ++ paramLoads ++ constructorArgAliases params

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
def compileConstructor (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← spec.body.mapM (compileStmt fields events errors .memory)
    return argLoads ++ bodyChunks.flatten

-- Main compilation function
-- SAFETY REQUIREMENTS (enforced by #guard in Specs.lean):
--   1. selectors.length == spec.functions.length (external functions only)
--   2. selectors[i] matches the Solidity signature of spec.functions[i]
-- WARNING: Order matters! If selector list is reordered but function list isn't,
--          functions will be mapped to wrong selectors with no runtime error.
def firstDuplicateSelector (selectors : List Nat) : Option Nat :=
  let rec go (seen : List Nat) : List Nat → Option Nat
    | [] => none
    | sel :: rest =>
      if seen.contains sel then
        some sel
      else
        go (sel :: seen) rest
  go [] selectors

def selectorNames (spec : ContractSpec) (selectors : List Nat) (sel : Nat) : List String :=
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  (externalFns.zip selectors).foldl (fun acc (fn, s) =>
    if s == sel then acc ++ [fn.name] else acc
  ) []

private def firstDuplicateName (names : List String) : Option String :=
  let rec go (seen : List String) : List String → Option String
    | [] => none
    | n :: rest =>
      if seen.contains n then
        some n
      else
        go (n :: seen) rest
  go [] names

private def validateErrorDef (err : ErrorDef) : Except String Unit := do
  for ty in err.params do
    if !supportedCustomErrorParamType ty then
      throw s!"Compilation error: custom error '{err.name}' uses unsupported dynamic parameter type {repr ty} ({issue586Ref}). Use uint256/address/bool/bytes32/bytes parameters."

def compile (spec : ContractSpec) (selectors : List Nat) : Except String IRContract := do
  let externalFns := spec.functions.filter (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)
  let internalFns := spec.functions.filter (·.isInternal)
  for fn in spec.functions do
    validateFunctionSpec fn
    validateInteropFunctionSpec fn
    validateSpecialEntrypointSpec fn
    validateEventArgShapesInFunction fn spec.events
    validateCustomErrorArgShapesInFunction fn spec.errors
    validateInternalCallShapesInFunction spec.functions fn
  validateConstructorSpec spec.constructor
  validateInteropConstructorSpec spec.constructor
  for ext in spec.externals do
    let _ ← externalFunctionReturns ext
    validateInteropExternalSpec ext
  match firstDuplicateName (spec.errors.map (·.name)) with
  | some dup =>
      throw s!"Compilation error: duplicate custom error declaration '{dup}'"
  | none =>
      pure ()
  for err in spec.errors do
    validateErrorDef err
  let fallbackSpec ← pickUniqueFunctionByName "fallback" spec.functions
  let receiveSpec ← pickUniqueFunctionByName "receive" spec.functions
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec spec.fields spec.events spec.errors sel fnSpec
  -- Compile internal functions as Yul function definitions (#181)
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction spec.fields spec.events spec.errors)
  let fallbackEntrypoint ← fallbackSpec.mapM (compileSpecialEntrypoint spec.fields spec.events spec.errors)
  let receiveEntrypoint ← receiveSpec.mapM (compileSpecialEntrypoint spec.fields spec.events spec.errors)
  return {
    name := spec.name
    deploy := (← compileConstructor spec.fields spec.events spec.errors spec.constructor)
    constructorPayable := spec.constructor.map (·.isPayable) |>.getD false
    functions := functions
    fallbackEntrypoint := fallbackEntrypoint
    receiveEntrypoint := receiveEntrypoint
    usesMapping := usesMapping spec.fields
    internalFunctions := internalFuncDefs
  }

end Compiler.ContractSpec
