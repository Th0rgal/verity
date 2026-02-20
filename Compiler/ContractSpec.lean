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
def compileExprList (fields : List Field) : List Expr → Except String (List YulExpr)
  | [] => pure []
  | e :: es => do
      let head ← compileExpr fields e
      let tail ← compileExprList fields es
      pure (head :: tail)

def compileExpr (fields : List Field) : Expr → Except String YulExpr
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
      compileMappingSlotRead fields field (← compileExpr fields key) "mapping"
  | Expr.mapping2 field key1 key2 =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let key1Expr ← compileExpr fields key1
        let key2Expr ← compileExpr fields key2
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [innerSlot, key2Expr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mappingUint field key => do
      compileMappingSlotRead fields field (← compileExpr fields key) "mappingUint"
  | Expr.caller => pure (YulExpr.call "caller" [])
  | Expr.msgValue => pure (YulExpr.call "callvalue" [])
  | Expr.blockTimestamp => pure (YulExpr.call "timestamp" [])
  | Expr.localVar name => pure (YulExpr.ident name)
  | Expr.externalCall name args => do
      let argExprs ← compileExprList fields args
      pure (YulExpr.call name argExprs)
  | Expr.internalCall functionName args => do
      let argExprs ← compileExprList fields args
      pure (YulExpr.call s!"internal_{functionName}" argExprs)
  | Expr.arrayLength name => pure (YulExpr.ident s!"{name}_length")
  | Expr.arrayElement name index => do
      let indexExpr ← compileExpr fields index
      pure (YulExpr.call "calldataload" [
        YulExpr.call "add" [
          YulExpr.ident s!"{name}_data_offset",
          YulExpr.call "mul" [indexExpr, YulExpr.lit 32]
        ]
      ])
  | Expr.add a b     => return yulBinOp "add" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.sub a b     => return yulBinOp "sub" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.mul a b     => return yulBinOp "mul" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.div a b     => return yulBinOp "div" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.mod a b     => return yulBinOp "mod" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.bitAnd a b  => return yulBinOp "and" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.bitOr a b   => return yulBinOp "or"  (← compileExpr fields a) (← compileExpr fields b)
  | Expr.bitXor a b  => return yulBinOp "xor" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.bitNot a    => return YulExpr.call "not" [← compileExpr fields a]
  | Expr.shl s v     => return yulBinOp "shl" (← compileExpr fields s) (← compileExpr fields v)
  | Expr.shr s v     => return yulBinOp "shr" (← compileExpr fields s) (← compileExpr fields v)
  | Expr.eq a b      => return yulBinOp "eq"  (← compileExpr fields a) (← compileExpr fields b)
  | Expr.gt a b      => return yulBinOp "gt"  (← compileExpr fields a) (← compileExpr fields b)
  | Expr.lt a b      => return yulBinOp "lt"  (← compileExpr fields a) (← compileExpr fields b)
  | Expr.ge a b      => return yulNegatedBinOp "lt" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.le a b      => return yulNegatedBinOp "gt" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.logicalAnd a b => return yulBinOp "and" (yulToBool (← compileExpr fields a)) (yulToBool (← compileExpr fields b))
  | Expr.logicalOr a b  => return yulBinOp "or"  (yulToBool (← compileExpr fields a)) (yulToBool (← compileExpr fields b))
  | Expr.logicalNot a   => return YulExpr.call "iszero" [← compileExpr fields a]
end

-- Compile require condition to a "failure" predicate to avoid double-negation.
def compileRequireFailCond (fields : List Field) : Expr → Except String YulExpr
  | Expr.ge a b => return yulBinOp "lt" (← compileExpr fields a) (← compileExpr fields b)
  | Expr.le a b => return yulBinOp "gt" (← compileExpr fields a) (← compileExpr fields b)
  | cond => return YulExpr.call "iszero" [← compileExpr fields cond]

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

private def validateFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  let _ ← functionReturns spec
  spec.body.forM (validateStmtParamReferences spec.name spec.params)

private def issue586Ref : String :=
  "Issue #586 (Solidity interop profile)"

private def isLowLevelCallName (name : String) : Bool :=
  ["call", "staticcall", "delegatecall", "callcode"].contains name

private def isInteropBuiltinCallName (name : String) : Bool :=
  (isLowLevelCallName name) ||
    ["create", "create2", "extcodesize", "extcodecopy", "extcodehash"].contains name

private def isUnsupportedInteropEntrypointName (name : String) : Bool :=
  ["fallback", "receive"].contains name

private def unsupportedEntrypointModelingError (name : String) : Except String Unit :=
  throw s!"Compilation error: function '{name}' uses unsupported Solidity interop entrypoint modeling ({issue586Ref}). Model this behavior with an explicit external function selector and guard logic until first-class fallback/receive support lands."

private def lowLevelCallUnsupportedError (context : String) (name : String) : Except String Unit :=
  throw s!"Compilation error: {context} uses unsupported low-level call '{name}' ({issue586Ref}). Use a verified linked external function wrapper instead of raw call/staticcall/delegatecall."

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
  | Stmt.returnValues values =>
      values.forM (validateInteropExpr context)
  | _ =>
      pure ()

private def validateInteropFunctionSpec (spec : FunctionSpec) : Except String Unit := do
  if isUnsupportedInteropEntrypointName spec.name then
    unsupportedEntrypointModelingError spec.name
  spec.body.forM (validateInteropStmt s!"function '{spec.name}'")

private def validateInteropExternalSpec (spec : ExternalFunction) : Except String Unit := do
  if isInteropBuiltinCallName spec.name then
    unsupportedInteropCallError s!"external declaration '{spec.name}'" spec.name

private def validateInteropConstructorSpec (ctor : Option ConstructorSpec) : Except String Unit := do
  match ctor with
  | none => pure ()
  | some spec =>
      spec.body.forM (validateInteropStmt "constructor")

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

-- Compile statement to Yul (using mutual recursion for lists).
-- When isInternal=true, Stmt.return compiles to `__ret := value` (for internal Yul functions)
-- instead of EVM RETURN which terminates the entire call.
mutual
def compileStmtList (fields : List Field) (events : List EventDef := [])
    (isInternal : Bool := false) :
    List Stmt → Except String (List YulStmt)
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields events isInternal s
      let tail ← compileStmtList fields events isInternal ss
      pure (head ++ tail)

def compileStmt (fields : List Field) (events : List EventDef := [])
    (isInternal : Bool := false) :
    Stmt → Except String (List YulStmt)
  | Stmt.letVar name value => do
      pure [YulStmt.let_ name (← compileExpr fields value)]
  | Stmt.assignVar name value => do
      pure [YulStmt.assign name (← compileExpr fields value)]
  | Stmt.setStorage field value =>
    if isMapping fields field then
      throw s!"Compilation error: field '{field}' is a mapping; use setMapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          pure [YulStmt.expr (YulExpr.call "sstore" [YulExpr.lit slot, ← compileExpr fields value])]
      | none => throw s!"Compilation error: unknown storage field '{field}' in setStorage"
  | Stmt.setMapping field key value => do
      compileMappingSlotWrite fields field (← compileExpr fields key) (← compileExpr fields value) "setMapping"
  | Stmt.setMapping2 field key1 key2 value =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
          let key1Expr ← compileExpr fields key1
          let key2Expr ← compileExpr fields key2
          let valueExpr ← compileExpr fields value
          let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
          pure [
            YulStmt.expr (YulExpr.call "sstore" [
              YulExpr.call "mappingSlot" [innerSlot, key2Expr],
              valueExpr
            ])
          ]
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMapping2"
  | Stmt.setMappingUint field key value => do
      compileMappingSlotWrite fields field (← compileExpr fields key) (← compileExpr fields value) "setMappingUint"
  | Stmt.require cond message =>
    do
      let failCond ← compileRequireFailCond fields cond
      pure [
        YulStmt.if_ failCond (revertWithMessage message)
      ]
  | Stmt.return value =>
    do
      let valueExpr ← compileExpr fields value
      if isInternal then
        pure [YulStmt.assign "__ret" valueExpr]
      else
        pure [
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, valueExpr]),
          YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])
        ]
  | Stmt.stop => return [YulStmt.expr (YulExpr.call "stop" [])]

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExpr fields cond
      let thenStmts ← compileStmtList fields events isInternal thenBranch
      let elseStmts ← compileStmtList fields events isInternal elseBranch
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
      let countExpr ← compileExpr fields count
      let bodyStmts ← compileStmtList fields events isInternal body
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
      let compiledArgs ← compileExprList fields args
      let zipped := eventDef.params.zip compiledArgs
      let indexed := zipped.filter (fun (p, _) => p.kind == EventParamKind.indexed)
      let unindexed := zipped.filter (fun (p, _) => p.kind == EventParamKind.unindexed)
      if indexed.length > 3 then
        throw s!"Compilation error: event '{eventName}' has {indexed.length} indexed params; max is 3"
      for (p, _) in indexed do
        match p.ty with
        | ParamType.array _ | ParamType.fixedArray _ _ | ParamType.bytes | ParamType.tuple _ =>
            throw s!"Compilation error: indexed dynamic/tuple param '{p.name}' in event '{eventName}' is not supported yet"
        | _ => pure ()
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
      let unindexedStores ← unindexed.zipIdx.mapM fun ((p, argExpr), idx) => do
        let storedExpr :=
          match p.ty with
          | ParamType.address => YulExpr.call "and" [argExpr, YulExpr.hex ((2^160) - 1)]
          | ParamType.bool => yulToBool argExpr
          | _ => argExpr
        pure (YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.call "add" [YulExpr.ident "__evt_ptr", YulExpr.lit (idx * 32)],
          storedExpr
        ]))
      let dataSize := unindexed.length * 32
      let topicExprs :=
        [YulExpr.ident "__evt_topic0"] ++ indexed.map (fun (p, argExpr) =>
          match p.ty with
          | ParamType.address => YulExpr.call "and" [argExpr, YulExpr.hex ((2^160) - 1)]
          | ParamType.bool => yulToBool argExpr
          | _ => argExpr
        )
      let logFn := match indexed.length with
        | 0 => "log1"
        | 1 => "log2"
        | 2 => "log3"
        | _ => "log4"
      let logArgs := [YulExpr.ident "__evt_ptr", YulExpr.lit dataSize] ++ topicExprs
      let logStmt := YulStmt.expr (YulExpr.call logFn logArgs)
      pure [YulStmt.block ([storePtr] ++ sigStores ++ [topic0Store] ++ unindexedStores ++ [logStmt])]

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields args
      pure [YulStmt.expr (YulExpr.call s!"internal_{functionName}" argExprs)]
  | Stmt.returnValues values => do
      if values.isEmpty then
        pure [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 0])]
      else
        let compiled ← compileExprList fields values
        let stores := (compiled.zipIdx.map fun (valueExpr, idx) =>
          YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit (idx * 32), valueExpr]))
        pure (stores ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit (values.length * 32)])])
  | Stmt.returnArray name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let byteLen := YulExpr.call "mul" [lenIdent, YulExpr.lit 32]
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.expr (YulExpr.call "calldatacopy" [YulExpr.lit 64, dataOffset, byteLen]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, byteLen]])
      ]
  | Stmt.returnBytes name => do
      let lenIdent := YulExpr.ident s!"{name}_length"
      let dataOffset := YulExpr.ident s!"{name}_data_offset"
      let tailOffset := YulExpr.call "add" [YulExpr.lit 64, lenIdent]
      let paddedLen :=
        YulExpr.call "and" [
          YulExpr.call "add" [lenIdent, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]
      pure [
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 0, YulExpr.lit 32]),
        YulStmt.expr (YulExpr.call "mstore" [YulExpr.lit 32, lenIdent]),
        YulStmt.expr (YulExpr.call "calldatacopy" [YulExpr.lit 64, dataOffset, lenIdent]),
        YulStmt.expr (YulExpr.call "mstore" [tailOffset, YulExpr.lit 0]),
        YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.call "add" [YulExpr.lit 64, paddedLen]])
      ]
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
            YulStmt.let_ "__slot" (YulExpr.call "calldataload" [
              YulExpr.call "add" [dataOffset, YulExpr.call "mul" [YulExpr.ident "__i", YulExpr.lit 32]]
            ]),
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

-- Generate calldata loads for a dynamic parameter (array or bytes).
private def genDynamicParamLoads (name : String) (headOffset : Nat) : List YulStmt :=
  let offsetLoad := YulStmt.let_ s!"{name}_offset"
    (YulExpr.call "calldataload" [YulExpr.lit headOffset])
  let lengthLoad := YulStmt.let_ s!"{name}_length"
    (YulExpr.call "calldataload" [
      YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{name}_offset"]
    ])
  let dataOffsetLoad := YulStmt.let_ s!"{name}_data_offset"
    (YulExpr.call "add" [
      YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{name}_offset"],
      YulExpr.lit 32
    ])
  [offsetLoad, lengthLoad, dataOffsetLoad]

private def genScalarLoad (name : String) (ty : ParamType) (offset : Nat) : List YulStmt :=
  match ty with
  | ParamType.uint256 =>
      [YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit offset])]
  | ParamType.bytes32 =>
      [YulStmt.let_ name (YulExpr.call "calldataload" [YulExpr.lit offset])]
  | ParamType.address =>
      [YulStmt.let_ name (YulExpr.call "and" [
        YulExpr.call "calldataload" [YulExpr.lit offset],
        YulExpr.hex ((2^160) - 1)
      ])]
  | ParamType.bool =>
      [YulStmt.let_ name (YulExpr.call "iszero" [YulExpr.call "iszero" [
        YulExpr.call "calldataload" [YulExpr.lit offset]
      ]])]
  | _ => []

private partial def genStaticTypeLoads (name : String) (ty : ParamType) (offset : Nat) :
    List YulStmt :=
  match ty with
  | ParamType.uint256 | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      genScalarLoad name ty offset
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap fun i =>
        genStaticTypeLoads s!"{name}_{i}" elemTy (offset + i * paramHeadSize elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) (curOffset : Nat) : List YulStmt :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            let elemName := s!"{name}_{idx}"
            let here := genStaticTypeLoads elemName elemTy curOffset
            here ++ go rest (idx + 1) (curOffset + paramHeadSize elemTy)
      go elemTys 0 offset
  | _ => []

-- Generate parameter loading code (from calldata)
def genParamLoads (params : List Param) : List YulStmt :=
  let rec go (paramList : List Param) (headOffset : Nat) : List YulStmt :=
    match paramList with
    | [] => []
    | param :: rest =>
      let stmts := match param.ty with
        | ParamType.uint256 =>
          [YulStmt.let_ param.name (YulExpr.call "calldataload" [YulExpr.lit headOffset])]
        | ParamType.address =>
          [YulStmt.let_ param.name (YulExpr.call "and" [
            YulExpr.call "calldataload" [YulExpr.lit headOffset],
            YulExpr.hex ((2^160) - 1)
          ])]
        | ParamType.bool =>
          [YulStmt.let_ param.name (YulExpr.call "iszero" [YulExpr.call "iszero" [
            YulExpr.call "calldataload" [YulExpr.lit headOffset]
          ]])]
        | ParamType.bytes32 =>
          [YulStmt.let_ param.name (YulExpr.call "calldataload" [YulExpr.lit headOffset])]
        | ParamType.tuple elemTypes =>
          if isDynamicParamType param.ty then
            genDynamicParamLoads param.name headOffset
          else
            genStaticTypeLoads param.name (ParamType.tuple elemTypes) headOffset
        | ParamType.array _ =>
          genDynamicParamLoads param.name headOffset
        | ParamType.fixedArray _ n =>
          -- Static fixed arrays are decoded inline recursively (including nested tuple members).
          -- For scalar element arrays we preserve `<name>` as an alias to `<name>_0`.
          if isDynamicParamType param.ty then
            genDynamicParamLoads param.name headOffset
          else
            let staticLoads := genStaticTypeLoads param.name param.ty headOffset
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
          genDynamicParamLoads param.name headOffset
      stmts ++ go rest (headOffset + paramHeadSize param.ty)
  go params 4  -- Start after 4-byte selector

-- Compile internal function to a Yul function definition (#181)
def compileInternalFunction (fields : List Field) (events : List EventDef) (spec : FunctionSpec) :
    Except String YulStmt := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  if returns.length > 1 then
    throw s!"Compilation error: internal function '{spec.name}' cannot return multiple values yet"
  let paramNames := spec.params.map (·.name)
  let retNames := match returns with
    | [_] => ["__ret"]
    | [] => []
    | _ => []
  let bodyStmts ← compileStmtList fields events (isInternal := true) spec.body
  pure (YulStmt.funcDef s!"internal_{spec.name}" paramNames retNames bodyStmts)

-- Compile function spec to IR function
def compileFunctionSpec (fields : List Field) (events : List EventDef) (selector : Nat) (spec : FunctionSpec) :
    Except String IRFunction := do
  validateFunctionSpec spec
  let returns ← functionReturns spec
  let paramLoads := genParamLoads spec.params
  let bodyChunks ← spec.body.mapM (compileStmt fields events)
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

-- Check if contract uses mappings
def usesMapping (fields : List Field) : Bool :=
  fields.any fun f => isMapping fields f.name

-- Generate constructor argument loading code (from end of bytecode)
def genConstructorArgLoads (params : List Param) : List YulStmt :=
  if params.isEmpty then []
  else
    let totalBytes := params.length * 32
    let argsOffset := [
      YulStmt.let_ "argsOffset" (YulExpr.call "sub" [YulExpr.call "codesize" [], YulExpr.lit totalBytes]),
      YulStmt.expr (YulExpr.call "codecopy" [YulExpr.lit 0, YulExpr.ident "argsOffset", YulExpr.lit totalBytes])
    ]
    let loadArgs := params.zipIdx.flatMap fun (param, idx) =>
      let offset := idx * 32
      match param.ty with
      | ParamType.address =>
        [YulStmt.let_ s!"arg{idx}" (YulExpr.call "and" [
          YulExpr.call "mload" [YulExpr.lit offset],
          YulExpr.hex ((2^160) - 1)
        ])]
      | _ =>
        -- uint256, bytes32, and other types loaded as raw 256-bit values
        [YulStmt.let_ s!"arg{idx}" (YulExpr.call "mload" [YulExpr.lit offset])]
    argsOffset ++ loadArgs

-- Compile deploy code (constructor)
-- Note: Don't append datacopy/return here - Codegen.deployCode does that
def compileConstructor (fields : List Field) (ctor : Option ConstructorSpec) :
    Except String (List YulStmt) := do
  match ctor with
  | none => return []
  | some spec =>
    let argLoads := genConstructorArgLoads spec.params
    let bodyChunks ← spec.body.mapM (compileStmt fields)
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
  let externalFns := spec.functions.filter (!·.isInternal)
  (externalFns.zip selectors).foldl (fun acc (fn, s) =>
    if s == sel then acc ++ [fn.name] else acc
  ) []

def compile (spec : ContractSpec) (selectors : List Nat) : Except String IRContract := do
  let externalFns := spec.functions.filter (!·.isInternal)
  let internalFns := spec.functions.filter (·.isInternal)
  for fn in spec.functions do
    validateFunctionSpec fn
    validateInteropFunctionSpec fn
  validateInteropConstructorSpec spec.constructor
  for ext in spec.externals do
    let _ ← externalFunctionReturns ext
    validateInteropExternalSpec ext
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec spec.fields spec.events sel fnSpec
  -- Compile internal functions as Yul function definitions (#181)
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction spec.fields spec.events)
  return {
    name := spec.name
    deploy := (← compileConstructor spec.fields spec.constructor)
    constructorPayable := spec.constructor.map (·.isPayable) |>.getD false
    functions := functions
    usesMapping := usesMapping spec.fields
    internalFunctions := internalFuncDefs
  }

end Compiler.ContractSpec
