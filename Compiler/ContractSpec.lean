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
  | mapping   -- Address → Uint256 (legacy, equivalent to mappingTyped (.simple .address))
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
  | bytes32                                -- Fixed 32-byte value
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
  | mapping => IRType.uint256  -- Mappings return uint256
  | mappingTyped _ => IRType.uint256  -- All mappings return uint256

def ParamType.toIRType : ParamType → IRType
  | uint256 => IRType.uint256
  | address => IRType.address
  | bytes32 => IRType.uint256  -- bytes32 is a 256-bit value
  | array _ => IRType.uint256  -- Arrays are represented as calldata offsets
  | fixedArray _ _ => IRType.uint256
  | bytes => IRType.uint256

-- Check if a param type is dynamic (requires offset-based ABI decoding)
def ParamType.isDynamic : ParamType → Bool
  | array _ => true
  | bytes => true
  | _ => false

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
  returnType : Option ParamType  -- None for void functions
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
  body : List Stmt
  /-- Whether this is an internal-only function (not exposed via selector dispatch) -/
  isInternal : Bool := false
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
  events : List EventDef := []  -- Event definitions (#153)
  externals : List ExternalFunction := []  -- External function declarations (#184)
  deriving Repr

/-!
## IR Generation from Spec

Automatically compile a ContractSpec to IRContract.
-/

-- Helper: Find field slot number
private def findFieldSlot (fields : List Field) (name : String) : Option Nat :=
  fields.findIdx? (·.name == name)

-- Helper: Is field a mapping? (legacy or typed)
private def isMapping (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    f.ty == FieldType.mapping || match f.ty with
    | FieldType.mappingTyped _ => true
    | _ => false

-- Helper: Is field a double mapping?
private def isMapping2 (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.mappingTyped (MappingType.nested _ _) => true
    | _ => false

-- Keep compiler literals aligned with Uint256 semantics (mod 2^256).
private def uint256Modulus : Nat := 2 ^ 256

-- Compile expression to Yul (using mutual recursion for lists)
mutual
private def compileExprList (fields : List Field) : List Expr → Except String (List YulExpr)
  | [] => pure []
  | e :: es => do
      let head ← compileExpr fields e
      let tail ← compileExprList fields es
      pure (head :: tail)

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
  | Expr.mapping2 field key1 key2 =>
    if !isMapping2 fields field then
      throw s!"Compilation error: field '{field}' is not a double mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let key1Expr ← compileExpr fields key1
        let key2Expr ← compileExpr fields key2
        -- Nested mapping: keccak256(key2 . keccak256(key1 . slot))
        let innerSlot := YulExpr.call "mappingSlot" [YulExpr.lit slot, key1Expr]
        pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [innerSlot, key2Expr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
  | Expr.mappingUint field key =>
    if !isMapping fields field then
      throw s!"Compilation error: field '{field}' is not a mapping"
    else
      match findFieldSlot fields field with
      | some slot => do
        let keyExpr ← compileExpr fields key
        -- Uint256-keyed mapping uses the same slot computation as address-keyed
        pure (YulExpr.call "sload" [YulExpr.call "mappingSlot" [YulExpr.lit slot, keyExpr]])
      | none => throw s!"Compilation error: unknown mapping field '{field}'"
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
  | Expr.arrayLength name =>
      -- Array length: calldataload(calldataload(4 + paramOffset) + 4)
      -- This is loaded into a local variable during param loading
      pure (YulExpr.ident s!"{name}_length")
  | Expr.arrayElement name index => do
      let indexExpr ← compileExpr fields index
      -- Array element: calldataload(arrayDataOffset + index * 32)
      -- arrayDataOffset is loaded during param loading
      pure (YulExpr.call "calldataload" [
        YulExpr.call "add" [
          YulExpr.ident s!"{name}_data_offset",
          YulExpr.call "mul" [indexExpr, YulExpr.lit 32]
        ]
      ])
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
  | Expr.ge a b => do
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
  | Expr.le a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "iszero" [YulExpr.call "gt" [aExpr, bExpr]])
  | Expr.logicalAnd a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "and" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [aExpr]],
        YulExpr.call "iszero" [YulExpr.call "iszero" [bExpr]]
      ])
  | Expr.logicalOr a b => do
      let aExpr ← compileExpr fields a
      let bExpr ← compileExpr fields b
      pure (YulExpr.call "or" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [aExpr]],
        YulExpr.call "iszero" [YulExpr.call "iszero" [bExpr]]
      ])
  | Expr.logicalNot a => do
      let aExpr ← compileExpr fields a
      pure (YulExpr.call "iszero" [aExpr])
end

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

/-!
### Event Topic Computation (#153)

Compute the event signature hash (topic 0) from the event name and parameter types.
This mirrors how Solidity computes event signatures: keccak256("EventName(type1,type2,...)").
At compile time we use a placeholder; CI validates the selector matches solc output.
-/

-- Map ParamType to its Solidity type string for event signature
private def paramTypeToSolidityString : ParamType → String
  | ParamType.uint256 => "uint256"
  | ParamType.address => "address"
  | ParamType.bytes32 => "bytes32"
  | ParamType.array t => paramTypeToSolidityString t ++ "[]"
  | ParamType.fixedArray t n => paramTypeToSolidityString t ++ "[" ++ toString n ++ "]"
  | ParamType.bytes => "bytes"

-- Build the Solidity-style event signature string
def eventSignature (event : EventDef) : String :=
  let paramTypes := event.params.map fun p => paramTypeToSolidityString p.ty
  event.name ++ "(" ++ String.intercalate "," paramTypes ++ ")"

-- Compile statement to Yul (using mutual recursion for lists)
mutual
private def compileStmtList (fields : List Field) : List Stmt → Except String (List YulStmt)
  | [] => pure []
  | s :: ss => do
      let head ← compileStmt fields s
      let tail ← compileStmtList fields ss
      pure (head ++ tail)

private def compileStmt (fields : List Field) : Stmt → Except String (List YulStmt)
  | Stmt.letVar name value =>
    do
      let valueExpr ← compileExpr fields value
      pure [YulStmt.let_ name valueExpr]
  | Stmt.assignVar name value =>
    do
      let valueExpr ← compileExpr fields value
      pure [YulStmt.assign name valueExpr]
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
  | Stmt.setMappingUint field key value =>
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
      | none => throw s!"Compilation error: unknown mapping field '{field}' in setMappingUint"
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

  | Stmt.ite cond thenBranch elseBranch => do
      -- If/else: compile to Yul if + negated if (#179)
      let condExpr ← compileExpr fields cond
      let thenStmts ← compileStmtList fields thenBranch
      let elseStmts ← compileStmtList fields elseBranch
      if elseBranch.isEmpty then
        -- Simple if (no else)
        pure [YulStmt.if_ condExpr thenStmts]
      else
        -- If/else: use Yul switch on iszero
        pure [
          YulStmt.if_ condExpr thenStmts,
          YulStmt.if_ (YulExpr.call "iszero" [condExpr]) elseStmts
        ]

  | Stmt.forEach varName count body => do
      -- Bounded loop: for { let i := 0 } lt(i, count) { i := add(i, 1) } { body } (#179)
      let countExpr ← compileExpr fields count
      let bodyStmts ← compileStmtList fields body
      let initStmts := [YulStmt.let_ varName (YulExpr.lit 0)]
      let condExpr := YulExpr.call "lt" [YulExpr.ident varName, countExpr]
      let postStmts := [YulStmt.assign varName (YulExpr.call "add" [YulExpr.ident varName, YulExpr.lit 1])]
      pure [YulStmt.for_ initStmts condExpr postStmts bodyStmts]

  | Stmt.emit eventName args => do
      -- Emit event using LOG opcode (#153)
      -- For now, emit with keccak256(signature) as topic0 and args as data
      -- Topic0 = keccak256(eventSignature) is computed at link time
      let argExprs ← args.enum.mapM fun (idx, arg) => do
        let argExpr ← compileExpr fields arg
        pure (YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit (idx * 32),
          argExpr
        ]))
      let dataSize := args.length * 32
      -- Use log1 with topic0 = keccak256(event signature) placeholder
      -- The actual topic hash will be resolved by the linker or hardcoded
      let logStmt := YulStmt.expr (YulExpr.call "log1" [
        YulExpr.lit 0,        -- memory offset
        YulExpr.lit dataSize,  -- data size
        YulExpr.call s!"__event_{eventName}" []  -- topic0 placeholder
      ])
      pure (argExprs ++ [logStmt])

  | Stmt.internalCall functionName args => do
      -- Internal function call as statement (#181)
      let argExprs ← compileExprList fields args
      pure [YulStmt.expr (YulExpr.call s!"internal_{functionName}" argExprs)]
end

-- Generate parameter loading code (from calldata)
private def genParamLoads (params : List Param) : List YulStmt :=
  -- First pass: compute which params are dynamic and calculate head offsets
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
        | ParamType.bytes32 =>
          [YulStmt.let_ param.name (YulExpr.call "calldataload" [YulExpr.lit headOffset])]
        | ParamType.array _ =>
          -- Dynamic array: head contains offset to array data
          -- offset is relative to start of params (byte 4)
          let offsetLoad := YulStmt.let_ s!"{param.name}_offset"
            (YulExpr.call "calldataload" [YulExpr.lit headOffset])
          -- Length at offset + 4
          let lengthLoad := YulStmt.let_ s!"{param.name}_length"
            (YulExpr.call "calldataload" [
              YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{param.name}_offset"]
            ])
          -- Data starts at offset + 4 + 32
          let dataOffsetLoad := YulStmt.let_ s!"{param.name}_data_offset"
            (YulExpr.call "add" [
              YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{param.name}_offset"],
              YulExpr.lit 32
            ])
          [offsetLoad, lengthLoad, dataOffsetLoad]
        | ParamType.fixedArray _ _ =>
          -- Fixed arrays are inline in calldata (no offset indirection)
          [YulStmt.let_ param.name (YulExpr.call "calldataload" [YulExpr.lit headOffset])]
        | ParamType.bytes =>
          -- Dynamic bytes: same encoding as dynamic array
          let offsetLoad := YulStmt.let_ s!"{param.name}_offset"
            (YulExpr.call "calldataload" [YulExpr.lit headOffset])
          let lengthLoad := YulStmt.let_ s!"{param.name}_length"
            (YulExpr.call "calldataload" [
              YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{param.name}_offset"]
            ])
          let dataOffsetLoad := YulStmt.let_ s!"{param.name}_data_offset"
            (YulExpr.call "add" [
              YulExpr.call "add" [YulExpr.lit 4, YulExpr.ident s!"{param.name}_offset"],
              YulExpr.lit 32
            ])
          [offsetLoad, lengthLoad, dataOffsetLoad]
      stmts ++ go rest (headOffset + 32)
  go params 4  -- Start after 4-byte selector

-- Compile internal function to a Yul function definition (#181)
private def compileInternalFunction (fields : List Field) (spec : FunctionSpec) :
    Except String YulStmt := do
  let paramNames := spec.params.map (·.name)
  let retNames := match spec.returnType with
    | some _ => ["__ret"]
    | none => []
  let bodyChunks ← spec.body.mapM (compileStmt fields)
  pure (YulStmt.funcDef s!"internal_{spec.name}" paramNames retNames bodyChunks.flatten)

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
  fields.any fun f => f.ty == FieldType.mapping || match f.ty with
    | FieldType.mappingTyped _ => true
    | _ => false

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
      | _ =>
        -- bytes32 and other types loaded as raw 256-bit values
        [YulStmt.let_ s!"arg{idx}" (YulExpr.call "mload" [YulExpr.lit offset])]
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
--   1. selectors.length == spec.functions.length (external functions only)
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
  let externalFns := spec.functions.filter (!·.isInternal)
  (externalFns.zip selectors).foldl (fun acc (fn, s) =>
    if s == sel then acc ++ [fn.name] else acc
  ) []

def compile (spec : ContractSpec) (selectors : List Nat) : Except String IRContract := do
  let externalFns := spec.functions.filter (!·.isInternal)
  let internalFns := spec.functions.filter (·.isInternal)
  if externalFns.length != selectors.length then
    throw s!"Selector count mismatch for {spec.name}: {selectors.length} selectors for {externalFns.length} external functions"
  match firstDuplicateSelector selectors with
  | some dup =>
      let names := selectorNames spec selectors dup
      let nameStr := if names.isEmpty then "<unknown>" else String.intercalate ", " names
      throw s!"Selector collision in {spec.name}: {dup} assigned to {nameStr}"
  | none => pure ()
  let functions ← (externalFns.zip selectors).mapM fun (fnSpec, sel) =>
    compileFunctionSpec spec.fields sel fnSpec
  -- Compile internal functions as Yul function definitions (#181)
  let internalFuncDefs ← internalFns.mapM (compileInternalFunction spec.fields)
  return {
    name := spec.name
    deploy := (← compileConstructor spec.fields spec.constructor)
    functions := functions
    usesMapping := usesMapping spec.fields
    internalFunctions := internalFuncDefs
  }

end Compiler.ContractSpec
