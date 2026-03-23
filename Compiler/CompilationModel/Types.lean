/-
  Compiler.CompilationModel: Declarative Compilation Model DSL

  This module defines a declarative way to model contracts for compilation,
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

import Compiler.Constants
import Compiler.ECM
import Compiler.IR
import Compiler.ProofStatus
import Compiler.Yul.Ast
import Compiler.Identifier

namespace Compiler.CompilationModel

export Compiler.Constants (errorStringSelectorWord addressMask selectorShift freeMemoryPointer)

open Compiler
open Compiler.Yul

/-!
## Compilation Model DSL

Instead of manually writing IR, contracts provide a high-level model:
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
  | chain (keyTypes : List MappingKeyType)                     -- mapping(K1 => ... => mapping(Kn => uint256))
  deriving Repr, BEq

structure PackedBits where
  /-- Least-significant bit offset within the 256-bit storage word. -/
  offset : Nat
  /-- Bit width of this packed subfield. -/
  width : Nat
  deriving Repr, BEq

/-- A named member within a struct-valued mapping.
    Each member occupies a specific word within the struct's storage region,
    and may optionally be packed into a subregion of that word. -/
structure StructMember where
  /-- The member name (used in `Expr.structMember` / `Stmt.setStructMember`). -/
  name : String
  /-- Zero-based word offset from the struct's base slot. -/
  wordOffset : Nat
  /-- Optional packed subfield within the word. When `none`, the member occupies
      the full 256-bit word. -/
  packed : Option PackedBits := none
  deriving Repr, BEq

inductive StorageArrayElemType
  | uint256
  | address
  | bool
  | uint8
  | bytes32
  deriving Repr, BEq

def storageArrayElemUsesOneStorageWord : StorageArrayElemType → Bool
  | .uint256 | .address | .bytes32 => true
  | .bool | .uint8 => false

inductive FieldType
  | uint256
  | address
  | dynamicArray (elemType : StorageArrayElemType)
  | mappingTyped (mt : MappingType)  -- Flexible mapping types (#154)
  /-- A mapping whose value is a multi-word struct with named members.
      `mappingStruct keyType members` defines `mapping(K => Struct)` where
      `Struct` spans `members.map (·.wordOffset) |>.maximum + 1` words.
      Access members via `Expr.structMember` / `Stmt.setStructMember`. -/
  | mappingStruct (keyType : MappingKeyType) (members : List StructMember)
  /-- A nested mapping whose inner value is a multi-word struct with named members.
      `mappingStruct2 outerKey innerKey members` defines
      `mapping(K1 => mapping(K2 => Struct))`.
      Access members via `Expr.structMember2` / `Stmt.setStructMember2`. -/
  | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMember)
  deriving Repr, BEq

structure Field where
  name : String
  ty : FieldType
  /-- Optional explicit storage slot override.
      When omitted, the slot defaults to declaration order (legacy behavior). -/
  slot : Option Nat := none
  /-- Optional packed subfield placement within the storage word.
      When present, reads/writes are masked and shifted to this bit range. -/
  packedBits : Option PackedBits := none
  /-- Optional compatibility mirror-write slots.
      Writes to this field also write the same value to each alias slot. -/
  aliasSlots : List Nat := []
  deriving Repr

structure ReservedSlotRange where
  /-- Inclusive start slot of a reserved storage interval. -/
  start : Nat
  /-- Inclusive end slot of a reserved storage interval. -/
  end_ : Nat
  deriving Repr, BEq

structure SlotAliasRange where
  /-- Inclusive start slot for canonical source slots. -/
  sourceStart : Nat
  /-- Inclusive end slot for canonical source slots. -/
  sourceEnd : Nat
  /-- Alias slot corresponding to sourceStart (sourceStart + i maps to targetStart + i). -/
  targetStart : Nat
  deriving Repr, BEq

/-!
### Parameter Types (#180)

Extended parameter types supporting arrays, bytes, and bytes32.
-/

inductive ParamType
  | uint256
  | int256
  | uint8
  | address
  | bool                                   -- Solidity bool (ABI-encoded as 32-byte 0/1)
  | bytes32                                -- Fixed 32-byte value
  | string                                 -- Dynamic UTF-8 string (ABI-compatible with bytes)
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
def ParamType.toIRType : ParamType → IRType
  | uint256 => IRType.uint256
  | int256 => IRType.uint256
  | uint8 => IRType.uint256
  | address => IRType.address
  | bool => IRType.uint256
  | bytes32 => IRType.uint256  -- bytes32 is a 256-bit value
  | string => IRType.uint256
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
  /-- Proof-accounting status for this foreign surface.
      `proved` means there is an end-to-end refinement theorem,
      `assumed` means downstream proofs must quantify over the spec explicitly,
      and `unchecked` means the function is available for compilation/testing only. -/
  proofStatus : Compiler.ProofStatus := .assumed
  /-- Names of axioms assumed about this function.
      The actual Lean propositions are stated separately;
      these names are for documentation and audit purposes. -/
  axiomNames : List String
  deriving Repr

structure LocalObligation where
  name : String
  /-- User-supplied summary of the local refinement contract that must hold
      for this localized unsafe/assembly boundary. -/
  obligation : String
  /-- Proof-accounting status for this local boundary. -/
  proofStatus : Compiler.ProofStatus := .assumed
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
  | storageAddr (field : String)
  | mapping (field : String) (key : Expr)
  | mappingWord (field : String) (key : Expr) (wordOffset : Nat)  -- mappingSlot(base,key) + wordOffset
  | mappingPackedWord (field : String) (key : Expr) (wordOffset : Nat) (packed : PackedBits)
  | mapping2 (field : String) (key1 key2 : Expr)  -- Double mapping (#154)
  | mapping2Word (field : String) (key1 key2 : Expr) (wordOffset : Nat)  -- Double mapping + word offset
  | mappingUint (field : String) (key : Expr)  -- Uint256-keyed mapping (#154)
  | mappingChain (field : String) (keys : List Expr)  -- Arbitrary-depth mapping read (#1570)
  /-- Read a named member of a struct-valued mapping.
      Resolves the member's word offset and optional packed bits at compile time.
      `structMember field key memberName` compiles to the same Yul as
      `mappingPackedWord field key member.wordOffset member.packed` (or
      `mappingWord` when unpacked). -/
  | structMember (field : String) (key : Expr) (memberName : String)
  /-- Read a named member of a struct-valued double mapping.
      `structMember2 field key1 key2 memberName` resolves the member's word offset
      and packed bits from the field's struct definition. -/
  | structMember2 (field : String) (key1 key2 : Expr) (memberName : String)
  | caller
  | contractAddress
  | chainid
  | msgValue
  | blockTimestamp
  | blockNumber
  | blobbasefee
  | mload (offset : Expr)
  | tload (offset : Expr)
  | keccak256 (offset size : Expr)
  /-- First-class low-level `call(gas, target, value, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | call (gas target value inOffset inSize outOffset outSize : Expr)
  /-- First-class low-level `staticcall(gas, target, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | staticcall (gas target inOffset inSize outOffset outSize : Expr)
  /-- First-class low-level `delegatecall(gas, target, inOffset, inSize, outOffset, outSize)`.
      Returns the EVM success bit (0/1). -/
  | delegatecall (gas target inOffset inSize outOffset outSize : Expr)
  /-- Size in bytes of the current call's calldata (`calldatasize()`). -/
  | calldatasize
  /-- Load a 32-byte word from calldata at the given byte offset (`calldataload(offset)`). -/
  | calldataload (offset : Expr)
  /-- Size in bytes of returndata from the most recent external call frame. -/
  | returndataSize
  /-- Size in bytes of code deployed at the given address (0 for EOAs). -/
  | extcodesize (addr : Expr)
  /-- ERC20-style optional bool return helper:
      true iff `returndatasize() == 0 || (returndatasize() == 32 && mload(outOffset) == 1)`. -/
  | returndataOptionalBoolAt (outOffset : Expr)
  | localVar (name : String)  -- Reference to local variable
  | externalCall (name : String) (args : List Expr)  -- External function call (linked at compile time)
  | internalCall (functionName : String) (args : List Expr)  -- Internal function call (#181)
  | arrayLength (name : String)  -- Length of a dynamic array parameter (#180)
  | arrayElement (name : String) (index : Expr)  -- Checked element access of a dynamic array parameter (revert on out-of-range) (#180)
  | storageArrayLength (field : String)  -- Read the length word of a storage dynamic array (#1571)
  | storageArrayElement (field : String) (index : Expr)  -- Checked element access of a storage dynamic array (#1571)
  /-- Equality on direct `bytes` / `string` parameters loaded from calldata or memory.
      The names refer to the dynamic parameter base names (`foo`, not `foo_offset`). -/
  | dynamicBytesEq (lhsName rhsName : String)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | div (a b : Expr)
  | sdiv (a b : Expr)
  | mod (a b : Expr)
  | smod (a b : Expr)
  | bitAnd (a b : Expr)
  | bitOr (a b : Expr)
  | bitXor (a b : Expr)
  | bitNot (a : Expr)
  | shl (shift value : Expr)
  | shr (shift value : Expr)
  | sar (shift value : Expr)
  | signextend (byteIndex value : Expr)
  | eq (a b : Expr)
  | ge (a b : Expr)
  | gt (a b : Expr)  -- Greater than (strict)
  | sgt (a b : Expr)
  | lt (a b : Expr)
  | slt (a b : Expr)
  | le (a b : Expr)  -- Less than or equal
  | logicalAnd (a b : Expr)  -- Logical AND (both operands always evaluated)
  | logicalOr (a b : Expr)   -- Logical OR  (both operands always evaluated)
  | logicalNot (a : Expr)    -- Logical NOT
  /-- `mulDivDown(a, b, c)` = `a * b / c` (round toward zero).
      Compiles to `div(mul(a, b), c)`. (#928) -/
  | mulDivDown (a b c : Expr)
  /-- `mulDivUp(a, b, c)` = `(a * b + c - 1) / c` (round away from zero).
      Compiles to `div(add(mul(a, b), sub(c, 1)), c)`. (#928) -/
  | mulDivUp (a b c : Expr)
  /-- `wMulDown(a, b)` = `a * b / WAD` (WAD = 1e18, round down).
      Sugar for `mulDivDown a b (literal WAD)`. (#928) -/
  | wMulDown (a b : Expr)
  /-- `wDivUp(a, b)` = `(a * WAD + b - 1) / b` (WAD = 1e18, round up).
      Compiles to `div(add(mul(a, WAD), sub(b, 1)), b)`. (#928) -/
  | wDivUp (a b : Expr)
  /-- `min(a, b)` — unsigned minimum.
      Compiles to `sub(a, mul(sub(a, b), gt(a, b)))`. (#928) -/
  | min (a b : Expr)
  /-- `max(a, b)` — unsigned maximum.
      Compiles to `add(a, mul(sub(b, a), gt(b, a)))`. (#928) -/
  | max (a b : Expr)
  /-- Expression-level conditional: `ite cond thenVal elseVal`.
      Compiles to branchless `add(mul(iszero(iszero(cond)), thenVal), mul(iszero(cond), elseVal))`.
      Both branches are eagerly evaluated; `cond` is evaluated twice.
      For complex conditions with side effects, bind to a local variable first. -/
  | ite (cond thenVal elseVal : Expr)
  deriving Repr

inductive Stmt
  | letVar (name : String) (value : Expr)  -- Declare local variable
  | assignVar (name : String) (value : Expr)  -- Reassign existing variable
  | setStorage (field : String) (value : Expr)
  | setStorageAddr (field : String) (value : Expr)
  | storageArrayPush (field : String) (value : Expr)  -- Append to a storage dynamic array (#1571)
  | storageArrayPop (field : String)  -- Pop from a storage dynamic array (#1571)
  | setStorageArrayElement (field : String) (index : Expr) (value : Expr)  -- Indexed write (#1571)
  | setMapping (field : String) (key : Expr) (value : Expr)
  | setMappingWord (field : String) (key : Expr) (wordOffset : Nat) (value : Expr)  -- mappingSlot(base,key)+wordOffset write
  | setMappingPackedWord (field : String) (key : Expr) (wordOffset : Nat) (packed : PackedBits) (value : Expr)
  | setMapping2 (field : String) (key1 key2 : Expr) (value : Expr)  -- Double mapping write (#154)
  | setMapping2Word (field : String) (key1 key2 : Expr) (wordOffset : Nat) (value : Expr)  -- Double mapping + word offset write
  | setMappingUint (field : String) (key : Expr) (value : Expr)  -- Uint256-keyed mapping write (#154)
  | setMappingChain (field : String) (keys : List Expr) (value : Expr)  -- Arbitrary-depth mapping write (#1570)
  /-- Write to a named member of a struct-valued mapping.
      Resolves the member's word offset and optional packed bits at compile time.
      Generates the same Yul as `setMappingPackedWord` (or `setMappingWord` when
      unpacked), including alias slot mirror writes. -/
  | setStructMember (field : String) (key : Expr) (memberName : String) (value : Expr)
  /-- Write to a named member of a struct-valued double mapping.
      `setStructMember2 field key1 key2 memberName value` resolves the member's
      word offset and packed bits from the field's struct definition. -/
  | setStructMember2 (field : String) (key1 key2 : Expr) (memberName : String) (value : Expr)
  | require (cond : Expr) (message : String)
  | requireError (cond : Expr) (errorName : String) (args : List Expr)
  | revertError (errorName : String) (args : List Expr)
  | return (value : Expr)
  | returnValues (values : List Expr)  -- ABI-encode multiple static return words
  | returnArray (name : String)        -- ABI-encode dynamic uint256[] parameter loaded from calldata
  | returnBytes (name : String)        -- ABI-encode dynamic bytes parameter loaded from calldata
  | returnStorageWords (name : String) -- ABI-encode dynamic uint256[] from sload over a dynamic word-array parameter
  | mstore (offset value : Expr)
  | tstore (offset value : Expr)
  /-- First-class `calldatacopy(destOffset, sourceOffset, size)` statement. -/
  | calldatacopy (destOffset sourceOffset size : Expr)
  /-- First-class `returndatacopy(destOffset, sourceOffset, size)` statement. -/
  | returndataCopy (destOffset sourceOffset size : Expr)
  /-- Forward current returndata as revert payload (`returndatacopy` + `revert`). -/
  | revertReturndata
  | stop
  | ite (cond : Expr) (thenBranch : List Stmt) (elseBranch : List Stmt)  -- If/else (#179)
  | forEach (varName : String) (count : Expr) (body : List Stmt)  -- Bounded loop (#179)
  | emit (eventName : String) (args : List Expr)  -- Emit event (#153)
  | internalCall (functionName : String) (args : List Expr)  -- Internal call as statement (#181)
  | internalCallAssign (names : List String) (functionName : String) (args : List Expr)
  /-- Low-level log emission: `logN(dataOffset, dataSize, topic0, …, topicN-1)`.
      `topics` must contain 0–4 expressions (selects log0–log4).
      The caller is responsible for prior `mstore` calls that populate the data region. (#930) -/
  | rawLog (topics : List Expr) (dataOffset dataSize : Expr)
  /-- Perform an external call and bind ABI-decoded return values to local variables.
      Reverts with forwarded returndata on call failure or insufficient return data. -/
  | externalCallBind
      (resultVars : List String)  -- local vars to bind return values to
      (externalName : String)     -- name of the external function declaration
      (args : List Expr)          -- call arguments
  /-- Invoke an External Call Module with the given arguments.
      This generic variant delegates validation, compilation, and state analysis
      to the module's metadata and compile function. See Compiler.ECM (#964). -/
  | ecm (mod : ECM.ExternalCallModule) (args : List Expr)
  deriving Repr

structure FunctionSpec where
  name : String
  params : List Param
  returnType : Option FieldType  -- None for unit/void
  returns : List ParamType := []  -- preferred ABI return model; falls back to returnType when empty
  /-- Whether this entrypoint accepts non-zero msg.value. -/
  isPayable : Bool := false
  /-- Whether this entrypoint is ABI-marked as `view` (read-only intent). -/
  isView : Bool := false
  /-- Whether this entrypoint is ABI-marked as `pure` (no state/environment reads intent). -/
  isPure : Bool := false
  body : List Stmt
  /-- Whether this is an internal-only function (not exposed via selector dispatch) -/
  isInternal : Bool := false
  /-- Local proof obligations that isolate unsafe/assembly-shaped trust
      boundaries to this function rather than the entire contract. -/
  localObligations : List LocalObligation := []
  deriving Repr

structure ConstructorSpec where
  params : List Param  -- Constructor parameters (passed at deployment)
  /-- Whether deployment is allowed with non-zero msg.value. -/
  isPayable : Bool := false
  body : List Stmt     -- Initialization code
  /-- Local proof obligations that isolate unsafe/assembly-shaped trust
      boundaries to this constructor rather than the entire contract. -/
  localObligations : List LocalObligation := []
  deriving Repr

structure CompilationModel where
  name : String
  fields : List Field
  /-- Storage slots reserved for compatibility policy; compiler rejects field
      canonical/alias write slots that overlap these intervals. -/
  reservedSlotRanges : List ReservedSlotRange := []
  /-- Slot remap policy for compatibility mirror writes.
      Any field whose canonical slot is in a source interval also mirrors writes
      to the corresponding target slot with the same relative offset. -/
  slotAliasRanges : List SlotAliasRange := []
  constructor : Option ConstructorSpec  -- Deploy-time initialization with params
  functions : List FunctionSpec
  events : List EventDef := []  -- Event definitions (#153)
  errors : List ErrorDef := []  -- Custom errors (#586)
  externals : List ExternalFunction := []  -- External function declarations (#184)
  deriving Repr

/-!
## IR Generation from Spec

Automatically compile a CompilationModel to IRContract.
-/

-- Helper: Look up a field by name, resolving its canonical slot, and apply
-- a caller-supplied projection to the matched field and resolved slot.
private def findFieldByName (fields : List Field) (name : String)
    (extract : Field → Nat → α) : Option α :=
  let rec go (remaining : List Field) (idx : Nat) : Option α :=
    match remaining with
    | [] => none
    | f :: rest =>
        if f.name == name then some (extract f (f.slot.getD idx))
        else go rest (idx + 1)
  go fields 0

def findFieldSlot (fields : List Field) (name : String) : Option Nat :=
  findFieldByName fields name fun _ slot => slot

def findFieldWithResolvedSlot (fields : List Field) (name : String) : Option (Field × Nat) :=
  findFieldByName fields name fun f slot => (f, slot)

theorem field_mem_of_findFieldWithResolvedSlot_eq_some
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    f ∈ fields := by
  unfold findFieldWithResolvedSlot at h
  unfold findFieldByName at h
  -- h now involves findFieldByName.go. We generalise the index.
  suffices ∀ (flds : List Field) (idx : Nat),
      findFieldByName.go name (fun f slot => (f, slot)) flds idx = some (f, slot) →
      f ∈ flds by
    exact this fields 0 h
  intro flds idx hgo
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go] at hgo
  | cons hd tl ih =>
      simp only [findFieldByName.go] at hgo
      split at hgo
      · simp at hgo; exact hgo.1 ▸ List.Mem.head tl
      · exact List.Mem.tail hd (ih (idx + 1) hgo)

theorem fieldName_eq_of_findFieldWithResolvedSlot_eq_some
    {fields : List Field}
    {name : String}
    {f : Field}
    {slot : Nat}
    (h : findFieldWithResolvedSlot fields name = some (f, slot)) :
    f.name = name := by
  unfold findFieldWithResolvedSlot at h
  unfold findFieldByName at h
  suffices ∀ (flds : List Field) (idx : Nat),
      findFieldByName.go name (fun f slot => (f, slot)) flds idx = some (f, slot) →
      f.name = name by
    exact this fields 0 h
  intro flds idx hgo
  induction flds generalizing idx with
  | nil => simp [findFieldByName.go] at hgo
  | cons hd tl ih =>
      simp only [findFieldByName.go] at hgo
      split at hgo
      case isTrue hname =>
        simp at hgo; rw [← hgo.1]; exact beq_iff_eq.mp hname
      case isFalse =>
        exact ih (idx + 1) hgo

def findFieldWriteSlots (fields : List Field) (name : String) : Option (List Nat) :=
  findFieldByName fields name fun f slot => slot :: f.aliasSlots

def mappingTypeKeyTypes : MappingType → List MappingKeyType
  | .simple keyType => [keyType]
  | .nested outerKey innerKey => [outerKey, innerKey]
  | .chain keyTypes => keyTypes

def mappingTypeDepth (mt : MappingType) : Nat :=
  mt |> mappingTypeKeyTypes |> List.length

-- Helper: Is field a mapping?
def isMapping (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.dynamicArray _ => false
    | FieldType.mappingTyped _ => true
    | FieldType.mappingStruct _ _ => true
    | FieldType.mappingStruct2 _ _ _ => true
    | _ => false

-- Helper: Is field a double mapping?
def isMapping2 (fields : List Field) (name : String) : Bool :=
  fields.find? (·.name == name) |>.any fun f =>
    match f.ty with
    | FieldType.dynamicArray _ => false
    | FieldType.mappingTyped mt => mappingTypeDepth mt == 2
    | FieldType.mappingStruct2 _ _ _ => true
    | _ => false

-- Helper: Find struct members for a struct-valued mapping field.
def findStructMembers (fields : List Field) (name : String) : Option (List StructMember) :=
  fields.find? (·.name == name) |>.bind fun f =>
    match f.ty with
    | FieldType.mappingStruct _ members => some members
    | FieldType.mappingStruct2 _ _ members => some members
    | _ => none

-- Helper: Look up a named struct member from the members list.
def findStructMember (members : List StructMember) (memberName : String) : Option StructMember :=
  members.find? (·.name == memberName)


end Compiler.CompilationModel
