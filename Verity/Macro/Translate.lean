import Lean
import Compiler.Modules.ERC20
import Compiler.Modules.Precompiles
import Compiler.CompilationModel.InternalNaming
import Compiler.Keccak.Sponge
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean
open Lean.Elab
open Lean.Elab.Command

set_option hygiene false

abbrev Term := TSyntax `term
abbrev Cmd := TSyntax `command
abbrev Ident := TSyntax `ident
abbrev DoSeq := TSyntax `Lean.Parser.Term.doSeq

inductive ValueType where
  | uint256
  | int256
  | uint8
  | address
  | bytes32
  | bool
  | string
  | bytes
  | array (elemTy : ValueType)
  | tuple (elemTys : List ValueType)
  | unit
  | newtype (name : String) (baseType : ValueType)  -- Semantic newtype; erased to baseType (#1727 Steps 3b/3c)
  | struct (name : String) (fields : List (String × ValueType)) -- Named ABI tuple with executable field access (#1750)
  | adt (name : String) (maxFields : Nat)  -- User-defined ADT (tagged union); maxFields = max variant field count (#1727 Step 5b)
  deriving Repr, BEq

inductive MappingKeyType where
  | address
  | uint256
  deriving BEq

structure StructMemberDecl where
  name : String
  wordOffset : Nat
  packed : Option (Nat × Nat) := none
  deriving BEq

inductive StorageType where
  | scalar (ty : ValueType)
  | dynamicArray (elemTy : Compiler.CompilationModel.StorageArrayElemType)
  | mappingAddressToUint256
  | mapping2AddressToAddressToUint256
  | mappingUintToUint256
  | mappingChain (keyTypes : List MappingKeyType)
  | mappingStruct (keyType : MappingKeyType) (members : List StructMemberDecl)
  | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMemberDecl)
  deriving BEq

structure StorageFieldDecl where
  ident : Ident
  name : String
  ty : StorageType
  slotNum : Nat
  adtInfo? : Option (String × Nat) := none

structure ParamDecl where
  ident : Ident
  name : String
  ty : ValueType

structure ErrorDecl where
  ident : Ident
  name : String
  params : Array ValueType

structure ConstantDecl where
  ident : Ident
  name : String
  ty : ValueType
  body : Term

structure ImmutableDecl where
  ident : Ident
  name : String
  ty : ValueType
  body : Term

structure ExternalDecl where
  ident : Ident
  name : String
  params : Array ValueType
  returnTys : Array ValueType

/-- A user-defined semantic newtype declared in the `types` section.
    At the language level the type is distinct from its base type; at the
    EVM/Yul level it is erased to the base type (zero overhead).
    (#1727, Axis 1 Step 3a) -/
structure NewtypeDecl where
  ident : Ident
  name : String
  baseType : ValueType

/-- A named ABI struct declared in the `verity_contract` body.
    It elaborates to a Lean `structure` for executable tests, while the compiler
    lowers it as an ABI tuple with named projection support. -/
structure StructDecl where
  ident : Ident
  name : String
  fields : Array ParamDecl

/-- A single variant (constructor) of a user-defined algebraic data type.
    E.g. `| Ok(value : Uint256)` or `| None`.
    (#1727, Axis 1 Step 5a) -/
structure AdtVariantDecl where
  ident : Ident
  name : String
  fields : Array ParamDecl

/-- A user-defined algebraic data type (tagged union) declared in the `inductive` section.
    E.g. `Result := | Ok(value : Uint256) | Err(code : Uint256)`.
    At the EVM level, ADTs use max-width tagged union encoding.
    (#1727, Axis 1 Step 5a) -/
structure AdtDecl where
  ident : Ident
  name : String
  variants : Array AdtVariantDecl

structure LocalObligationDecl where
  ident : Ident
  name : String
  obligation : String
  proofStatus : Compiler.ProofStatus

inductive InitGuardDecl where
  | initializer (fieldIdent : Ident) (fieldName : String)
  | reinitializer (fieldIdent : Ident) (fieldName : String) (version : Nat)

structure FunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTy : ValueType
  isPayable : Bool := false
  isView : Bool := false
  noExternalCalls : Bool := false
  /-- When true, the function is annotated `allow_post_interaction_writes` and
      CEI (Checks-Effects-Interactions) enforcement is bypassed.  This is the
      explicit trust-surface opt-out in the escalation ladder (#1728, Axis 2 Step 2a). -/
  allowPostInteractionWrites : Bool := false
  /-- When `some fieldIdent`, the function is annotated `nonreentrant(field)`.
      The named storage field is used as a reentrancy lock.  CEI enforcement is
      bypassed because the lock prevents reentrant state corruption.
      (#1728, Axis 2 Step 2b — known-safe guard rung) -/
  nonReentrantLock : Option Ident := none
  /-- When true, the function is annotated `cei_safe` — the user asserts CEI
      safety via a machine-checked proof obligation.  CEI enforcement is bypassed
      and a proof obligation is generated.
      (#1728, Axis 2 Step 2b — Lean proof rung) -/
  ceiSafe : Bool := false
  /-- When `some fieldIdent`, the function is annotated `requires(field)`.
      The named Address-typed storage field is an access-control role.
      A `require(caller == roleHolder)` check is auto-injected at the start
      of the function body.  (#1728, Axis 2 Step 2c) -/
  requiresRole : Option Ident := none
  initGuard? : Option InitGuardDecl := none
  /-- Storage field names declared via `modifies(field1, field2)`.
      When non-empty, the compiler validates that the function body only
      writes to fields in this set and auto-generates a `_frame` theorem. -/
  modifies : Array Ident := #[]
  localObligations : Array LocalObligationDecl := #[]
  body : Term

private partial def valueTypeSignatureComponent : ValueType → String
  | .uint256 => "scalar_uint256"
  | .int256 => "scalar_int256"
  | .uint8 => "scalar_uint8"
  | .address => "scalar_address"
  | .bool => "scalar_bool"
  | .bytes32 => "scalar_bytes32"
  | .string => "scalar_string"
  | .bytes => "scalar_bytes"
  | .unit => "scalar_unit"
  | .array ty => "array_" ++ valueTypeSignatureComponent ty
  | .tuple tys => "tuple" ++ toString tys.length ++ "_" ++ String.intercalate "__" (tys.map valueTypeSignatureComponent)
  | .newtype name baseType => "newtype_" ++ name ++ "_" ++ valueTypeSignatureComponent baseType
  | .struct name fields =>
      "struct_" ++ name ++ "_" ++
        String.intercalate "__" (fields.map (fun field => field.fst ++ "_" ++ valueTypeSignatureComponent field.snd))
  | .adt name _ => "adt_" ++ name

private def functionSignatureKey (fn : FunctionDecl) : String :=
  fn.name ++ "(" ++ String.intercalate "," (fn.params.toList.map (fun p => valueTypeSignatureComponent p.ty)) ++ ")"

private partial def valueTypeAbiSignatureComponent : ValueType → String
  | .newtype _ baseType => valueTypeAbiSignatureComponent baseType
  | .array ty => "array_" ++ valueTypeAbiSignatureComponent ty
  | .tuple tys => "tuple" ++ toString tys.length ++ "_" ++ String.intercalate "__" (tys.map valueTypeAbiSignatureComponent)
  | .struct _ fields =>
      "tuple" ++ toString fields.length ++ "_" ++ String.intercalate "__" (fields.map (fun field => valueTypeAbiSignatureComponent field.snd))
  | .adt _ maxFields =>
      "tuple" ++ toString (maxFields + 1) ++ "_" ++
        String.intercalate "__" ("scalar_uint8" :: List.replicate maxFields "scalar_uint256")
  | ty => valueTypeSignatureComponent ty

private def functionAbiSignatureKey (fn : FunctionDecl) : String :=
  fn.name ++ "(" ++ String.intercalate "," (fn.params.toList.map (fun p => valueTypeAbiSignatureComponent p.ty)) ++ ")"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent part => nameComponents parent ++ [part]
  | .num parent n => nameComponents parent ++ [toString n]

private def mapNameLastComponent (f : String → String) : Name → Name
  | .anonymous => .anonymous
  | .str parent part => .str parent (f part)
  | .num parent n => .str parent (f (toString n))

private def isQualifiedFunctionName (name : Name) : Bool :=
  (nameComponents name).length == 2

private def qualifiedFunctionModelName (name : Name) : Name :=
  mapNameLastComponent (fun part => part ++ "_model") name

private def qualifiedFunctionDisplayName (name : Name) : String :=
  String.intercalate "." (nameComponents name)

private def internalHelperSpecNameFor (fn : FunctionDecl) : String :=
  Compiler.CompilationModel.internalFunctionPrefix ++ toString fn.ident.getId

private def qualifiedInternalHelperBaseName (name : Name) : String :=
  let encodedComponents :=
    nameComponents name |>.map fun component =>
      s!"{component.length}_{component}"
  Compiler.CompilationModel.internalFunctionPrefix ++
    "qualified_" ++ String.intercalate "_" encodedComponents

private def qualifiedInternalHelperName (functions : Array FunctionDecl) (name : Name) : String :=
  Compiler.CompilationModel.pickFreshName
    (qualifiedInternalHelperBaseName name)
    ((functions.map internalHelperSpecNameFor).toList)

private def qualifiedInternalHelperNameFromUsed
    (usedNames : List String)
    (name : Name) : String :=
  Compiler.CompilationModel.pickFreshName (qualifiedInternalHelperBaseName name) usedNames

private partial def qualifiedFunctionAppSyntax? (stx : Term) : Option (Name × Array Term) :=
  match stx.raw with
  | .node _ `Lean.Parser.Term.doExpr args =>
      match args.getD 0 Syntax.missing with
      | inner => qualifiedFunctionAppSyntax? ⟨inner⟩
  | .node _ `Lean.Parser.Term.paren args =>
      match args.getD 1 Syntax.missing with
      | inner => qualifiedFunctionAppSyntax? ⟨inner⟩
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ _ raw _ =>
          if isQualifiedFunctionName raw then
            let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
            some (raw, argTerms)
          else
            none
      | _ => none
  | _ => none

private def overloadedFunctionIdentName (fn : FunctionDecl) : String :=
  -- Length-prefix each component so the suffix encoding is injective.
  -- Component strings can contain `_` (e.g. `newtype_Foo_scalar_uint256`,
  -- `tuple2_scalar_uint256__scalar_bool`), so a plain `_` join is ambiguous
  -- and distinct overloads can collapse to the same identifier.
  let suffix :=
    match fn.params.toList.map (fun p => valueTypeSignatureComponent p.ty) with
    | [] => "0"
    | parts => String.join (parts.map fun p => toString p.length ++ "x" ++ p)
  fn.name ++ "__" ++ suffix

private def assignOverloadInternalIdents (functions : Array FunctionDecl) :
    Array FunctionDecl :=
  functions.map fun fn =>
    if functions.any (fun other => other.name == fn.name && functionSignatureKey other != functionSignatureKey fn) then
      { fn with ident := mkIdentFrom fn.ident (Name.mkSimple (overloadedFunctionIdentName fn)) }
    else
      fn

structure ConstructorDecl where
  params : Array ParamDecl
  isPayable : Bool := false
  localObligations : Array LocalObligationDecl := #[]
  body : Term

private def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩
private def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

private partial def expectTermListLiteral (stx : Term) : CommandElabM (Array Term) := do
  match stx with
  | `(term| [ $[$xs],* ]) => pure xs
  | `(term| ($inner:term)) => expectTermListLiteral inner
  | _ => throwErrorAt stx "expected list literal [..]"

private partial def collectTupleElems (stx : Syntax) : Array Syntax :=
  if stx.isAtom then
    #[]
  else if stx.getKind == `null then
    stx.getArgs.foldl (fun acc child => acc ++ collectTupleElems child) #[]
  else
    #[stx]

private def tupleElemsFromSyntax? (stx : Syntax) : Option (Array Syntax) :=
  if stx.getKind == `Lean.Parser.Term.tuple then
    some (collectTupleElems stx[1])
  else
    none

private partial def expectMappingKeyTerms (stx : Term) : CommandElabM (Array Term) := do
  expectTermListLiteral stx

private partial def collectArrowChainTypes (stx : Term) : CommandElabM (List Term × Term) := do
  match stx with
  | `(term| $lhs:term → $rhs:term) =>
      let (rest, resultTy) ← collectArrowChainTypes rhs
      pure (lhs :: rest, resultTy)
  | _ => pure ([], stx)

private def natFromSyntax (stx : Syntax) : CommandElabM Nat :=
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural literal"

private partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(term| ($inner)) => stripParens inner
  | _ => stx

private def structValueTypeFields (decl : StructDecl) : List (String × ValueType) :=
  decl.fields.toList.map fun field => (field.name, field.ty)

private partial def valueTypeFromSyntax
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (ty : Term) : CommandElabM ValueType := do
  let ty := stripParens ty
  let (arrowArgs, _arrowResult) ← collectArrowChainTypes ty
  if !arrowArgs.isEmpty then
    throwErrorAt ty
      "unsupported function type in verity_contract boundary (#1747); internal function-pointer parameters are not first-class in the CompilationModel yet. Pass an explicit mode/enum and dispatch to direct internal helper calls, or inline the helper call at each call site."
  match ty with
  | `(term| Uint256) => pure .uint256
  | `(term| Int256) => pure .int256
  | `(term| Uint8) => pure .uint8
  | `(term| Address) => pure .address
  | `(term| Bytes32) => pure .bytes32
  | `(term| Bool) => pure .bool
  | `(term| String) => pure .string
  | `(term| Bytes) => pure .bytes
  | `(term| Array $elemTy:term) =>
      let elem ← valueTypeFromSyntax newtypes structDecls adtDecls elemTy
      match elem with
      | .unit => throwErrorAt ty "unsupported type '{ty}'; Array Unit is not allowed"
      | .array _ => throwErrorAt ty "unsupported type '{ty}'; nested arrays are not supported"
      | _ => pure (.array elem)
  | `(term| Tuple [ $[$elemTys:term],* ]) =>
      let elems ← elemTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      if elems.size < 2 then
        throwErrorAt ty "tuple types must have at least 2 elements"
      pure (.tuple elems.toList)
  | `(term| Unit) => pure .unit
  | `(term| $id:ident) =>
      let tyName := toString id.getId
      -- Try resolving as a user-defined newtype (#1727, Axis 1 Steps 3a/3b)
      match newtypes.find? (fun nt => nt.name == tyName) with
      | some nt => pure (.newtype nt.name nt.baseType)
      | none =>
        -- Try resolving as a user-defined ADT (#1727, Axis 1 Step 5b)
        match structDecls.find? (fun s => s.name == tyName) with
        | some decl => pure (.struct decl.name (structValueTypeFields decl))
        | none =>
          match adtDecls.find? (fun a => a.name == tyName) with
          | some decl =>
              let maxFields := decl.variants.foldl (fun acc v => max acc v.fields.size) 0
              pure (.adt decl.name maxFields)
          | none => throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Int256, Uint8, Address, Bytes32, Bool, String, Bytes, Array <type>, Tuple [...], Unit, a user-defined struct, or a user-defined type from the `types` or `inductive` section"
  | _ =>
      throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Int256, Uint8, Address, Bytes32, Bool, String, Bytes, Array <type>, Tuple [...], Unit, a user-defined struct, or a user-defined type from the `types` or `inductive` section"

private def storageTypeFromSyntax (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (ty : Term) : CommandElabM StorageType := do
  let keyTypeFromSyntax (stx : Term) : CommandElabM MappingKeyType := do
    match stx with
    | `(term| Address) => pure .address
    | `(term| Uint256) => pure .uint256
    | _ => throwErrorAt stx "unsupported mapping key type; expected Address or Uint256"

  let structMemberFromSyntax (stx : TSyntax `verityStructMember) : CommandElabM StructMemberDecl := do
    match stx with
    | `(verityStructMember| $name:ident @word $wordOffset:num) =>
        pure {
          name := toString name.getId
          wordOffset := ← natFromSyntax wordOffset
        }
    | `(verityStructMember| $name:ident @word $wordOffset:num packed($offset:num,$width:num)) =>
        pure {
          name := toString name.getId
          wordOffset := ← natFromSyntax wordOffset
          packed := some (← natFromSyntax offset, ← natFromSyntax width)
        }
    | _ => throwErrorAt stx "invalid struct member declaration"

  let storageArrayElemTypeFromValueType (elemTy : ValueType) : CommandElabM Compiler.CompilationModel.StorageArrayElemType :=
    match elemTy with
    | .uint256 => pure .uint256
    | .address => pure .address
    | .bool => pure .bool
    | .bytes32 => pure .bytes32
    | _ =>
        throwErrorAt ty
          s!"storage dynamic arrays currently support only one-word elements (Uint256, Address, Bool, Bytes32) on the macro path, got {reprStr (ValueType.array elemTy)}"

  let (arrowArgs, arrowResult) ← collectArrowChainTypes ty
  if !arrowArgs.isEmpty then
    match arrowResult with
    | `(term| Uint256) =>
        let keyTypes ← arrowArgs.mapM keyTypeFromSyntax
        match keyTypes with
        | [.address] => pure .mappingAddressToUint256
        | [.uint256] => pure .mappingUintToUint256
        | [.address, .address] => pure .mapping2AddressToAddressToUint256
        | _ => pure (.mappingChain keyTypes)
    | _ =>
        throwErrorAt ty "unsupported mapping value type; expected Uint256"
  else
    match ty with
  | `(term| MappingStruct($keyTy:term,[ $[$members:verityStructMember],* ])) =>
      pure <| .mappingStruct
        (← keyTypeFromSyntax keyTy)
        ((← members.mapM structMemberFromSyntax).toList)
  | `(term| MappingStruct2($outerKey:term,$innerKey:term,[ $[$members:verityStructMember],* ])) =>
      pure <| .mappingStruct2
        (← keyTypeFromSyntax outerKey)
        (← keyTypeFromSyntax innerKey)
        ((← members.mapM structMemberFromSyntax).toList)
  | _ => do
      let vt ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      match vt with
      | .array elemTy => pure (.dynamicArray (← storageArrayElemTypeFromValueType elemTy))
      | .tuple _ => throwErrorAt ty "storage fields cannot be Tuple; use mapping encodings"
      | .struct _ _ =>
          throwErrorAt ty
            "top-level named struct storage fields are not supported yet (#1758); flatten the struct into explicit scalar storage fields with fixed slots, or use MappingStruct/MappingStruct2 for struct-valued mappings"
      | _ => pure (.scalar vt)

private def modelMappingKeyTypeTerm : MappingKeyType → CommandElabM Term
  | .address => `(Compiler.CompilationModel.MappingKeyType.address)
  | .uint256 => `(Compiler.CompilationModel.MappingKeyType.uint256)

private def storageTypeMappingKeyTypes? : StorageType → Option (List MappingKeyType)
  | .mappingAddressToUint256 => some [.address]
  | .mapping2AddressToAddressToUint256 => some [.address, .address]
  | .mappingUintToUint256 => some [.uint256]
  | .mappingChain keyTypes => some keyTypes
  | _ => none

private def storageTypeMappingDepth? (ty : StorageType) : Option Nat :=
  storageTypeMappingKeyTypes? ty |>.map List.length

private def storageKeyTypeContractTerm : MappingKeyType → CommandElabM Term
  | .address => `(Address)
  | .uint256 => `(Uint256)

private def modelStructMemberTerm (member : StructMemberDecl) : CommandElabM Term := do
  let packedTerm ←
    match member.packed with
    | none => `(none)
    | some (offset, width) =>
        `(some { offset := $(natTerm offset), width := $(natTerm width) })
  `(Compiler.CompilationModel.StructMember.mk
      $(strTerm member.name)
      $(natTerm member.wordOffset)
      $packedTerm)

private def modelFieldTypeTerm (ty : StorageType) : CommandElabM Term :=
  match ty with
  | .scalar .uint256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .int256 => `(Compiler.CompilationModel.FieldType.uint256)
  | .scalar .uint8 => throwError "storage fields cannot be Uint8; use Uint256 encoding"
  | .scalar .address => `(Compiler.CompilationModel.FieldType.address)
  | .scalar .bytes32 => throwError "storage fields cannot be Bytes32; use Uint256 encoding"
  | .scalar .bool => throwError "storage fields cannot be Bool; use Uint256 (0/1) encoding"
  | .scalar .string => throwError "storage fields cannot be String; use Uint256 encoding"
  | .scalar .bytes => throwError "storage fields cannot be Bytes; use Uint256 encoding"
  | .scalar (.array _) => throwError "storage fields cannot be Array; use mapping encodings"
  | .scalar (.tuple _) => throwError "storage fields cannot be Tuple; use mapping encodings"
  | .scalar (.struct _ _) =>
      throwError
        "top-level named struct storage fields are not supported yet (#1758); flatten the struct into explicit scalar storage fields with fixed slots, or use MappingStruct/MappingStruct2 for struct-valued mappings"
  | .scalar .unit => throwError "storage fields cannot be Unit"
  | .scalar (.newtype _ baseType) => modelFieldTypeTerm (.scalar baseType)  -- Erased to base type
  | .scalar (.adt name maxFields) =>
      `(Compiler.CompilationModel.FieldType.adt $(Lean.quote name) $(Lean.quote maxFields))
  | .dynamicArray .uint256 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.uint256)
  | .dynamicArray .address => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.address)
  | .dynamicArray .bool => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.bool)
  | .dynamicArray .uint8 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.uint8)
  | .dynamicArray .bytes32 => `(Compiler.CompilationModel.FieldType.dynamicArray Compiler.CompilationModel.StorageArrayElemType.bytes32)
  | .mappingAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.address))
  | .mapping2AddressToAddressToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.nested
            Compiler.CompilationModel.MappingKeyType.address
            Compiler.CompilationModel.MappingKeyType.address))
  | .mappingUintToUint256 =>
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.simple Compiler.CompilationModel.MappingKeyType.uint256))
  | .mappingChain keyTypes => do
      let keyTypeTerms := (← keyTypes.mapM modelMappingKeyTypeTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingTyped
          (Compiler.CompilationModel.MappingType.chain [ $[$keyTypeTerms],* ]))
  | .mappingStruct keyType members => do
      let keyTypeTerm ← modelMappingKeyTypeTerm keyType
      let memberTerms := (← members.mapM modelStructMemberTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingStruct $keyTypeTerm [ $[$memberTerms],* ])
  | .mappingStruct2 outerKey innerKey members => do
      let outerKeyTerm ← modelMappingKeyTypeTerm outerKey
      let innerKeyTerm ← modelMappingKeyTypeTerm innerKey
      let memberTerms := (← members.mapM modelStructMemberTerm).toArray
      `(Compiler.CompilationModel.FieldType.mappingStruct2 $outerKeyTerm $innerKeyTerm [ $[$memberTerms],* ])

private partial def modelParamTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Compiler.CompilationModel.ParamType.uint256)
  | .int256 => `(Compiler.CompilationModel.ParamType.int256)
  | .uint8 => `(Compiler.CompilationModel.ParamType.uint8)
  | .address => `(Compiler.CompilationModel.ParamType.address)
  | .bytes32 => `(Compiler.CompilationModel.ParamType.bytes32)
  | .bool => `(Compiler.CompilationModel.ParamType.bool)
  | .string => `(Compiler.CompilationModel.ParamType.string)
  | .bytes => `(Compiler.CompilationModel.ParamType.bytes)
  | .array elemTy => do
      `(Compiler.CompilationModel.ParamType.array $(← modelParamTypeTerm elemTy))
  | .tuple elemTys => do
      let elemTerms ← elemTys.mapM modelParamTypeTerm
      `(Compiler.CompilationModel.ParamType.tuple [ $[$elemTerms.toArray],* ])
  | .struct _ fields => do
      let elemTerms ← fields.mapM (fun field => modelParamTypeTerm field.snd)
      `(Compiler.CompilationModel.ParamType.tuple [ $[$elemTerms.toArray],* ])
  | .unit => throwError "function parameters cannot be Unit"
  | .newtype name baseType => do
      let baseTerm ← modelParamTypeTerm baseType
      `(Compiler.CompilationModel.ParamType.newtypeOf $(Lean.quote name) $baseTerm)
  | .adt name maxFields => do
      `(Compiler.CompilationModel.ParamType.adt $(Lean.quote name) $(Lean.quote maxFields))

private def modelReturnTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `(none)
  | .uint256 => `(some Compiler.CompilationModel.FieldType.uint256)
  | .int256 => `(none)
  | .uint8 => `(none)
  | .address => `(some Compiler.CompilationModel.FieldType.address)
  | .bytes32 => `(none)
  | .bool => `(none)
  | .string => `(none)
  | .bytes => `(none)
  | .array _ => `(none)
  | .tuple _ => `(none)
  | .struct _ _ => `(none)
  | .newtype _ baseType => modelReturnTypeTerm baseType
  | .adt _ _ => `(none)  -- ADTs are not directly returnable as single FieldType

private partial def modelReturnsTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `([])
  | .uint256 => `([Compiler.CompilationModel.ParamType.uint256])
  | .int256 => `([Compiler.CompilationModel.ParamType.int256])
  | .uint8 => `([Compiler.CompilationModel.ParamType.uint8])
  | .address => `([Compiler.CompilationModel.ParamType.address])
  | .bytes32 => `([Compiler.CompilationModel.ParamType.bytes32])
  | .bool => `([Compiler.CompilationModel.ParamType.bool])
  | .string => `([Compiler.CompilationModel.ParamType.string])
  | .bytes => `([Compiler.CompilationModel.ParamType.bytes])
  | .array elemTy => do
      `([Compiler.CompilationModel.ParamType.array $(← modelParamTypeTerm elemTy)])
  | .tuple elemTys => do
      let elemTerms ← elemTys.mapM modelParamTypeTerm
      `([ $[$elemTerms.toArray],* ])
  | .struct _ fields => do
      let elemTerms ← fields.mapM (fun field => modelParamTypeTerm field.snd)
      `([ $[$elemTerms.toArray],* ])
  | .newtype name baseType => do
      let baseTerm ← modelParamTypeTerm baseType
      `([Compiler.CompilationModel.ParamType.newtypeOf $(Lean.quote name) $baseTerm])
  | .adt name maxFields => do
      `([Compiler.CompilationModel.ParamType.adt $(Lean.quote name) $(Lean.quote maxFields)])

private partial def valueTypeFromModelParamType? : Compiler.CompilationModel.ParamType → Option ValueType
  | .uint256 => some .uint256
  | .int256 => some .int256
  | .uint8 => some .uint8
  | .address => some .address
  | .bool => some .bool
  | .bytes32 => some .bytes32
  | .string => some .string
  | .bytes => some .bytes
  | .array elemTy => do
      let elem ← valueTypeFromModelParamType? elemTy
      some (.array elem)
  | .tuple elemTys => do
      let elems ← elemTys.mapM valueTypeFromModelParamType?
      some (.tuple elems)
  | .newtypeOf name baseType => do
      let base ← valueTypeFromModelParamType? baseType
      some (.newtype name base)
  | .adt name maxFields => some (.adt name maxFields)
  | .fixedArray _ _ => none

private unsafe def evalQualifiedFunctionSpec
    (fnName : Name) : CommandElabM Compiler.CompilationModel.FunctionSpec := do
  let modelTerm : Term := ⟨(mkIdent (qualifiedFunctionModelName fnName)).raw⟩
  liftTermElabM do
    let expectedType := mkConst ``Compiler.CompilationModel.FunctionSpec
    let expr ← Lean.Elab.Term.elabTermEnsuringType modelTerm expectedType
    Lean.Meta.evalExpr Compiler.CompilationModel.FunctionSpec expectedType expr .unsafe

private unsafe def qualifiedFunctionReturnTypes
    (stx : Syntax)
    (fnName : Name) : CommandElabM (Array ValueType) := do
  let spec ←
    try
      unsafe evalQualifiedFunctionSpec fnName
    catch _ =>
      throwErrorAt stx
        s!"unable to inspect qualified helper '{qualifiedFunctionDisplayName fnName}'; expected generated model '{qualifiedFunctionModelName fnName}' to be in scope"
  let mut result := #[]
  for returnTy in spec.returns do
    match valueTypeFromModelParamType? returnTy with
    | some ty => result := result.push ty
    | none =>
        throwErrorAt stx
          s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns unsupported value type {repr returnTy}"
  pure result

mutual
private partial def mkTupleContractType (elemTys : List ValueType) : CommandElabM Term := do
  let rec go : List ValueType → CommandElabM Term
    | [] => throwError "tuple types must have at least 2 elements"
    | [ty] => contractValueTypeTerm ty
    | ty :: rest => do
        `(($(← contractValueTypeTerm ty) × $(← go rest)))
  go elemTys

private partial def contractValueTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .uint256 => `(Uint256)
  | .int256 => `(Int256)
  | .uint8 => `(Uint256)
  | .address => `(Address)
  | .bytes32 => `(Uint256)
  | .bool => `(Bool)
  | .string => `(String)
  | .bytes => `(ByteArray)
  | .array elemTy => do
      `(Array $(← contractValueTypeTerm elemTy))
  | .tuple elemTys => mkTupleContractType elemTys
  | .unit => `(Unit)
  | .newtype _ baseType => contractValueTypeTerm baseType  -- Erased to base type at contract level
  | .struct name _ => pure (mkIdent (Name.mkSimple name))
  | .adt _ _ => `(Uint256)  -- ADTs represented as tag value at contract level
end

private def parseStorageField (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (stx : Syntax) : CommandElabM StorageFieldDecl := do
  match stx with
  | `(verityStorageField| $name:ident : $ty:term := slot $slotNum:num) =>
      let parsedTy ← storageTypeFromSyntax newtypes structDecls adtDecls ty
      let adtInfo? :=
        match parsedTy with
        | .scalar (.adt adtName maxFields) => some (adtName, maxFields)
        | _ => none
      pure {
        ident := name
        name := toString name.getId
        ty := parsedTy
        slotNum := ← natFromSyntax slotNum
        adtInfo? := adtInfo?
      }
  | _ => throwErrorAt stx "invalid storage field declaration"

private def parseParam (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes structDecls adtDecls ty
      }
  | _ => throwErrorAt stx "invalid parameter declaration"

private def parseNewtype (stx : Syntax) : CommandElabM NewtypeDecl := do
  match stx with
  | `(verityNewtype| $name:ident : $ty:term) =>
      let baseType ← valueTypeFromSyntax #[] #[] #[] ty
      -- Validate: newtypes must be based on scalar types (not arrays, tuples, or unit)
      match baseType with
      | .array _ => throwErrorAt ty "newtype base type must be a scalar type, not an array"
      | .tuple _ => throwErrorAt ty "newtype base type must be a scalar type, not a tuple"
      | .unit => throwErrorAt ty "newtype base type must be a scalar type, not Unit"
      | _ => pure ()
      pure {
        ident := name
        name := toString name.getId
        baseType := baseType
      }
  | _ => throwErrorAt stx "invalid type declaration"

private def parseStructDecl (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (stx : Syntax) : CommandElabM StructDecl := do
  match stx with
  | `(verityStructDecl| struct $name:ident where $[$fields:verityParam],*) =>
      let parsedFields ← fields.mapM (parseParam newtypes structDecls #[])
      if parsedFields.isEmpty then
        throwErrorAt name s!"struct '{toString name.getId}' must have at least one field"
      let mut seenFieldNames : Array String := #[]
      for field in parsedFields do
        if seenFieldNames.contains field.name then
          throwErrorAt field.ident s!"duplicate field '{field.name}' in struct '{toString name.getId}'"
        seenFieldNames := seenFieldNames.push field.name
      pure { ident := name, name := toString name.getId, fields := parsedFields }
  | _ => throwErrorAt stx "invalid struct declaration"

/-- Parse a single ADT variant: `| Name(field1 : Type1, field2 : Type2)` or `| Name`.
    (#1727, Axis 1 Step 5a) -/
private def parseAdtVariant (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM AdtVariantDecl := do
  match stx with
  | `(verityAdtVariant| | $name:ident ($[$params:verityParam],*)) =>
      let parsedParams ← params.mapM (parseParam newtypes #[] #[])
      pure { ident := name, name := toString name.getId, fields := parsedParams }
  | `(verityAdtVariant| | $name:ident) =>
      pure { ident := name, name := toString name.getId, fields := #[] }
  | _ => throwErrorAt stx "invalid ADT variant declaration"

/-- Parse a full ADT declaration: `Name := | Variant1(...) | Variant2(...)`.
    (#1727, Axis 1 Step 5a) -/
private def parseAdtDecl (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM AdtDecl := do
  match stx with
  | `(verityAdtDecl| $name:ident := $[$variants:verityAdtVariant]*) =>
      let parsedVariants ← variants.mapM (parseAdtVariant newtypes)
      if parsedVariants.isEmpty then
        throwErrorAt name s!"ADT '{toString name.getId}' must have at least one variant"
      if parsedVariants.size > 256 then
        throwErrorAt name
          s!"ADT '{toString name.getId}' has {parsedVariants.size} variants, but ADT tags are encoded as Uint8 and support at most 256 variants"
      -- Validate: no duplicate variant names within this ADT
      let mut seenVariantNames : Array String := #[]
      for v in parsedVariants do
        if seenVariantNames.contains v.name then
          throwErrorAt v.ident s!"duplicate variant name '{v.name}' in ADT '{toString name.getId}'"
        seenVariantNames := seenVariantNames.push v.name
      pure { ident := name, name := toString name.getId, variants := parsedVariants }
  | _ => throwErrorAt stx "invalid ADT declaration"

private def parseError (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ErrorDecl := do
  match stx with
  | `(verityError| error $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      }
  | _ => throwErrorAt stx "invalid custom error declaration"

private def parseConstant (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM ConstantDecl := do
  match stx with
  | `(verityConstant| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes #[] #[] ty
        body := body
      }
  | _ => throwErrorAt stx "invalid constant declaration"

private def parseImmutable (newtypes : Array NewtypeDecl) (stx : Syntax) : CommandElabM ImmutableDecl := do
  match stx with
  | `(verityImmutable| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax newtypes #[] #[] ty
        body := body
      }
  | _ => throwErrorAt stx "invalid immutable declaration"

private def parseExternal (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl) (adtDecls : Array AdtDecl) (stx : Syntax) : CommandElabM ExternalDecl := do
  match stx with
  | `(verityExternal| external $name:ident ($[$params:term],*) -> ($[$returnTys:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := ← returnTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      }
  | `(verityExternal| external $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := #[]
      }
  | _ => throwErrorAt stx "invalid external declaration"

private def parseProofStatusIdent (stx : Syntax) : CommandElabM Compiler.ProofStatus := do
  match stx with
  | .ident _ raw _ _ =>
      match raw.toString with
      | "proved" => pure .proved
      | "assumed" => pure .assumed
      | "unchecked" => pure .unchecked
      | other =>
          throwErrorAt stx s!"unsupported proof status '{other}'; expected proved, assumed, or unchecked"
  | _ => throwErrorAt stx "expected proof status identifier"

private def parseLocalObligation (stx : Syntax) : CommandElabM LocalObligationDecl := do
  match stx with
  | `(verityLocalObligation| $name:ident := $status:ident $obligation:str) =>
      pure {
        ident := name
        name := toString name.getId
        obligation := obligation.getString
        proofStatus := ← parseProofStatusIdent status
      }
  | _ => throwErrorAt stx "invalid local obligation declaration"

private structure ParsedMutability where
  isPayable : Bool := false
  isView : Bool := false
  noExternalCalls : Bool := false
  allowPostInteractionWrites : Bool := false
  nonReentrantLock : Option Ident := none
  ceiSafe : Bool := false

private def parseMutabilityModifiers
    (mods : Array (TSyntax `verityMutability))
    (stx : Syntax) : CommandElabM ParsedMutability := do
  let mut result : ParsedMutability := {}
  for mod in mods do
    match mod with
    | `(verityMutability| payable) =>
        if result.isPayable then
          throwErrorAt mod "duplicate 'payable' modifier"
        result := { result with isPayable := true }
    | `(verityMutability| view) =>
        if result.isView then
          throwErrorAt mod "duplicate 'view' modifier"
        result := { result with isView := true }
    | `(verityMutability| no_external_calls) =>
        if result.noExternalCalls then
          throwErrorAt mod "duplicate 'no_external_calls' modifier"
        result := { result with noExternalCalls := true }
    | `(verityMutability| allow_post_interaction_writes) =>
        if result.allowPostInteractionWrites then
          throwErrorAt mod "duplicate 'allow_post_interaction_writes' modifier"
        result := { result with allowPostInteractionWrites := true }
    | `(verityMutability| nonreentrant($field:ident)) =>
        if result.nonReentrantLock.isSome then
          throwErrorAt mod "duplicate 'nonreentrant' modifier"
        result := { result with nonReentrantLock := some field }
    | `(verityMutability| cei_safe) =>
        if result.ceiSafe then
          throwErrorAt mod "duplicate 'cei_safe' modifier"
        result := { result with ceiSafe := true }
    | _ => throwErrorAt stx "invalid function mutability modifier"
  pure result

private def parseModifies (stx : TSyntax `verityModifies) : CommandElabM (Array Ident) := do
  match stx with
  | `(verityModifies| modifies($[$fields:ident],*)) =>
      let result := fields
      -- Check for duplicates
      let mut seen : Array String := #[]
      for f in result do
        let s := toString f.getId
        if seen.contains s then
          throwErrorAt f s!"duplicate field '{s}' in modifies annotation"
        seen := seen.push s
      pure result
  | _ => throwErrorAt stx "invalid modifies annotation"

private def parseInitGuard (stx : TSyntax `verityInitGuard) : CommandElabM InitGuardDecl := do
  match stx with
  | `(verityInitGuard| initializer($field:ident)) =>
      pure (.initializer field (toString field.getId))
  | `(verityInitGuard| reinitializer($field:ident, $version:num)) => do
      let versionNat ← natFromSyntax version
      if versionNat == 0 then
        throwErrorAt version "reinitializer version must be greater than 0"
      pure (.reinitializer field (toString field.getId) versionNat)
  | _ => throwErrorAt stx "invalid initializer guard"

private def parseLocalObligations
    (stx : TSyntax `verityLocalObligations) : CommandElabM (Array LocalObligationDecl) := do
  match stx with
  | `(verityLocalObligations| local_obligations [ $[$obligations:verityLocalObligation],* ]) =>
      obligations.mapM parseLocalObligation
  | _ => throwErrorAt stx "invalid local obligations declaration"

private def hiddenEntrypointIdent (name : String) : Ident :=
  mkIdent (Name.mkSimple s!"__verity_{name}")

private def parseSpecialEntrypoint (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(veritySpecialEntrypoint| receive $[$localObligations?:verityLocalObligations]? := $body:term) => do
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := hiddenEntrypointIdent "receive"
        name := "receive"
        params := #[]
        returnTy := .unit
        isPayable := true
        localObligations := parsedLocalObligations
        body := body
      }
  | `(veritySpecialEntrypoint| fallback $[$localObligations?:verityLocalObligations]? := $body:term) => do
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := hiddenEntrypointIdent "fallback"
        name := "fallback"
        params := #[]
        returnTy := .unit
        localObligations := parsedLocalObligations
        body := body
      }
  | _ => throwErrorAt stx "invalid special entrypoint declaration"

private def parseFunction (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(verityFunction| function $[$mods:verityMutability]* $name:ident ($[$params:verityParam],*) $[$guard?:verityInitGuard]? $[$requiresRoleClause?:verityRequiresRole]? $[$modifiesClause?:verityModifies]? $[$localObligations?:verityLocalObligations]? : $retTy:term := $body:term) => do
      let mut_ ← parseMutabilityModifiers mods stx
      let parsedParams ← params.mapM (parseParam newtypes structDecls adtDecls)
      let parsedReturnTy ← valueTypeFromSyntax newtypes structDecls adtDecls retTy
      match parsedReturnTy with
      | .struct _ _ =>
          throwErrorAt retTy "function return types cannot be named structs; return an explicit Tuple [...] instead"
      | _ => pure ()
      let parsedGuard? ←
        match guard? with
        | some guard => pure (some (← parseInitGuard guard))
        | none => pure none
      let parsedRequiresRole ←
        match requiresRoleClause? with
        | some roleClause =>
            match roleClause with
            | `(verityRequiresRole| requires($roleField:ident)) => pure (some roleField)
            | _ => throwErrorAt roleClause "invalid requires annotation"
        | none => pure none
      let parsedModifies ←
        match modifiesClause? with
        | some modClause => parseModifies modClause
        | none => pure #[]
      let parsedLocalObligations ←
        match localObligations? with
        | some obligations => parseLocalObligations obligations
        | none => pure #[]
      pure {
        ident := name
        name := toString name.getId
        params := parsedParams
        returnTy := parsedReturnTy
        isPayable := mut_.isPayable
        isView := mut_.isView
        noExternalCalls := mut_.noExternalCalls
        allowPostInteractionWrites := mut_.allowPostInteractionWrites
        nonReentrantLock := mut_.nonReentrantLock
        ceiSafe := mut_.ceiSafe
        requiresRole := parsedRequiresRole
        initGuard? := parsedGuard?
        modifies := parsedModifies
        localObligations := parsedLocalObligations
        body := body
      }
  | _ => throwErrorAt stx "invalid function declaration"

private def parseConstructor (newtypes : Array NewtypeDecl) (structDecls : Array StructDecl := #[]) (adtDecls : Array AdtDecl := #[]) (stx : Syntax) : CommandElabM ConstructorDecl := do
  match stx with
  | `(verityConstructor| constructor ($[$params:verityParam],*) payable local_obligations [ $[$obligations:verityLocalObligation],* ] := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        isPayable := true
        localObligations := ← obligations.mapM parseLocalObligation
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) payable := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        isPayable := true
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) local_obligations [ $[$obligations:verityLocalObligation],* ] := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        localObligations := ← obligations.mapM parseLocalObligation
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) := $body:term) =>
      pure {
        params := ← params.mapM (parseParam newtypes structDecls adtDecls)
        body := body
      }
  | _ => throwErrorAt stx "invalid constructor declaration"

private def immutableHiddenName (imm : ImmutableDecl) : String :=
  s!"__immutable_{imm.name}"

private def storageFieldFootprintSize (field : StorageFieldDecl) : Nat :=
  match field.ty with
  | .scalar (.adt _ maxFields) => maxFields + 1
  | _ => 1

private def immutableSlotIndex (fields : Array StorageFieldDecl) (idx : Nat) : Nat :=
  let nextUserSlot := fields.foldl (fun maxSlot field =>
    max maxSlot (field.slotNum + storageFieldFootprintSize field)) 0
  nextUserSlot + idx

private def immutableSlotIdent (imm : ImmutableDecl) : Ident :=
  mkIdent (Name.mkSimple s!"__verity_immutable_slot_{imm.name}")

def immutableStorageFieldDecl
    (fields : Array StorageFieldDecl)
    (imm : ImmutableDecl)
    (idx : Nat) : StorageFieldDecl :=
  {
    ident := immutableSlotIdent imm
    name := immutableHiddenName imm
    ty := match imm.ty with
      | .uint256 | .int256 | .uint8 | .bytes32 | .bool => .scalar .uint256
      | .address => .scalar .address
      | _ => .scalar imm.ty
    slotNum := immutableSlotIndex fields idx
    adtInfo? := none
  }

private def validateImmutableType (imm : ImmutableDecl) : CommandElabM Unit :=
  match imm.ty with
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool => pure ()
  | _ =>
      throwErrorAt imm.ident
        s!"contract immutables currently support only Uint256, Int256, Uint8, Address, Bytes32, and Bool; '{imm.name}' uses unsupported type"

private def validateImmutableBodyType
    (imm : ImmutableDecl)
    (ctorParams : Array ParamDecl) : CommandElabM Unit := do
  let expectedTy ← contractValueTypeTerm imm.ty
  let mut wrappedBody : Term := imm.body
  wrappedBody ← `(term| (($wrappedBody : $expectedTy)))
  for param in ctorParams.reverse do
    wrappedBody ← `(term| fun ($(param.ident) : $(← contractValueTypeTerm param.ty)) => $wrappedBody)
  liftTermElabM do
    discard <| Lean.Elab.Term.elabTerm wrappedBody none

private partial def containsAdtValueType : ValueType → Bool
  | .adt _ _ => true
  | .newtype _ baseType => containsAdtValueType baseType
  | .array elemTy => containsAdtValueType elemTy
  | .tuple elemTys => elemTys.any containsAdtValueType
  | .struct _ fields => fields.any (fun field => containsAdtValueType field.snd)
  | _ => false

private def rejectExecutableBoundaryAdt
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  if containsAdtValueType ty then
    throwErrorAt stx
      s!"{context} uses an ADT at the executable contract boundary. ADT storage is supported, but ABI/function boundary ADT lowering is not yet implemented; pass scalar fields explicitly or keep the ADT in storage."

private def externalExecutableWordType? : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool => true
  | .newtype _ baseType => externalExecutableWordType? baseType
  | _ => false

private def validateExternalExecutableType
    (extIdent : Ident)
    (extName : String)
    (ty : ValueType)
    (role : String) : CommandElabM Unit := do
  if !externalExecutableWordType? ty then
    throwErrorAt extIdent
      s!"linked external '{extName}' uses unsupported {role} type; executable externalCall currently supports only Uint256, Int256, Uint8, Address, Bytes32, and Bool"

private def tupleElemsFromTerm? (stx : Term) : Option (Array Term) :=
  tupleElemsFromSyntax? (stripParens stx).raw |>.map (·.map (fun syn => ⟨syn⟩))

private def throwNonCompileTimeConstantError (stx : Syntax) (what : String) : CommandElabM α :=
  throwErrorAt stx s!"contract constants must be compile-time expressions; '{what}' is runtime-dependent"

private def lookupStructMemberDecl
    (fields : Array StorageFieldDecl)
    (fieldName memberName : String)
    (expectNested : Bool) : CommandElabM StructMemberDecl := do
  let field ←
    match fields.find? (fun f => f.name == fieldName) with
    | some f => pure f
    | none => throwError s!"unknown storage field '{fieldName}'"
  let members ←
    match field.ty with
    | .mappingStruct _ members =>
        if expectNested then
          throwError s!"field '{fieldName}' is not a nested struct mapping"
        pure members
    | .mappingStruct2 _ _ members =>
        if expectNested then pure members
        else throwError s!"field '{fieldName}' is a nested struct mapping; use structMember2/setStructMember2"
    | _ =>
        if expectNested then
          throwError s!"field '{fieldName}' is not a nested struct mapping"
        else
          throwError s!"field '{fieldName}' is not a struct-valued mapping"
  match members.find? (fun member => member.name == memberName) with
  | some member => pure member
  | none => throwError s!"unknown struct member '{memberName}' on field '{fieldName}'"

private def lookupStorageField (fields : Array StorageFieldDecl) (name : String) : CommandElabM StorageFieldDecl := do
  match fields.find? (fun f => f.name == name) with
  | some f => pure f
  | none => throwError s!"unknown storage field '{name}'"

private def resolveInitGuardField
    (fields : Array StorageFieldDecl)
    (guard : InitGuardDecl)
    (stx : Syntax) : CommandElabM StorageFieldDecl := do
  let field ←
    match guard with
    | .initializer _ fieldName => lookupStorageField fields fieldName
    | .reinitializer _ fieldName _ => lookupStorageField fields fieldName
  match field.ty with
  | .scalar .uint256 => pure field
  | _ =>
      throwErrorAt stx
        s!"initializer guard field '{field.name}' must be a Uint256 storage slot"

private def initGuardRequireMessage : InitGuardDecl → String
  | .initializer .. => "initializer already run"
  | .reinitializer _ _ version => s!"reinitializer({version}) already run"

private def initGuardVersionTerm (version : Nat) : Term :=
  natTerm version

private def initGuardPreludeStmtTerms
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.initGuard? with
  | none => pure #[]
  | some guard =>
      let field ← resolveInitGuardField fields guard fn.ident
      let message := strTerm (initGuardRequireMessage guard)
      match guard with
      | .initializer _ _ =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.eq
                    (Compiler.CompilationModel.Expr.storage $(strTerm field.name))
                    (Compiler.CompilationModel.Expr.literal 0))
                  $message),
            ← `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm field.name)
                  (Compiler.CompilationModel.Expr.literal 1))
          ]
      | .reinitializer _ _ version =>
          pure #[
            ← `(Compiler.CompilationModel.Stmt.require
                  (Compiler.CompilationModel.Expr.lt
                    (Compiler.CompilationModel.Expr.storage $(strTerm field.name))
                    (Compiler.CompilationModel.Expr.literal $(initGuardVersionTerm version)))
                  $message),
            ← `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm field.name)
                  (Compiler.CompilationModel.Expr.literal $(initGuardVersionTerm version)))
          ]

private def mkInitGuardedBody
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM Term := do
  match fn.initGuard? with
  | none => pure fn.body
  | some guard =>
      let field ← resolveInitGuardField fields guard fn.ident
      let currentVersion := mkIdent (Name.mkSimple s!"__verity_init_version_{field.name}")
      let message := strTerm (initGuardRequireMessage guard)
      match fn.body with
      | `(term| do $[$elems:doElem]*) =>
          match guard with
          | .initializer _ _ =>
              `(do
                  let $currentVersion ← getStorage $field.ident
                  require ($currentVersion == 0) $message
                  setStorage $field.ident 1
                  $[$elems:doElem]*)
          | .reinitializer _ _ version =>
              `(do
                  let $currentVersion ← getStorage $field.ident
                  require ($currentVersion < $(initGuardVersionTerm version)) $message
                  setStorage $field.ident $(initGuardVersionTerm version)
                  $[$elems:doElem]*)
      | _ => throwErrorAt fn.body "function body must be a do block"

/-- Resolve the storage field referenced by a `requires(role)` annotation.
    The role must be an Address-typed scalar storage field. -/
private def resolveRoleField
    (fields : Array StorageFieldDecl) (roleIdent : Ident) (fnIdent : Ident)
    : CommandElabM StorageFieldDecl := do
  let roleName := toString roleIdent.getId
  match fields.find? (fun f => f.name == roleName) with
  | none =>
      throwErrorAt roleIdent s!"function '{toString fnIdent.getId}': requires references unknown storage field '{roleName}'; known fields: {(fields.map (·.name)).toList}"
  | some field =>
      match field.ty with
      | .scalar .address | .scalar (.newtype _ .address) => pure field
      | _ => throwErrorAt roleIdent s!"function '{toString fnIdent.getId}': requires({roleName}) must reference an Address-typed storage field, but '{roleName}' has a different type"

/-- Generate IR-level prelude statements for a `requires(role)` annotation.
    Injects `Stmt.require (Expr.eq Expr.caller (Expr.storage roleField)) "Access denied: only role"`.
    (#1728, Axis 2 Step 2c) -/
private def roleGuardPreludeStmtTerms
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.requiresRole with
  | none => pure #[]
  | some roleIdent =>
      let field ← resolveRoleField fields roleIdent fn.ident
      let message := strTerm s!"Access denied: caller is not {field.name}"
      pure #[
        ← `(Compiler.CompilationModel.Stmt.require
              (Compiler.CompilationModel.Expr.eq
                (Compiler.CompilationModel.Expr.caller)
                (Compiler.CompilationModel.Expr.storageAddr $(strTerm field.name)))
              $message)
      ]

/-- Transform the source-level do-block body to inject a role access control check
    at the start.  Injects `let __sender ← msgSender; let __roleHolder ← getStorageAddr field;
    require (__sender == __roleHolder) "Access denied: caller is not role"`.
    (#1728, Axis 2 Step 2c) -/
private def mkRoleGuardedBody
    (fields : Array StorageFieldDecl)
    (fn : FunctionDecl) : CommandElabM Term := do
  match fn.requiresRole with
  | none => pure fn.body
  | some roleIdent =>
      let field ← resolveRoleField fields roleIdent fn.ident
      let senderVar := mkIdent (Name.mkSimple s!"__verity_role_sender_{field.name}")
      let holderVar := mkIdent (Name.mkSimple s!"__verity_role_holder_{field.name}")
      let message := strTerm s!"Access denied: caller is not {field.name}"
      match fn.body with
      | `(term| do $[$elems:doElem]*) =>
          `(do
              let $senderVar ← msgSender
              let $holderVar ← getStorageAddr $field.ident
              require ($senderVar == $holderVar) $message
              $[$elems:doElem]*)
      | _ => throwErrorAt fn.body "function body must be a do block"

private def mkImmutableBoundBody
    (fields : Array StorageFieldDecl)
    (immutableDecls : Array ImmutableDecl)
    (fn : FunctionDecl)
    (body : Term) : CommandElabM Term := do
  let visibleImmutables := immutableDecls.filter fun imm =>
    !fn.params.any (fun p => p.name == imm.name)
  match body with
  | `(term| do $[$elems:doElem]*) =>
      let preludeElemGroups ← visibleImmutables.zipIdx.mapM fun (imm, idx) => do
        let slotField := immutableStorageFieldDecl fields imm idx
        match imm.ty with
        | .uint256 | .uint8 | .bytes32 =>
            pure #[← `(doElem| let $(imm.ident) ← getStorage $(slotField.ident))]
        | .int256 =>
            pure #[← `(doElem| let $(imm.ident) := toInt256 (← getStorage $(slotField.ident)))]
        | .bool =>
            let rawName := mkIdent (Name.mkSimple s!"__verity_immutable_raw_{imm.name}")
            pure #[
              ← `(doElem| let $rawName ← getStorage $(slotField.ident)),
              ← `(doElem| let $(imm.ident) := ($rawName != 0))
            ]
        | .address =>
            pure #[← `(doElem| let $(imm.ident) ← getStorageAddr $(slotField.ident))]
        | _ => throwErrorAt imm.ident s!"immutable '{imm.name}' uses unsupported type"
      let preludeElems := preludeElemGroups.foldl (· ++ ·) #[]
      `(do $[$preludeElems:doElem]* $[$elems:doElem]*)
  | _ => throwErrorAt body "function body must be a do block"

private def expectStringLiteral (stx : Term) : CommandElabM String :=
  match (stripParens stx).raw.isStrLit? with
  | some s => pure s
  | none => throwErrorAt stx "expected string literal"

private def expectStringOrIdent (stx : Term) : CommandElabM String := do
  match stripParens stx with
  | `(term| $id:ident) => pure (toString id.getId)
  | other => expectStringLiteral other

private def expectStringList (stx : Term) : CommandElabM (Array String) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      xs.mapM expectStringOrIdent
  | _ => throwErrorAt stx "expected list literal [..]"

private def tupleBinderNames? (stx : Syntax) : Option (Array (Option String)) := do
  let elems ← tupleElemsFromSyntax? stx
  elems.mapM fun elem =>
    match elem with
    | .ident _ raw _ _ => some raw.toString
    | .node _ `Lean.Parser.Term.hole _ => some none
    | _ => none

private def ensureFreshLocalNames
    (locals : Array String)
    (names : Array (Option String))
    (stx : Syntax) : CommandElabM Unit := do
  let boundNames := names.filterMap id
  let rec firstDuplicate (seen : Array String) (rest : Array String) (idx : Nat) : Option String :=
    if h : idx < rest.size then
      let name := rest[idx]
      if seen.contains name then
        some name
      else
        firstDuplicate (seen.push name) rest (idx + 1)
    else
      none
  match firstDuplicate #[] boundNames 0 with
  | some dup => throwErrorAt stx s!"duplicate local variable '{dup}'"
  | none => pure ()
  for name in boundNames do
    if locals.contains name then
      throwErrorAt stx s!"duplicate local variable '{name}'"

private def freshDiscardName (usedNames : List String) (idx : Nat) : String :=
  let base := s!"__tuple_discard_{idx}"
  if !usedNames.contains base then
    base
  else
    let rec go (suffix : Nat) (remaining : Nat) : String :=
      let candidate := s!"{base}_{suffix}"
      if !usedNames.contains candidate then
        candidate
      else
        match remaining with
        | 0 => s!"{base}_fresh"
        | n + 1 => go (suffix + 1) n
    go 1 usedNames.length

private def tupleParamElemExprs?
    (params : Array ParamDecl)
    (name : String) : CommandElabM (Option (Array Term)) := do
  match params.find? (fun p => p.name == name) with
  | some p =>
      match p.ty with
      | .tuple elemTys => do
          let exprs ← (elemTys.toArray.zipIdx).mapM fun (_ty, idx) =>
            `(Compiler.CompilationModel.Expr.param $(strTerm s!"{name}_{idx}"))
          pure (some exprs)
      | _ => pure none
  | none => pure none

private def isTupleComponentRef (params : Array ParamDecl) (name : String) : Bool :=
  -- Check if `name` matches `<paramName>_<digit>` for a tuple-typed param
  match name.splitOn "_" with
  | [baseName, indexStr] =>
      match indexStr.toNat? with
      | some idx =>
          params.any fun p =>
            p.name == baseName &&
            match p.ty with
            | .tuple elemTys => idx < elemTys.length
            | _ => false
      | none => false
  | _ => false

private def lookupVarExpr (params : Array ParamDecl) (locals : Array String) (name : String) : CommandElabM Term := do
  if params.any (fun p => p.name == name) then
    `(Compiler.CompilationModel.Expr.param $(strTerm name))
  else if isTupleComponentRef params name then
    `(Compiler.CompilationModel.Expr.param $(strTerm name))
  else if locals.contains name then
    `(Compiler.CompilationModel.Expr.localVar $(strTerm name))
  else
    throwError s!"unknown variable '{name}'"

private abbrev TypedLocal := String × ValueType

private def typedLocalNames (locals : Array TypedLocal) : Array String :=
  locals.map Prod.fst

private def matchesBareName (actual bare : String) : Bool :=
  actual == bare || actual.endsWith s!".{bare}"

private def declaredNameMatches (query declared : String) : Bool :=
  matchesBareName query declared || matchesBareName declared query

private def contextAccessorBareName? (name : String) : Option String :=
  if matchesBareName name "msgSender" then some "msgSender"
  else if matchesBareName name "msgValue" then some "msgValue"
  else if matchesBareName name "selfBalance" then some "selfBalance"
  else if matchesBareName name "blockTimestamp" then some "blockTimestamp"
  else if matchesBareName name "blockNumber" then some "blockNumber"
  else if matchesBareName name "blobbasefee" then some "blobbasefee"
  else if matchesBareName name "contractAddress" then some "contractAddress"
  else if matchesBareName name "chainid" then some "chainid"
  else none

private def findContextAccessorShadowName?
    (params : Array ParamDecl) (locals : Array String) (name : String) : Option String :=
  match params.find? (fun p => matchesBareName p.name name) with
  | some param => some param.name
  | none => locals.find? (fun localName => matchesBareName localName name)

private def isSignedWordValueType : ValueType → Bool
  | .int256 => true
  | .newtype _ baseType => isSignedWordValueType baseType
  | _ => false

private def isWordLikeValueType : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .address | .bytes32 => true
  | .newtype _ baseType => isWordLikeValueType baseType
  | _ => false

private def isSingleWordStaticValueType : ValueType → Bool
  | .bool => true
  | .newtype _ baseType => isSingleWordStaticValueType baseType
  | ty => isWordLikeValueType ty

private partial def staticAbiWordCount? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool => some 1
  | .tuple elemTys =>
      elemTys.foldl
        (fun acc ty =>
          match acc, staticAbiWordCount? ty with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .struct _ fields =>
      fields.foldl
        (fun acc field =>
          match acc, staticAbiWordCount? field.snd with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .newtype _ baseType => staticAbiWordCount? baseType
  | _ => none

private partial def abiLocalHeadWordCount? : ValueType → Option Nat
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool
  | .string | .bytes | .array _ => some 1
  | .tuple elemTys =>
      elemTys.foldl
        (fun acc ty =>
          match acc, abiLocalHeadWordCount? ty with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .struct _ fields =>
      fields.foldl
        (fun acc field =>
          match acc, abiLocalHeadWordCount? field.snd with
          | some n, some m => some (n + m)
          | _, _ => none)
        (some 0)
  | .newtype _ baseType => abiLocalHeadWordCount? baseType
  | .adt _ _ | .unit => none

private partial def valueTypeUsesDynamicData : ValueType → Bool
  | .string | .bytes | .array _ => true
  | .tuple elemTys => elemTys.any valueTypeUsesDynamicData
  | .struct _ fields => fields.any (fun field => valueTypeUsesDynamicData field.snd)
  | .newtype _ baseType => valueTypeUsesDynamicData baseType
  | .adt _ _ => false  -- ADTs are stored as tag + fixed-width slots, not dynamic
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool | .unit => false

private partial def abiParentHeadWordCount? (ty : ValueType) : Option Nat :=
  match ty with
  | .string | .bytes | .array _ => some 1
  | .tuple _ | .struct _ _ =>
      if valueTypeUsesDynamicData ty then
        some 1
      else
        abiLocalHeadWordCount? ty
  | .newtype _ baseType => abiParentHeadWordCount? baseType
  | .uint256 | .int256 | .uint8 | .address | .bytes32 | .bool => some 1
  | .adt _ _ | .unit => none

private def classifyWordArithmeticResultType
    (stx : Syntax)
    (context : String)
    (lhsTy rhsTy : ValueType) : CommandElabM ValueType := do
  unless isWordLikeValueType lhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr lhsTy}"
  unless isWordLikeValueType rhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr rhsTy}"
  if isSignedWordValueType lhsTy || isSignedWordValueType rhsTy then
    if lhsTy == .int256 && rhsTy == .int256 then
      pure .int256
    else
      throwErrorAt stx
        s!"{context} requires explicit casts when mixing Int256 with non-Int256 words; got {reprStr lhsTy} and {reprStr rhsTy}"
  else
    pure .uint256

private def classifyUnsignedWordArithmeticResultType
    (stx : Syntax)
    (context : String)
    (lhsTy rhsTy : ValueType) : CommandElabM ValueType := do
  unless isWordLikeValueType lhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr lhsTy}"
  unless isWordLikeValueType rhsTy do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {reprStr rhsTy}"
  pure .uint256

private def isNatLiteralTerm (stx : Term) : Bool :=
  match stripParens stx with
  | `(term| $_n:num) => true
  | _ => false

private def numericLiteralCompatibleValueType : ValueType → Bool
  | .uint256 | .int256 | .uint8 => true
  | .newtype _ baseType => numericLiteralCompatibleValueType baseType
  | _ => false

private def argumentTypeMatchesParam (arg : Term) (argTy paramTy : ValueType) : Bool :=
  argTy == paramTy || (argTy == .uint256 && isNatLiteralTerm arg && numericLiteralCompatibleValueType paramTy)

private def argumentTypesMatchParams (args : Array Term) (argTypes : Array ValueType)
    (params : Array ParamDecl) : Bool :=
  args.size == params.size && Id.run do
    for idx in [:args.size] do
      let some arg := args[idx]? | return false
      let some argTy := argTypes[idx]? | return false
      let some param := params[idx]? | return false
      unless argumentTypeMatchesParam arg argTy param.ty do
        return false
    return true

private def preferSignedNumericLiteralPeer
    (lhs rhs : Term)
    (lhsTy rhsTy : ValueType) : ValueType × ValueType :=
  let lhsTy :=
    if lhsTy == .uint256 && rhsTy == .int256 && isNatLiteralTerm lhs then .int256 else lhsTy
  let rhsTy :=
    if rhsTy == .uint256 && lhsTy == .int256 && isNatLiteralTerm rhs then .int256 else rhsTy
  (lhsTy, rhsTy)

private def lookupTypedLocalType? (locals : Array TypedLocal) (name : String) : Option ValueType :=
  locals.findSome? fun localTy =>
    if localTy.1 == name then some localTy.2 else none

private def tupleParamElemType? (params : Array ParamDecl) (name : String) : Option ValueType :=
  match name.splitOn "_" with
  | [baseName, indexStr] =>
      match indexStr.toNat? with
      | some idx =>
          params.findSome? fun p =>
            if p.name == baseName then
              match p.ty with
              | .tuple elemTys => elemTys.toArray[idx]?
              | _ => none
            else
              none
      | none => none
  | _ => none

private partial def structProjectionPath? (stx : Term) : Option (Term × List String) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      match (toString id.getId).splitOn "." with
      | root :: field :: rest =>
          some (mkIdent (Name.mkSimple root), field :: rest)
      | _ => none
  | `(term| $base:term.$field:ident) =>
      let fieldName := toString field.getId
      match structProjectionPath? base with
      | some (root, path) => some (root, path ++ [fieldName])
      | none => some (base, [fieldName])
  | _ => none

private partial def structFieldPath?
    (ty : ValueType)
    (path : List String)
    (indices : List Nat := []) : Option (ValueType × List Nat) :=
  -- The returned indices are the recursive tuple binding path used by
  -- ParamLoading.staticParamBindingNames, not flattened ABI word offsets.
  match path with
  | [] => some (ty, indices)
  | fieldName :: rest =>
      match ty with
      | .struct _ fields =>
          fields.zipIdx.findSome? fun (field, idx) =>
            if field.fst == fieldName then
              structFieldPath? field.snd rest (indices ++ [idx])
            else
              none
      | _ => none

private partial def structFieldHeadOffset?
    (ty : ValueType)
    (path : List String)
    (baseOffset : Nat := 0) : Option (ValueType × Nat) :=
  match path with
  | [] => none
  | fieldName :: rest =>
      match ty with
      | .struct _ fields =>
          let rec go (remaining : List (String × ValueType)) (curOffset : Nat) : Option (ValueType × Nat) :=
            match remaining with
            | [] => none
            | (name, fieldTy) :: more =>
                if name == fieldName then
                  match rest with
                  | [] => some (fieldTy, curOffset)
                  | _ =>
                      if valueTypeUsesDynamicData fieldTy then
                        none
                      else
                        structFieldHeadOffset? fieldTy rest curOffset
                else
                  match abiParentHeadWordCount? fieldTy with
                  | some n => go more (curOffset + n)
                  | none => none
          go fields baseOffset
      | _ => none

private def paramStructProjectionResolved?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType × ValueType) := do
  let resolve (rootName : String) (path : List String) := do
    let param ← params.find? (fun p => p.name == rootName)
    let (fieldTy, indices) ← structFieldPath? param.ty path
    if indices.isEmpty then
      none
    else
      some (String.intercalate "_" (rootName :: indices.map toString), fieldTy, param.ty)
  match (stripParens stx).raw with
  | .ident _ raw _ _ =>
      let parts := raw.toString.splitOn "."
      let rec findParamPath : List String → Option (String × List String)
        | [] | [_] => none
        | rootName :: fieldName :: rest =>
            if params.any (fun p => p.name == rootName) then
              some (rootName, fieldName :: rest)
            else
              findParamPath (fieldName :: rest)
      match findParamPath parts with
      | some (rootName, path) => resolve rootName path
      | none => none
  | _ =>
      let (root, path) ← structProjectionPath? stx
      match stripParens root with
      | `(term| $id:ident) => resolve (toString id.getId) path
      | _ => none

private def arrayElementStructProjectionResolved?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let (root, path) ← structProjectionPath? stx
  match stripParens root with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName ←
        match stripParens name with
        | `(term| $id:ident) => some (toString id.getId)
        | _ => none
      let param ← params.find? (fun p => p.name == paramName)
      let elemTy ← match param.ty with
        | .array elemTy => some elemTy
        | _ => none
      let (fieldTy, wordOffset) ← structFieldHeadOffset? elemTy path
      some (paramName, index, fieldTy, elemTy, wordOffset)
  | _ => none

private def arrayElementStructProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × Term × ValueType × ValueType × Nat) := do
  let resolved@(_, _, fieldTy, _, _) ← arrayElementStructProjectionResolved? params stx
  if isSingleWordStaticValueType fieldTy then
    some resolved
  else
    none

private def paramStructProjection?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) := do
  let (paramName, fieldTy, rootTy) ← paramStructProjectionResolved? params stx
  if isSingleWordStaticValueType fieldTy && !valueTypeUsesDynamicData rootTy then
    some (paramName, fieldTy)
  else
    none

private def isParamStructNonLeafProjection (params : Array ParamDecl) (stx : Term) : Bool :=
  match paramStructProjectionResolved? params stx with
  | some (_, fieldTy, _) => !isSingleWordStaticValueType fieldTy
  | none => false

private def isParamStructDynamicRootProjection (params : Array ParamDecl) (stx : Term) : Bool :=
  match paramStructProjectionResolved? params stx with
  | some (_, fieldTy, rootTy) => isSingleWordStaticValueType fieldTy && valueTypeUsesDynamicData rootTy
  | none => false

private def throwStructNonLeafProjectionError (stx : Term) : CommandElabM α :=
  throwErrorAt stx
    "non-leaf struct parameter projection is not supported; project a scalar or static single-word leaf field instead"

private def throwStructDynamicRootProjectionError (stx : Term) : CommandElabM α :=
  throwErrorAt stx
    "struct parameter projection from an ABI-dynamic root is not supported; use a static struct parameter or wait for nested-dynamic ABI decoding"

private def renderValueType (ty : ValueType) : String :=
  reprStr ty

private def requireWordLikeType (stx : Syntax) (context : String) (ty : ValueType) : CommandElabM Unit := do
  unless isWordLikeValueType ty do
    throwErrorAt stx s!"{context} requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got {renderValueType ty}"

private def requireBoolType (stx : Syntax) (context : String) (ty : ValueType) : CommandElabM Unit := do
  unless ty == .bool do
    throwErrorAt stx s!"{context} requires Bool, got {renderValueType ty}"

private def requireSupportedReturnArrayType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  match ty with
  | .array elemTy =>
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt stx
          s!"{context} currently supports only arrays with single-word static elements on the compilation-model path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx s!"{context} requires an Array value, got {renderValueType ty}"

private def requireSupportedArrayElementSourceType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM ValueType := do
  match ty with
  | .array elemTy =>
      unless isSingleWordStaticValueType elemTy do
        throwErrorAt stx
          s!"{context} currently supports only arrays with single-word static elements on the compilation-model path, got {renderValueType ty}"
      pure elemTy
  | _ =>
      throwErrorAt stx s!"{context} requires an Array parameter, got {renderValueType ty}"

private def requireSupportedArrayElementTupleSourceType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM ValueType := do
  match ty with
  | .array elemTy@(.tuple _) =>
      match staticAbiWordCount? elemTy, abiLocalHeadWordCount? elemTy with
      | some _, _ => pure elemTy
      | none, some _ => pure elemTy
      | none, none =>
          throwErrorAt stx
            s!"{context} currently supports only arrays with ABI-decodable tuple elements, got {renderValueType ty}"
  | .array elemTy =>
      match staticAbiWordCount? elemTy with
      | some _ => pure elemTy
      | none =>
          throwErrorAt stx
            s!"{context} currently supports only arrays with static ABI-word elements on the tuple arrayElement path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx s!"{context} requires an Array parameter, got {renderValueType ty}"

private def directParamNameWithType?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      let name := toString id.getId
      params.findSome? fun p =>
        if p.name == name then
          some (name, p.ty)
        else
          none
  | _ => none

private def requireDirectParamRef
    (stx : Term)
    (context : String)
    (params : Array ParamDecl) : CommandElabM ValueType := do
  match directParamNameWithType? params stx with
  | some (_, paramTy) => pure paramTy
  | none =>
      throwErrorAt stx
        s!"{context} currently requires a direct parameter reference on the compilation-model path"

private def requireSupportedReturnBytesType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  unless ty == .bytes || ty == .string do
    throwErrorAt stx
      s!"{context} requires a Bytes or String parameter on the compilation-model path, got {renderValueType ty}"

private def requireSupportedReturnStorageWordsType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  match ty with
  | .array elemTy =>
      if isSingleWordStaticValueType elemTy then
        pure ()
      else
        throwErrorAt stx
          s!"{context} requires an array with single-word static elements on the compilation-model path, got {renderValueType ty}"
  | _ =>
      throwErrorAt stx
        s!"{context} requires an Array parameter on the compilation-model path, got {renderValueType ty}"

private def requireEqComparableTypes (stx : Syntax) (lhsTy rhsTy : ValueType) : CommandElabM Unit := do
  let bothWordLike := isWordLikeValueType lhsTy && isWordLikeValueType rhsTy
  let bothBool := lhsTy == .bool && rhsTy == .bool
  let bothDynamicBytes := (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes)
  unless bothWordLike || bothBool || bothDynamicBytes do
    throwErrorAt stx
      s!"equality is currently supported only for Bool, matching bytes/string params, and word-like values (Uint256, Int256, Uint8, Address, Bytes32); got {renderValueType lhsTy} and {renderValueType rhsTy}"

private def directDynamicComparableParamName?
    (params : Array ParamDecl)
    (stx : Term) : Option (String × ValueType) :=
  match stripParens stx with
  | `(term| $id:ident) =>
      let name := toString id.getId
      params.findSome? fun p =>
        if p.name == name && (p.ty == .string || p.ty == .bytes) then
          some (name, p.ty)
        else
          none
  | _ => none

private def dynamicEqParamNames
    (stx : Syntax)
    (params : Array ParamDecl)
    (lhs rhs : Term)
    (lhsTy rhsTy : ValueType) : CommandElabM (String × String) := do
  match directDynamicComparableParamName? params lhs, directDynamicComparableParamName? params rhs with
  | some (lhsName, lhsParamTy), some (rhsName, rhsParamTy) =>
      if lhsParamTy == lhsTy && rhsParamTy == rhsTy && lhsTy == rhsTy then
        pure (lhsName, rhsName)
      else
        throwErrorAt stx
          s!"bytes/string equality requires matching direct parameter references, got {renderValueType lhsTy} and {renderValueType rhsTy}"
  | _, _ =>
      throwErrorAt stx
        "bytes/string equality currently requires direct parameter references on the compilation-model path"

private def requireSameOrWordLikeTypes (stx : Syntax) (context : String) (lhsTy rhsTy : ValueType) : CommandElabM Unit := do
  unless lhsTy == rhsTy || (isWordLikeValueType lhsTy && isWordLikeValueType rhsTy) do
    throwErrorAt stx
      s!"{context} requires matching branch types, got {renderValueType lhsTy} and {renderValueType rhsTy}"

private def requireDeclaredValueType
    (stx : Syntax)
    (context : String)
    (expectedTy actualTy : ValueType) : CommandElabM Unit := do
  unless actualTy == expectedTy || (isWordLikeValueType actualTy && isWordLikeValueType expectedTy) do
    throwErrorAt stx
      s!"{context} expects {renderValueType expectedTy}, got {renderValueType actualTy}"

private def localBindingUsesDynamicData : ValueType → Bool :=
  valueTypeUsesDynamicData

private def requireSupportedLocalBindingType
    (stx : Syntax)
    (context : String)
    (ty : ValueType) : CommandElabM Unit := do
  if localBindingUsesDynamicData ty then
    throwErrorAt stx
      s!"{context} currently cannot bind dynamic values ({renderValueType ty}) to local variables on the compilation-model path; use the parameter directly"

private unsafe def qualifiedTupleBindTypedLocals
    (stx : Syntax)
    (fnName : Name)
    (names : Array (Option String)) : CommandElabM (Array TypedLocal) := do
  let valueTys ← unsafe qualifiedFunctionReturnTypes stx fnName
  if names.size != valueTys.size then
    throwErrorAt stx
      s!"tuple destructuring binds {names.size} names, but qualified helper '{qualifiedFunctionDisplayName fnName}' returns {valueTys.size} values"
  for (name?, ty) in names.zip valueTys do
    if let some name := name? then
      requireSupportedLocalBindingType stx s!"local binding '{name}'" ty
  pure <| (names.zip valueTys).filterMap fun (name?, ty) =>
    name?.map (fun name => (name, ty))

private unsafe def qualifiedSingleBindType
    (stx : Syntax)
    (fnName : Name) : CommandElabM ValueType := do
  let valueTys ← unsafe qualifiedFunctionReturnTypes stx fnName
  match valueTys.toList with
  | [] =>
      throwErrorAt stx
        s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns Unit and cannot be bound"
  | [retTy] =>
      pure retTy
  | _ =>
      throwErrorAt stx
        s!"qualified helper '{qualifiedFunctionDisplayName fnName}' returns multiple values; use tuple destructuring"

private def customErrorRequiresDirectParamRef : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .address | .bool | .bytes32 => false
  | .newtype _ baseType => customErrorRequiresDirectParamRef baseType
  | _ => true

private def directParamRefName? (stx : Term) : Option String :=
  match stripParens stx with
  | `(term| $id:ident) => some (toString id.getId)
  | _ => none

private def validateDirectParamCustomErrorArg
    (arg : Term)
    (fnName errorName : String)
    (params : Array ParamDecl)
    (expectedTy : ValueType)
    (argIdx : Nat) : CommandElabM Unit := do
  match directParamRefName? arg with
  | some name =>
      match params.find? (·.name == name) with
      | some param =>
          unless param.ty == expectedTy do
            throwErrorAt arg
              s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' expects direct parameter reference of type {renderValueType expectedTy}, got parameter '{name}' of type {renderValueType param.ty}"
      | none =>
          throwErrorAt arg
            s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' references unknown parameter '{name}' on the compilation-model path"
  | none =>
      throwErrorAt arg
        s!"custom error '{errorName}' arg {argIdx + 1} in function '{fnName}' currently requires direct parameter reference of type {renderValueType expectedTy} on the compilation-model path"

private def validateCustomErrorCall
    (fnName errorName : String)
    (params : Array ParamDecl)
    (errorDecls : Array ErrorDecl)
    (args : Array Term) : CommandElabM Unit := do
  let errorDecl ←
    match errorDecls.find? (·.name == errorName) with
    | some decl => pure decl
    | none => throwError s!"unknown custom error '{errorName}'"
  unless errorDecl.params.size == args.size do
    throwError s!"custom error '{errorName}' expects {errorDecl.params.size} args, got {args.size}"
  for ((expectedTy, arg), argIdx) in errorDecl.params.zip args |>.zipIdx do
    if customErrorRequiresDirectParamRef expectedTy then
      validateDirectParamCustomErrorArg arg fnName errorName params expectedTy argIdx

private def localFunctionAppSyntax?
    (stx : Term) : Option (String × Array Term) :=
  let stx := stripParens stx
  match stx.raw with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ raw _ _ =>
          let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
          some (raw.toString, argTerms)
      | _ => none
  | .ident _ raw _ _ =>
      some (raw.toString, #[])
  | _ => none

private def internalHelperSpecName
    (functions : Array FunctionDecl)
    (fnName : String) : String :=
  Compiler.CompilationModel.pickFreshName
    (Compiler.CompilationModel.internalFunctionPrefix ++ fnName)
    (functions.map (·.name)).toList

private partial def hasDynamicInternalHelperType (ty : ValueType) : Bool :=
  match ty with
  | .string | .bytes | .array _ => true
  | .tuple elemTys => elemTys.any hasDynamicInternalHelperType
  | .struct _ fields => fields.any (fun field => hasDynamicInternalHelperType field.snd)
  | _ => false

private def supportsInternalHelperSpec (fn : FunctionDecl) : Bool :=
  fn.name != "fallback" &&
    fn.name != "receive" &&
    fn.params.all (fun param => !hasDynamicInternalHelperType param.ty) &&
    !hasDynamicInternalHelperType fn.returnTy

private def ensureSupportsInternalHelperSpec
    (stx : Syntax)
    (fn : FunctionDecl) : CommandElabM Unit := do
  unless supportsInternalHelperSpec fn do
    throwErrorAt stx
      s!"helper call '{fn.name}' uses a parameter or return type that direct macro helper lowering does not support yet; only static non-fallback/non-receive helpers can be lowered to internal specs"

private def throwPureContextAccessorError (stx : Syntax) (name : String) : CommandElabM α :=
  throwErrorAt stx
    s!"context accessor '{name}' is monadic; use `let x ← {name}` before using it in a pure expression"

mutual
private partial def leanExprAppFnArgs (expr : Expr) : Expr × Array Expr :=
  let rec go (fn : Expr) (argsRev : Array Expr) : Expr × Array Expr :=
    match fn.consumeMData with
    | .app f arg => go f (argsRev.push arg)
    | other => (other, argsRev.reverse)
  go expr #[]

private partial def leanConstName? (expr : Expr) : Option Name :=
  match expr.consumeMData with
  | .const name _ => some name
  | _ => none

private partial def leanConstNameMatches (expr : Expr) (names : List Name) : Bool :=
  match leanConstName? expr with
  | some name => names.contains name
  | none => false

private partial def leanConstNameMatchesStringOrSuffix
    (expr : Expr)
    (names : List String)
    (suffixes : List String) : Bool :=
  match leanConstName? expr with
  | some name =>
      let nameString := name.toString
      names.contains nameString || suffixes.any (fun suffix => nameString.endsWith s!".{suffix}")
  | none => false

private partial def valueTypeFromLeanTypeExpr? (expr : Expr) : Option ValueType :=
  match expr.consumeMData with
  | .const name _ =>
      let nameString := name.toString
      if nameString == "Verity.Uint256" || nameString == "Verity.Core.Uint256" ||
          nameString.endsWith ".Uint256" then
        some .uint256
      else if nameString == "Verity.Int256" || nameString == "Verity.Core.Int256" ||
          nameString.endsWith ".Int256" then
        some .int256
      else if nameString == "Verity.Address" || nameString == "Verity.Core.Address" ||
          nameString.endsWith ".Address" then
        some .address
      else if nameString == "Bool" then
        some .bool
      else if nameString == "String" then
        some .string
      else if nameString == "ByteArray" then
        some .bytes
      else
        none
  | _ => none

private partial def peelForallTypes (type : Expr) : List Expr × Expr :=
  let rec go (remaining : Expr) (acc : List Expr) : List Expr × Expr :=
    match remaining.consumeMData with
    | .forallE _ domain body _ => go body (domain :: acc)
    | other => (acc.reverse, other)
  go type []

private partial def peelLambdaBody (value : Expr) (arity : Nat) : Option Expr :=
  match arity with
  | 0 => some value
  | n + 1 =>
      match value.consumeMData with
      | .lam _ _ body _ => peelLambdaBody body n
      | _ => none

private partial def leanDefAppSyntax? (stx : Term) : Option (Syntax × String × Array Term) :=
  let stx := stripParens stx
  match stx.raw with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | head@(.ident _ _ raw _) =>
          if isQualifiedFunctionName raw then
            none
          else
            let argTerms := (args.getD 1 Syntax.missing).getArgs.map (fun syn => ⟨syn⟩)
            some (head, raw.toString, argTerms)
      | _ => none
  | _ => none

private partial def resolveLeanDefName? (head : Syntax) : CommandElabM (Option Name) := do
  try
    pure (some (← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo head none))
  catch _ =>
    pure none

private partial def leanDefInfo? (name : Name) : CommandElabM (Option DefinitionVal) := do
  match (← getEnv).find? name with
  | some (.defnInfo info) => pure (some info)
  | _ => pure none

private partial def checkLeanDefCallArgs
    (stx : Syntax)
    (fnDisplay : String)
    (argTerms : Array Term)
    (paramTypeExprs : List Expr)
    (argTypes : Array ValueType) : CommandElabM Unit := do
  unless argTerms.size == paramTypeExprs.length do
    throwErrorAt stx
      s!"Lean helper '{fnDisplay}' expects {paramTypeExprs.length} argument(s), got {argTerms.size}"
  for ((argTerm, argTy), expectedExpr) in argTerms.zip argTypes |>.zip paramTypeExprs.toArray do
    let expectedTy ←
      match valueTypeFromLeanTypeExpr? expectedExpr with
      | some ty => pure ty
      | none =>
          throwErrorAt stx
            s!"Lean helper '{fnDisplay}' uses an unsupported parameter type; supported pure helper parameters are Uint256, Int256, Address, Bytes32/Uint256, Bool, String, and Bytes"
    unless argTy == expectedTy || (isNatLiteralTerm argTerm && numericLiteralCompatibleValueType expectedTy) do
      throwErrorAt argTerm
        s!"Lean helper '{fnDisplay}' argument expects {renderValueType expectedTy}, got {renderValueType argTy}"

private partial def inferLeanDefCallType?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String) : CommandElabM (Option ValueType) := do
  let some (head, fnDisplay, argTerms) := leanDefAppSyntax? stx
    | pure none
  let some fnName ← resolveLeanDefName? head
    | pure none
  let some info ← leanDefInfo? fnName
    | pure none
  let (paramTypeExprs, resultTypeExpr) := peelForallTypes info.type
  let argTypes ← argTerms.mapM
    (inferPureExprType fields constDecls immutableDecls externalDecls params locals · visitingConstants)
  checkLeanDefCallArgs stx.raw fnDisplay argTerms paramTypeExprs argTypes
  match valueTypeFromLeanTypeExpr? resultTypeExpr with
  | some ty =>
      requireSupportedLocalBindingType stx.raw s!"Lean helper '{fnDisplay}' return" ty
      pure (some ty)
  | none =>
      throwErrorAt stx
        s!"Lean helper '{fnDisplay}' uses an unsupported return type; supported pure helper returns are Uint256, Int256, Address, Bytes32/Uint256, and Bool"

private partial def inferPureExprType
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM ValueType := do
  let stx := stripParens stx
  let inferContextAccessorOrLocal (name : String) : CommandElabM ValueType := do
    match locals.findSome? (fun localDecl =>
        if matchesBareName localDecl.fst name then some localDecl.snd else none)
        <|> params.findSome? (fun p =>
          if matchesBareName p.name name then some p.ty else none) with
    | some ty => pure ty
    | none => throwPureContextAccessorError stx name
  if let some (_, index, fieldTy, _, _) := arrayElementStructProjection? params stx then
    requireWordLikeType index "arrayElement index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
    pure fieldTy
  else
  if isParamStructDynamicRootProjection params stx then
    throwStructDynamicRootProjectionError stx
  else
  if isParamStructNonLeafProjection params stx then
    throwStructNonLeafProjectionError stx
  else
  if let some (_, ty) := paramStructProjection? params stx then
    pure ty
  else
  match stx with
  | `(term| true) | `(term| false) => pure .bool
  | `(term| constructorArg $idx:num) =>
      match params[(← natFromSyntax idx)]? with
      | some param => pure param.ty
      | none => throwErrorAt stx s!"constructorArg index {idx.raw.reprint.getD ""} is out of bounds"
  | `(term| Verity.msgSender) =>
      throwPureContextAccessorError stx "msgSender"
  | `(term| Verity.msgValue) =>
      throwPureContextAccessorError stx "msgValue"
  | `(term| Verity.selfBalance) =>
      throwPureContextAccessorError stx "selfBalance"
  | `(term| Verity.blockTimestamp) =>
      throwPureContextAccessorError stx "blockTimestamp"
  | `(term| Verity.blockNumber) =>
      throwPureContextAccessorError stx "blockNumber"
  | `(term| Verity.blobbasefee) =>
      throwPureContextAccessorError stx "blobbasefee"
  | `(term| Verity.chainid) =>
      throwPureContextAccessorError stx "chainid"
  | `(term| Verity.contractAddress) =>
      throwPureContextAccessorError stx "contractAddress"
  | `(term| $id:ident) =>
      let name := toString id.getId
      match params.findSome? (fun p => if p.name == name then some p.ty else none)
          <|> tupleParamElemType? params name
          <|> lookupTypedLocalType? locals name
          <|> immutableDecls.findSome? (fun imm =>
                if declaredNameMatches name imm.name then some imm.ty else none)
          <|> constDecls.findSome? (fun constant =>
                if declaredNameMatches name constant.name then some constant.ty else none) with
      | some ty => pure ty
      | none =>
          if matchesBareName name "calldatasize" || matchesBareName name "returndataSize" then
            pure .uint256
          else if matchesBareName name "zeroAddress" then
            pure .address
          else
            match contextAccessorBareName? name with
            | some accessor => inferContextAccessorOrLocal accessor
            | none => throwErrorAt stx s!"unknown variable '{name}'"
  | `(term| calldatasize) | `(term| returndataSize) =>
      pure .uint256
  | `(term| zeroAddress) =>
      match lookupTypedLocalType? locals "zeroAddress" <|> params.findSome? (fun p =>
        if p.name == "zeroAddress" then some p.ty else none) with
      | some ty => pure ty
      | none => pure .address
  | `(term| isZeroAddress $a:term) =>
      requireWordLikeType a "isZeroAddress" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .bool
  | `(term| wordToAddress $a:term) =>
      requireWordLikeType a "wordToAddress" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .address
  | `(term| addressToWord $a:term) =>
      let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      unless ty == .address do
        throwErrorAt a s!"addressToWord requires Address, got {renderValueType ty}"
      pure .uint256
  | `(term| toInt256 $a:term) => do
      requireWordLikeType a "toInt256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .int256
  | `(term| toUint256 $a:term) => do
      requireWordLikeType a "toUint256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| boolToWord $a:term) =>
      requireBoolType a "boolToWord" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| $n:num) =>
      pure .uint256
  | `(term| add $a $b) | `(term| sub $a $b) | `(term| mul $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      classifyWordArithmeticResultType stx "word arithmetic" lhsTy rhsTy
  | `(term| bitAnd $a $b)
    | `(term| bitOr $a $b) | `(term| bitXor $a $b) | `(term| and $a $b)
    | `(term| or $a $b) | `(term| xor $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "bitwise word arithmetic" lhsTy rhsTy
  | `(term| pow $a $b) | `(term| $a ^ $b)
  | `(term| min $a $b) | `(term| max $a $b) | `(term| wMulDown $a $b) | `(term| wDivUp $a $b)
  | `(term| ceilDiv $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "unsigned word arithmetic" lhsTy rhsTy
  | `(term| div $a $b) | `(term| $a / $b) | `(term| mod $a $b) | `(term| $a % $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      classifyWordArithmeticResultType stx "division/modulo" lhsTy rhsTy
  | `(term| sdiv $a $b) | `(term| smod $a $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      classifyUnsignedWordArithmeticResultType stx "signed builtin arithmetic" lhsTy rhsTy
  | `(term| bitNot $a) | `(term| not $a) => do
      let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      requireWordLikeType a "bitwise not" ty
      pure .uint256
  | `(term| shl $shift $value) | `(term| shr $shift $value) | `(term| sar $shift $value)
    | `(term| signextend $shift $value) => do
      requireWordLikeType shift "shift" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals shift visitingConstants)
      let valueTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value visitingConstants
      requireWordLikeType value "shift" valueTy
      pure .uint256
  | `(term| slt $a $b) | `(term| sgt $a $b) => do
      requireWordLikeType a "signed ordering comparison" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireWordLikeType b "signed ordering comparison" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .bool
  | `(term| $a == $b) | `(term| $a != $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      requireEqComparableTypes stx lhsTy rhsTy
      pure .bool
  | `(term| $a >= $b) | `(term| $a > $b) | `(term| $a < $b) | `(term| $a <= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      discard <| classifyWordArithmeticResultType stx "ordering comparison" lhsTy rhsTy
      pure .bool
  | `(term| $a && $b) | `(term| $a || $b) => do
      requireBoolType a "logical operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireBoolType b "logical operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .bool
  | `(term| logicalAnd $a $b) | `(term| logicalOr $a $b) => do
      requireWordLikeType a "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      requireWordLikeType b "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b visitingConstants)
      pure .uint256
  | `(term| logicalNot $a) => do
      requireWordLikeType a "logical word operator" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .uint256
  | `(term| ! $a) => do
      requireBoolType a "logical not" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a visitingConstants)
      pure .bool
  | `(term| mload $offset) | `(term| tload $offset) | `(term| calldataload $offset)
    | `(term| extcodesize $offset) => do
      requireWordLikeType offset "word offset expression" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset visitingConstants)
      pure .uint256
  | `(term| keccak256 $offset $size) => do
      requireWordLikeType offset "keccak256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset visitingConstants)
      requireWordLikeType size "keccak256" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals size visitingConstants)
      pure .uint256
  | `(term| call $gas $target $value $inOffset $inSize $outOffset $outSize) => do
      for arg in [gas, target, value, inOffset, inSize, outOffset, outSize] do
        requireWordLikeType arg "low-level call" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| staticcall $gas $target $inOffset $inSize $outOffset $outSize)
    | `(term| delegatecall $gas $target $inOffset $inSize $outOffset $outSize) => do
      for arg in [gas, target, inOffset, inSize, outOffset, outSize] do
        requireWordLikeType arg "low-level call" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| arrayLength $name:term) =>
      match lookupNamedValueType? constDecls immutableDecls params locals (← expectStringOrIdent name) with
      | some (.array _) => pure .uint256
      | some ty => throwErrorAt name s!"arrayLength expects an Array value, got {renderValueType ty}"
      | none => throwErrorAt name "unknown array value"
  | `(term| arrayElement $name:term $index:term) => do
      requireWordLikeType index "arrayElement index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index visitingConstants)
      let sourceTy ← requireDirectParamRef name "arrayElement" params
      requireSupportedArrayElementSourceType name "arrayElement" sourceTy
  | `(term| mulDivDown $a $b $c) | `(term| mulDivUp $a $b $c) => do
      for arg in [a, b, c] do
        requireWordLikeType arg "mulDiv" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg visitingConstants)
      pure .uint256
  | `(term| ite $cond $thenVal $elseVal) => do
      requireBoolType cond "ite condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond visitingConstants)
      let thenTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals thenVal visitingConstants
      let elseTy ← inferPureExprType fields constDecls immutableDecls externalDecls params locals elseVal visitingConstants
      requireSameOrWordLikeTypes stx "ite" thenTy elseTy
      pure thenTy
  | `(term| externalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            requireWordLikeType x s!"externalCall '{extName}' argument" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x visitingConstants)
      | _ => throwErrorAt args "expected list literal [..]"
      match externalDecls.find? (fun ext => ext.name == extName) with
      | some ext =>
          match ext.returnTys.toList with
          | [retTy] => pure retTy
          | [] => throwErrorAt name s!"externalCall '{extName}' returns no values; use `let success ← tryExternalCall \"{extName}\" [...]` instead"
          | _ => throwErrorAt name s!"externalCall '{extName}' returns {ext.returnTys.size} values; use `let (success, ...) ← tryExternalCall \"{extName}\" [...]` for multi-return"
      | none => pure .uint256
  | `(term| structMember $field:term $key:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      requireWordLikeType key "structMember key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key visitingConstants)
      pure .uint256
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      requireWordLikeType key1 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1 visitingConstants)
      requireWordLikeType key2 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2 visitingConstants)
      pure .uint256
  | _ =>
      match qualifiedFunctionAppSyntax? stx with
      | some (fnName, _) =>
          if (nameComponents fnName).head? == some "Verity" then
            throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"
          else
            throwErrorAt stx
              s!"qualified library helper call '{qualifiedFunctionDisplayName fnName}' is only supported as a monadic bind source; use `let x ← {qualifiedFunctionDisplayName fnName} ...` or tuple destructuring bind syntax"
      | none =>
          match ← inferLeanDefCallType? fields constDecls immutableDecls externalDecls params locals stx visitingConstants with
          | some ty => pure ty
          | none => throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"

private partial def lookupNamedValueType?
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (name : String) : Option ValueType :=
  params.findSome? (fun p => if p.name == name then some p.ty else none)
    <|> lookupTypedLocalType? locals name
    <|> immutableDecls.findSome? (fun imm => if imm.name == name then some imm.ty else none)
    <|> constDecls.findSome? (fun constant => if constant.name == name then some constant.ty else none)

private partial def inferBindSourceType
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM ValueType := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 => pure .uint256
      | .scalar .int256 => pure .int256
      | .scalar (.newtype ntName (.uint256)) => pure (.newtype ntName .uint256)
      | .scalar (.adt name maxFields) => pure (.adt name maxFields)
      | .scalar (.newtype _ (.address)) => throwErrorAt rhs s!"field '{f.name}' is Address-based newtype; use getStorageAddr"
      | .scalar .address => throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; encode as Uint256 and use getStorage"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address => pure .address
      | .scalar (.newtype ntName (.address)) => pure (.newtype ntName .address)
      | .scalar (.newtype _ (.uint256)) => throwErrorAt rhs s!"field '{f.name}' is Uint256-based newtype; use getStorage"
      | .scalar .uint256 => throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; use getStorage"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageArrayLength $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ => pure .uint256
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getStorageArrayElement $field:ident $index:term) => do
      requireWordLikeType index "storage array index" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray .uint256 => pure .uint256
      | .dynamicArray .address => pure .address
      | .dynamicArray .bool => pure .bool
      | .dynamicArray .uint8 => pure .uint8
      | .dynamicArray .bytes32 => pure .bytes32
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getMapping $field:ident $key:term) | `(term| getMappingUint $field:ident $key:term)
    | `(term| getMappingWord $field:ident $key:term $_wordOffset:num) => do
      requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 => pure .uint256
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingAddr $field:ident $key:term) | `(term| getMappingUintAddr $field:ident $key:term) => do
      requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 => pure .address
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) => do
      requireWordLikeType key1 "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
      requireWordLikeType key2 "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 => pure .uint256
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| getMappingN $field:ident $keys:term) => do
      let keyTerms ← expectMappingKeyTerms keys
      for key in keyTerms do
        requireWordLikeType key "mapping key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      let f ← lookupStorageField fields (toString field.getId)
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size == keyTypes.length then
            pure .uint256
          else
            throwErrorAt rhs s!"field '{f.name}' expects {keyTypes.length} mapping keys, but getMappingN received {keyTerms.size}"
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
          | _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| structMember $field:term $key:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      requireWordLikeType key "structMember key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
      pure .uint256
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) => do
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      requireWordLikeType key1 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
      requireWordLikeType key2 "structMember2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
      pure .uint256
  | `(term| msgSender) | `(term| Verity.msgSender) =>
      pure .address
  | `(term| msgValue) | `(term| Verity.msgValue) | `(term| selfBalance)
    | `(term| Verity.selfBalance) | `(term| blockTimestamp)
    | `(term| Verity.blockTimestamp) | `(term| blockNumber) | `(term| Verity.blockNumber)
    | `(term| blobbasefee) | `(term| Verity.blobbasefee) | `(term| chainid)
    | `(term| Verity.chainid) =>
      pure .uint256
  | `(term| contractAddress) | `(term| Verity.contractAddress) =>
      pure .address
  | `(term| tload $offset:term) => do
      requireWordLikeType offset "tload offset" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset)
      pure .uint256
  | `(term| ecrecover $hash:term $v:term $r:term $s:term) => do
      for arg in [hash, v, r, s] do
        requireWordLikeType arg "ecrecover" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .address
  | `(term| balanceOf $token:term $owner:term) =>
      for arg in [token, owner] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .uint256
  | `(term| allowance $token:term $owner:term $spender:term) =>
      for arg in [token, owner, spender] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
      pure .uint256
  | `(term| totalSupply $token:term) => do
      requireWordLikeType token "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals token)
      pure .uint256
  | `(term| ecmCall $_moduleFactory:term $args:term) => do
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            requireWordLikeType x "ECM argument"
              (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
      | _ => throwErrorAt args "expected list literal [..]"
      pure .uint256
  | `(term| tryExternalCall $name:term $args:term) => do
      let extName := ← expectStringOrIdent name
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            requireWordLikeType x s!"tryExternalCall '{extName}' argument"
              (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
      | _ => throwErrorAt args "expected list literal [..]"
      match externalDecls.find? (fun ext => ext.name == extName) with
      | some ext =>
          if ext.returnTys.size > 0 then
            throwErrorAt rhs s!"tryExternalCall '{extName}' returns {ext.returnTys.size} value(s); use tuple destructuring: `let (success, ...) ← tryExternalCall ...`"
          -- Zero-return external: success flag only
          pure .bool
      | none =>
          throwErrorAt rhs s!"unknown external function '{extName}'"
  | `(term| requireSomeUint $optExpr:term $_msg:term) =>
      match stripParens optExpr with
      | `(term| safeAdd $a:term $b:term)
      | `(term| safeSub $a:term $b:term)
      | `(term| safeMul $a:term $b:term)
      | `(term| safeDiv $a:term $b:term) => do
          requireWordLikeType a "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals a)
          requireWordLikeType b "safe uint helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals b)
          pure .uint256
      | _ => throwErrorAt rhs "unsupported requireSomeUint source; expected safeAdd, safeSub, safeMul, or safeDiv"
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
      | some (fn, _argTerms) =>
          ensureSupportsInternalHelperSpec rhs fn
          match fn.returnTy with
          | .tuple _ =>
              throwErrorAt rhs
                s!"helper call '{fn.name}' returns multiple values; use tuple destructuring"
          | .unit =>
              throwErrorAt rhs
                s!"helper call '{fn.name}' returns Unit and cannot be bound"
          | retTy =>
              pure retTy
      | none =>
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              unsafe qualifiedSingleBindType rhs.raw qualifiedName
          | none =>
              throwErrorAt rhs
                "unsupported bind source; expected getStorage/getStorageAddr/getStorageArrayLength/getStorageArrayElement/getMapping/getMappingAddr/getMappingUint/getMappingUintAddr/getMappingWord/getMapping2/getMappingN/structMember/structMember2/msgSender/msgValue/selfBalance/tload/ecrecover/ecmCall, a direct internal helper call, or a qualified library helper call"

private partial def inferTupleSourceTypes?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array ValueType)) := do
  match tupleElemsFromTerm? rhs with
  | some elems =>
      pure <| some (← elems.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals))
  | none =>
      match stripParens rhs with
      | `(term| $id:ident) =>
          match params.find? (fun p => p.name == toString id.getId) with
          | some p =>
              match p.ty with
              | .tuple elemTys => pure (some elemTys.toArray)
              | _ => pure none
          | none => pure none
      | `(term| structMembers $field:term $key:term $members:term) => do
          let fieldName := ← expectStringOrIdent field
          let memberNames := ← expectStringList members
          for memberName in memberNames do
            let _ ← lookupStructMemberDecl fields fieldName memberName false
          requireWordLikeType key "structMembers key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key)
          pure (some (Array.replicate memberNames.size .uint256))
      | `(term| structMembers2 $field:term $key1:term $key2:term $members:term) => do
          let fieldName := ← expectStringOrIdent field
          let memberNames := ← expectStringList members
          for memberName in memberNames do
            let _ ← lookupStructMemberDecl fields fieldName memberName true
          requireWordLikeType key1 "structMembers2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1)
          requireWordLikeType key2 "structMembers2 key" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2)
          pure (some (Array.replicate memberNames.size .uint256))
      | `(term| arrayElement $name:term $index:term) => do
          requireWordLikeType index "arrayElement index"
            (← inferPureExprType fields constDecls immutableDecls externalDecls params locals index)
          let sourceTy ← requireDirectParamRef name "arrayElement" params
          match sourceTy with
          | .array (.tuple elemTys) =>
              let _ ← requireSupportedArrayElementTupleSourceType name "arrayElement tuple destructuring" sourceTy
              pure (some elemTys.toArray)
          | _ => pure none
      | `(term| tryExternalCall $name:term $args:term) =>
          let extName := ← expectStringOrIdent name
          match stripParens args with
          | `(term| [ $[$xs],* ]) =>
              for x in xs do
                requireWordLikeType x s!"tryExternalCall '{extName}' argument"
                  (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
          | _ => throwErrorAt args "expected list literal [..]"
          match externalDecls.find? (fun ext => ext.name == extName) with
          | some ext =>
              -- tryExternalCall returns (success : Bool, result₁ : T₁, ..., resultₙ : Tₙ)
              pure (some (#[.bool] ++ ext.returnTys))
          | none =>
              -- When called from translation path with empty externalDecls, return none
              -- to let the tryExternalCallBindStmt? helper handle translation.
              -- The validation path (with real externalDecls) catches actual errors.
              pure none
      | other =>
          match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals other with
          | some (fn, _argTerms) =>
              ensureSupportsInternalHelperSpec rhs fn
              match fn.returnTy with
              | .tuple elemTys => pure (some elemTys.toArray)
              | _ => pure none
          | none => pure none

private partial def resolveLocalFunctionApp?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (FunctionDecl × Array Term)) := do
  let some (fnName, argTerms) := localFunctionAppSyntax? stx
    | pure none
  let candidates := functions.filter (fun fn => fn.name == fnName && fn.params.size == argTerms.size)
  if candidates.isEmpty then
    pure none
  else
    let argTypes ← argTerms.mapM (inferPureExprType fields constDecls immutableDecls externalDecls params locals)
    let exactMatchedFns := candidates.filter (fun fn =>
      fn.params.map (fun param => param.ty) == argTypes)
    let literalCompatibleFns :=
      if exactMatchedFns.isEmpty then
        candidates.filter (fun fn => argumentTypesMatchParams argTerms argTypes fn.params)
      else
        exactMatchedFns
    match literalCompatibleFns.toList with
    | [fn] => pure (some (fn, argTerms))
    | [] =>
        let expected :=
          String.intercalate ", "
            (candidates.toList.map functionSignatureKey)
        let actual :=
          fnName ++ "(" ++ String.intercalate "," (argTypes.toList.map renderValueType) ++ ")"
        throwErrorAt stx
          s!"no overload of '{fnName}' matches argument types {actual}; candidates: {expected}"
    | _ =>
        throwErrorAt stx
          s!"ambiguous overload resolution for '{fnName}'"

private partial def resolveQualifiedFunctionApp?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Option (Name × Array Term)) := do
  let some (fnName, argTerms) := qualifiedFunctionAppSyntax? stx
    | pure none
  if (nameComponents fnName).head? == some "Verity" then
    pure none
  else
    for arg in argTerms do
      requireWordLikeType arg s!"qualified helper '{qualifiedFunctionDisplayName fnName}' argument"
        (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
    pure (some (fnName, argTerms))
end

mutual
private partial def validateConstantBody
    (constDecls : Array ConstantDecl)
    (stx : Term)
    (visiting : List String := []) : CommandElabM Unit := do
  let stx := stripParens stx
  match stx with
  | `(term| true) => pure ()
  | `(term| false) => pure ()
  | `(term| constructorArg $idx:num) => throwNonCompileTimeConstantError idx "constructorArg"
  | `(term| msgValue) => throwNonCompileTimeConstantError stx "msgValue"
  | `(term| selfBalance) => throwNonCompileTimeConstantError stx "selfBalance"
  | `(term| blockTimestamp) => throwNonCompileTimeConstantError stx "blockTimestamp"
  | `(term| blockNumber) => throwNonCompileTimeConstantError stx "blockNumber"
  | `(term| blobbasefee) | `(term| Verity.blobbasefee) =>
      throwNonCompileTimeConstantError stx "blobbasefee"
  | `(term| contractAddress) => throwNonCompileTimeConstantError stx "contractAddress"
  | `(term| chainid) => throwNonCompileTimeConstantError stx "chainid"
  | `(term| calldatasize) => throwNonCompileTimeConstantError stx "calldatasize"
  | `(term| returndataSize) => throwNonCompileTimeConstantError stx "returndataSize"
  | `(term| zeroAddress) => pure ()
  | `(term| isZeroAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| wordToAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| addressToWord $a:term) => validateConstantBody constDecls a visiting
  | `(term| toInt256 $a:term) => validateConstantBody constDecls a visiting
  | `(term| toUint256 $a:term) => validateConstantBody constDecls a visiting
  | `(term| boolToWord $a:term) => validateConstantBody constDecls a visiting
  | `(term| $id:ident) =>
      let name := toString id.getId
      match constDecls.find? (fun c => c.name == name) with
      | none => throwErrorAt stx s!"unknown variable '{name}'"
      | some constant =>
          if visiting.contains name then
            throwErrorAt stx s!"constant '{name}' depends on itself recursively"
          validateConstantBody constDecls constant.body (name :: visiting)
  | `(term| $n:num) => pure ()
  | `(term| add $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sub $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| mul $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| div $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sdiv $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| mod $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| smod $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitAnd $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitOr $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitXor $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| bitNot $a) => validateConstantBody constDecls a visiting
  | `(term| shl $shift $value) => validateConstantBody constDecls shift visiting *> validateConstantBody constDecls value visiting
  | `(term| shr $shift $value) => validateConstantBody constDecls shift visiting *> validateConstantBody constDecls value visiting
  | `(term| $a == $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a != $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a >= $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a > $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a < $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a <= $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a && $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| $a || $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalAnd $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalOr $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| logicalNot $a) => validateConstantBody constDecls a visiting
  | `(term| and $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| or $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| xor $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| not $a) => validateConstantBody constDecls a visiting
  | `(term| mload $offset) => throwNonCompileTimeConstantError offset "mload"
  | `(term| tload $offset) => throwNonCompileTimeConstantError offset "tload"
  | `(term| calldataload $offset) => throwNonCompileTimeConstantError offset "calldataload"
  | `(term| extcodesize $addr) => throwNonCompileTimeConstantError addr "extcodesize"
  | `(term| keccak256 $offset $_size) => throwNonCompileTimeConstantError offset "keccak256"
  | `(term| call $gas $_target $_value $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "call"
  | `(term| staticcall $gas $_target $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "staticcall"
  | `(term| delegatecall $gas $_target $_inOffset $_inSize $_outOffset $_outSize) =>
      throwNonCompileTimeConstantError gas "delegatecall"
  | `(term| byte $index $word) => validateConstantBody constDecls index visiting *> validateConstantBody constDecls word visiting
  | `(term| addmod $a $b $c) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting *> validateConstantBody constDecls c visiting
  | `(term| mulmod $a $b $c) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting *> validateConstantBody constDecls c visiting
  | `(term| signextend $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sar $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| slt $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| sgt $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| min $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| max $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| ceilDiv $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| ite $cond $thenVal $elseVal) =>
      validateConstantBody constDecls cond visiting *>
      validateConstantBody constDecls thenVal visiting *>
      validateConstantBody constDecls elseVal visiting
  | _ => throwErrorAt stx "unsupported expression in contract constant"

private partial def translateConstantExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (visiting : List String)
    (name : String) : CommandElabM Term := do
  match constDecls.find? (fun c => c.name == name) with
  | none => throwError s!"unknown variable '{name}'"
  | some constant =>
      if visiting.contains name then
        throwError s!"constant '{name}' depends on itself recursively"
      translatePureExprWithTypes fields constDecls immutableDecls #[] #[] constant.body (name :: visiting)

private partial def translateLeanExprFromDef
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (origin : Syntax)
    (fnDisplay : String)
    (argExprs : Array Term)
    (expr : Expr) : CommandElabM Term := do
  match expr.consumeMData with
  | .bvar idx =>
      if idx < argExprs.size then
        let argIdx := argExprs.size - 1 - idx
        match argExprs[argIdx]? with
        | some arg => pure arg
        | none => throwErrorAt origin s!"Lean helper '{fnDisplay}' body references an out-of-scope argument"
      else
        throwErrorAt origin s!"Lean helper '{fnDisplay}' body references an out-of-scope argument"
  | .lit (.natVal n) =>
      `(Compiler.CompilationModel.Expr.literal $(natTerm n))
  | .const ``Bool.true _ =>
      `(Compiler.CompilationModel.Expr.literal 1)
  | .const ``Bool.false _ =>
      `(Compiler.CompilationModel.Expr.literal 0)
  | other =>
      let (fn, args) := leanExprAppFnArgs other
      if leanConstNameMatches fn [``OfNat.ofNat] then
        match args.toList with
        | [_ty, .lit (.natVal n), _inst] =>
            `(Compiler.CompilationModel.Expr.literal $(natTerm n))
        | _ =>
            throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported numeric literal form"
      else if leanConstNameMatches fn [``ite] then
        match args.toList with
        | [_ty, cond, _dec, thenExpr, elseExpr] =>
            `(Compiler.CompilationModel.Expr.ite
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs cond)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs thenExpr)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs elseExpr))
        | _ =>
            throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported if/ite form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.toInt256", "Verity.toUint256", "Verity.wordToAddress", "Verity.addressToWord"]
          ["toInt256", "toUint256", "wordToAddress", "addressToWord"] then
        match args.toList with
        | [arg] => translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs arg
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported cast form"
      else if leanConstNameMatches fn [``Neg.neg] then
        match args.toList with
        | [_ty, _inst, arg] =>
            `(Compiler.CompilationModel.Expr.sub
                (Compiler.CompilationModel.Expr.literal 0)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs arg))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported negation form"
      else if leanConstNameMatches fn [``Eq] then
        match args.toList with
        | [_tyExpr, lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.eq
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported equality form"
      else if leanConstNameMatches fn [``LT.lt, ``LE.le] then
        match args.toList with
        | [tyExpr, _inst, lhs, rhs] =>
            let lhsExpr ← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs
            let rhsExpr ← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs
            match leanConstName? fn with
            | some ``LT.lt =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.slt $lhsExpr $rhsExpr)
                else
                  `(Compiler.CompilationModel.Expr.lt $lhsExpr $rhsExpr)
            | _ =>
                if valueTypeFromLeanTypeExpr? tyExpr == some .int256 then
                  `(Compiler.CompilationModel.Expr.logicalNot
                      (Compiler.CompilationModel.Expr.sgt $lhsExpr $rhsExpr))
                else
                  `(Compiler.CompilationModel.Expr.le $lhsExpr $rhsExpr)
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported comparison form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.add", "Verity.EVM.Int256.add",
           "Verity.Core.Uint256.add", "Verity.Core.Int256.add"]
          ["add"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.add
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported add form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.sub", "Verity.EVM.Int256.sub",
           "Verity.Core.Uint256.sub", "Verity.Core.Int256.sub"]
          ["sub"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.sub
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported sub form"
      else if leanConstNameMatchesStringOrSuffix fn
          ["Verity.EVM.Uint256.mul", "Verity.EVM.Int256.mul",
           "Verity.Core.Uint256.mul", "Verity.Core.Int256.mul"]
          ["mul"] then
        match args.toList with
        | [lhs, rhs] =>
            `(Compiler.CompilationModel.Expr.mul
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs lhs)
                $(← translateLeanExprFromDef fields constDecls immutableDecls params locals origin fnDisplay argExprs rhs))
        | _ => throwErrorAt origin s!"Lean helper '{fnDisplay}' contains an unsupported mul form"
      else
        throwErrorAt origin
          s!"Lean helper '{fnDisplay}' body contains unsupported expression '{fn}'; inline it or rewrite the helper using supported pure Verity operations"

private partial def translateLeanDefCall?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String) : CommandElabM (Option Term) := do
  let some (head, fnDisplay, argTerms) := leanDefAppSyntax? stx
    | pure none
  let some fnName ← resolveLeanDefName? head
    | pure none
  let some info ← leanDefInfo? fnName
    | pure none
  let (paramTypeExprs, resultTypeExpr) := peelForallTypes info.type
  let argTypes ← argTerms.mapM
    (inferPureExprType fields constDecls immutableDecls externalDecls params locals · visitingConstants)
  checkLeanDefCallArgs stx.raw fnDisplay argTerms paramTypeExprs argTypes
  match valueTypeFromLeanTypeExpr? resultTypeExpr with
  | some ty => requireSupportedLocalBindingType stx.raw s!"Lean helper '{fnDisplay}' return" ty
  | none =>
      throwErrorAt stx
        s!"Lean helper '{fnDisplay}' uses an unsupported return type; supported pure helper returns are Uint256, Int256, Address, Bytes32/Uint256, and Bool"
  let some body := peelLambdaBody info.value argTerms.size
    | throwErrorAt stx s!"Lean helper '{fnDisplay}' body is not a transparent function definition"
  let argExprs ← argTerms.mapM
    (translatePureExprWithTypes fields constDecls immutableDecls params locals · visitingConstants)
  pure (some (← translateLeanExprFromDef fields constDecls immutableDecls params locals stx.raw fnDisplay argExprs body))

partial def translatePureExprWithTypes
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM Term := do
  let stx := stripParens stx
  let localNames := typedLocalNames locals
  if let some (paramName, index, _fieldTy, elemTy, wordOffset) := arrayElementStructProjection? params stx then
    let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants
    if valueTypeUsesDynamicData elemTy then
      `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm wordOffset))
    else
      let elementWords ←
        match staticAbiWordCount? elemTy with
        | some n => pure n
        | none => throwErrorAt stx "arrayElement struct projection requires a static or dynamic ABI-decodable element"
      `(Compiler.CompilationModel.Expr.arrayElementWord
        $(strTerm paramName)
        $indexExpr
        $(natTerm elementWords)
        $(natTerm wordOffset))
  else
  if isParamStructDynamicRootProjection params stx then
    throwStructDynamicRootProjectionError stx
  else
  if isParamStructNonLeafProjection params stx then
    throwStructNonLeafProjectionError stx
  else
  if let some (paramName, _ty) := paramStructProjection? params stx then
    `(Compiler.CompilationModel.Expr.param $(strTerm paramName))
  else
  match stx with
  | `(term| true) => `(Compiler.CompilationModel.Expr.literal 1)
  | `(term| false) => `(Compiler.CompilationModel.Expr.literal 0)
  | `(term| constructorArg $idx:num) =>
      `(Compiler.CompilationModel.Expr.constructorArg $idx)
  | `(term| Verity.msgSender) =>
      throwPureContextAccessorError stx "msgSender"
  | `(term| Verity.msgValue) =>
      throwPureContextAccessorError stx "msgValue"
  | `(term| Verity.selfBalance) =>
      throwPureContextAccessorError stx "selfBalance"
  | `(term| Verity.blockTimestamp) =>
      throwPureContextAccessorError stx "blockTimestamp"
  | `(term| Verity.blockNumber) =>
      throwPureContextAccessorError stx "blockNumber"
  | `(term| Verity.blobbasefee) =>
      throwPureContextAccessorError stx "blobbasefee"
  | `(term| Verity.contractAddress) =>
      throwPureContextAccessorError stx "contractAddress"
  | `(term| Verity.chainid) =>
      throwPureContextAccessorError stx "chainid"
  | `(term| $id:ident) =>
      let name := toString id.getId
      if params.any (fun p => p.name == name) || isTupleComponentRef params name || localNames.contains name then
        lookupVarExpr params localNames name
      else if let some actualName := findContextAccessorShadowName? params localNames name then
        lookupVarExpr params localNames actualName
      else if matchesBareName name "calldatasize" then
        `(Compiler.CompilationModel.Expr.calldatasize)
      else if matchesBareName name "returndataSize" then
        `(Compiler.CompilationModel.Expr.returndataSize)
      else if matchesBareName name "zeroAddress" then
        `(Compiler.CompilationModel.Expr.literal 0)
      else if let some imm := immutableDecls.find? (fun imm => declaredNameMatches name imm.name) then
        match imm.ty with
        | .uint256 | .int256 | .uint8 | .bytes32 | .bool =>
            `(Compiler.CompilationModel.Expr.storage $(strTerm (immutableHiddenName imm)))
        | .address => `(Compiler.CompilationModel.Expr.storageAddr $(strTerm (immutableHiddenName imm)))
        | _ => throwErrorAt stx s!"immutable '{name}' uses unsupported type"
      else if let some constant := constDecls.find? (fun constant => declaredNameMatches name constant.name) then
        translateConstantExpr fields constDecls immutableDecls visitingConstants constant.name
      else if let some accessor := contextAccessorBareName? name then
        throwPureContextAccessorError stx accessor
      else
        translateConstantExpr fields constDecls immutableDecls visitingConstants name
  | `(term| calldatasize) => `(Compiler.CompilationModel.Expr.calldatasize)
  | `(term| returndataSize) => `(Compiler.CompilationModel.Expr.returndataSize)
  | `(term| zeroAddress) =>
      if params.any (fun p => p.name == "zeroAddress") || localNames.contains "zeroAddress" then
        lookupVarExpr params localNames "zeroAddress"
      else
        `(Compiler.CompilationModel.Expr.literal 0)
  | `(term| isZeroAddress $a:term) =>
      `(Compiler.CompilationModel.Expr.eq
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| wordToAddress $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| addressToWord $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| toInt256 $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| toUint256 $a:term) => translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants
  | `(term| boolToWord $a:term) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 1)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| $n:num) => `(Compiler.CompilationModel.Expr.literal $n)
  | `(term| add $a $b) => `(Compiler.CompilationModel.Expr.add $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sub $a $b) => `(Compiler.CompilationModel.Expr.sub $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mul $a $b) => `(Compiler.CompilationModel.Expr.mul $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| pow $a $b) | `(term| $a ^ $b) =>
      `(Compiler.CompilationModel.Expr.externalCall Compiler.CompilationModel.builtinExpName
          [$(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants),
           $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)])
  | `(term| div $a $b) | `(term| $a / $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.sdiv $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.div $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sdiv $a $b) => `(Compiler.CompilationModel.Expr.sdiv $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mod $a $b) | `(term| $a % $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.smod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.mod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| smod $a $b) => `(Compiler.CompilationModel.Expr.smod $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitAnd $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitOr $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitXor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitNot $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| shl $shift $value) => `(Compiler.CompilationModel.Expr.shl $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| shr $shift $value) => `(Compiler.CompilationModel.Expr.shr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| sar $shift $value) => `(Compiler.CompilationModel.Expr.sar $(← translatePureExprWithTypes fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| signextend $byteIndex $value) => `(Compiler.CompilationModel.Expr.signextend $(← translatePureExprWithTypes fields constDecls immutableDecls params locals byteIndex visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| $a == $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      if (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes) then
        let (lhsName, rhsName) ← dynamicEqParamNames stx params a b lhsTy rhsTy
        `(Compiler.CompilationModel.Expr.dynamicBytesEq $(strTerm lhsName) $(strTerm rhsName))
      else
        `(Compiler.CompilationModel.Expr.eq
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a != $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      if (lhsTy == .string && rhsTy == .string) || (lhsTy == .bytes && rhsTy == .bytes) then
        let (lhsName, rhsName) ← dynamicEqParamNames stx params a b lhsTy rhsTy
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.dynamicBytesEq $(strTerm lhsName) $(strTerm rhsName)))
      else
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.eq
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)))
  | `(term| $a >= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.slt
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)))
      else
        `(Compiler.CompilationModel.Expr.ge $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a > $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.sgt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.gt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sgt $a $b) => `(Compiler.CompilationModel.Expr.sgt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a < $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.slt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
      else
        `(Compiler.CompilationModel.Expr.lt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| slt $a $b) => `(Compiler.CompilationModel.Expr.slt $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a <= $b) => do
      let lhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals a visitingConstants
      let rhsTy ← inferPureExprType fields constDecls immutableDecls #[] params locals b visitingConstants
      let (lhsTy, rhsTy) := preferSignedNumericLiteralPeer a b lhsTy rhsTy
      if lhsTy == .int256 && rhsTy == .int256 then
        `(Compiler.CompilationModel.Expr.logicalNot
            (Compiler.CompilationModel.Expr.sgt
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)))
      else
        `(Compiler.CompilationModel.Expr.le $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a && $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a || $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalAnd $a $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalOr $a $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalNot $a) => `(Compiler.CompilationModel.Expr.logicalNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| and $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| or $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| xor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| not $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| mload $offset) =>
      `(Compiler.CompilationModel.Expr.mload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| tload $offset) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| calldataload $offset) =>
      `(Compiler.CompilationModel.Expr.calldataload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| extcodesize $addr) =>
      `(Compiler.CompilationModel.Expr.extcodesize
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals addr visitingConstants))
  | `(term| keccak256 $offset $size) =>
      `(Compiler.CompilationModel.Expr.keccak256
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size visitingConstants))
  | `(term| call $gas $target $value $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.call
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| staticcall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.staticcall
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| delegatecall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.delegatecall
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| arrayLength $name:term) =>
      `(Compiler.CompilationModel.Expr.arrayLength $(strTerm (← expectStringOrIdent name)))
  | `(term| arrayElement $name:term $index:term) =>
      `(Compiler.CompilationModel.Expr.arrayElement
          $(strTerm (← expectStringOrIdent name))
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index visitingConstants))
  | `(term| ceilDiv $a $b) =>
      `(Compiler.CompilationModel.Expr.ceilDiv
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mulDivDown $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivDown
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| mulDivUp $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivUp
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| wMulDown $a $b) =>
      `(Compiler.CompilationModel.Expr.wMulDown
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| wDivUp $a $b) =>
      `(Compiler.CompilationModel.Expr.wDivUp
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| min $a $b) => `(Compiler.CompilationModel.Expr.min $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| max $a $b) => `(Compiler.CompilationModel.Expr.max $(← translatePureExprWithTypes fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| ite $cond $thenVal $elseVal) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals thenVal visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals elseVal visitingConstants))
  | `(term| externalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argsExprs ←
        match stripParens args with
        | `(term| [ $[$xs],* ]) => xs.mapM (fun x => translatePureExprWithTypes fields constDecls immutableDecls params locals x visitingConstants)
        | _ => throwErrorAt args "expected list literal [..]"
      `(Compiler.CompilationModel.Expr.externalCall $(strTerm extName) [ $[$argsExprs],* ])
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key visitingConstants)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1 visitingConstants)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2 visitingConstants)
          $(strTerm memberName))
  | _ =>
      match ← translateLeanDefCall? fields constDecls immutableDecls #[] params locals stx visitingConstants with
      | some expr => pure expr
      | none => throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"
end

partial def translatePureExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM Term :=
  translatePureExprWithTypes fields constDecls immutableDecls params
    (locals.map (fun name => (name, .uint256))) stx visitingConstants

private def validateWordLikeExprListLiteral
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (args : Term)
    (context : String) : CommandElabM Unit := do
  match stripParens args with
  | `(term| [ $[$xs],* ]) =>
      for x in xs do
        requireWordLikeType x context
          (← inferPureExprType fields constDecls immutableDecls externalDecls params locals x)
  | _ => throwErrorAt args "expected list literal [..]"

private partial def syntaxMentionsIdent (stx : Syntax) (name : String) : Bool :=
  match stx with
  | .ident _ raw _ _ => raw.toString == name
  | .node _ _ args => args.any (fun child => syntaxMentionsIdent child name)
  | _ => false

private def freshSyntheticLocalName
    (base : String)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String) : String :=
  let used :=
    ((params.map (·.name)) ++ typedLocalNames locals ++ mutableLocals).toList
  let rec go (remaining : Nat) (suffix : Nat) : String :=
    let candidate :=
      if suffix == 0 then base else s!"{base}_{suffix}"
    if !(used.contains candidate) then
      candidate
    else
      match remaining with
      | 0 => s!"{base}_fresh"
      | n + 1 => go n (suffix + 1)
  go used.length 0

private def parseTryCatchHandler
    (handler : Term) : CommandElabM (Option String × Array (TSyntax `doElem)) := do
  match stripParens handler with
  | `(term| fun $name:ident => do $[$elems:doElem]*) =>
      pure (some (toString name.getId), elems)
  | `(term| do $[$elems:doElem]*) =>
      pure (none, elems)
  | _ =>
      throwErrorAt handler
        "tryCatch handler must be `fun _ => do ...` or a direct `do ...` block"

private def validateTryCatchHandlerDoesNotUsePayload
    (handler : Term)
    (payloadName? : Option String)
    (elems : Array (TSyntax `doElem)) : CommandElabM Unit := do
  match payloadName? with
  | none => pure ()
  | some payloadName =>
      if elems.any (fun elem => syntaxMentionsIdent elem.raw payloadName) then
        throwErrorAt handler
          s!"tryCatch catch payload '{payloadName}' is not available on the compilation-model path yet; use `_`/ignore it and read returndata explicitly if needed"

private unsafe def evalExternalCallModuleTerm
    (moduleTerm : Term) : CommandElabM Compiler.ECM.ExternalCallModule := do
  liftTermElabM do
    let expectedType := mkConst ``Compiler.ECM.ExternalCallModule
    let expr ← Lean.Elab.Term.elabTermEnsuringType moduleTerm expectedType
    Lean.Meta.evalExpr Compiler.ECM.ExternalCallModule expectedType expr .unsafe

private def validateEffectOnlyEcmModuleTerm
    (moduleTerm : Term) : CommandElabM Unit := do
  let mod ← unsafe evalExternalCallModuleTerm moduleTerm
  if !mod.resultVars.isEmpty then
    throwErrorAt moduleTerm
      s!"ecmDo requires an effect-only ECM module, but '{mod.name}' binds {mod.resultVars.length} result value(s)"

private def validateSingleResultEcmModuleTerm
    (moduleTerm : Term)
    (boundVarName : String) : CommandElabM Unit := do
  let mod ← unsafe evalExternalCallModuleTerm moduleTerm
  if mod.resultVars != [boundVarName] then
    throwErrorAt moduleTerm
      s!"ecmCall must elaborate to an ECM module binding exactly ['{boundVarName}'], but '{mod.name}' binds {repr mod.resultVars}"

private def arrayElementTupleElemExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          let elementWords ←
            match staticAbiWordCount? (.tuple elemTys) with
            | some n => pure n
            | none =>
                throwErrorAt rhs
                  "arrayElement tuple destructuring requires a static ABI-word tuple element type"
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let mut offset := 0
          let mut exprs : Array Term := #[]
          for elemTy in elemTys do
            let elemWords ←
              match staticAbiWordCount? elemTy with
              | some n => pure n
              | none =>
                  throwErrorAt rhs
                    "arrayElement tuple destructuring requires static ABI-word tuple members"
            if elemWords != 1 then
              throwErrorAt rhs
                "arrayElement tuple destructuring currently supports top-level single-word tuple members"
            exprs := exprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexExpr
              $(natTerm elementWords)
              $(natTerm offset)))
            offset := offset + elemWords
          pure (some exprs)
      | _ => pure none
  | _ => pure none

private def arrayElementTupleDestructureStmts?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option (Array Term × TypedLocal)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          if names.size != elemTys.length then
            throwErrorAt rhs
              s!"tuple destructuring binds {names.size} names, but the source provides {elemTys.length} values"
          let syntheticUsed := mutableLocals ++ names.filterMap id
          let indexName := freshSyntheticLocalName "arrayElement_index" params locals syntheticUsed
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let indexStmt ←
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm indexName) $indexExpr)
          let indexLocal ←
            `(Compiler.CompilationModel.Expr.localVar $(strTerm indexName))
          let mut offset := 0
          let mut valueExprs : Array Term := #[]
          match staticAbiWordCount? (.tuple elemTys) with
          | some elementWords =>
              for elemTy in elemTys do
                let elemWords ←
                  match staticAbiWordCount? elemTy with
                  | some n => pure n
                  | none =>
                      throwErrorAt rhs
                        "arrayElement tuple destructuring requires static ABI-word tuple members"
                if elemWords != 1 then
                  throwErrorAt rhs
                    "arrayElement tuple destructuring currently supports top-level single-word tuple members"
                valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
                  $(strTerm paramName)
                  $indexLocal
                  $(natTerm elementWords)
                  $(natTerm offset)))
                offset := offset + elemWords
          | none =>
              let _ ←
                match abiLocalHeadWordCount? (.tuple elemTys) with
                | some n => pure n
                | none =>
                    throwErrorAt rhs
                      "arrayElement tuple destructuring requires an ABI-decodable tuple element type"
              for (elemTy, name?) in elemTys.zip names.toList do
                if isSingleWordStaticValueType elemTy then
                  valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementDynamicWord
                    $(strTerm paramName)
                    $indexLocal
                    $(natTerm offset)))
                else
                  match name? with
                  | none =>
                      valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.literal 0))
                  | some boundName =>
                      throwErrorAt rhs
                        s!"arrayElement tuple destructuring cannot bind dynamic member '{boundName}' yet; use '_' for nested dynamic members"
                let elemHeadWords ←
                  match abiLocalHeadWordCount? elemTy with
                  | some n => pure n
                  | none =>
                      throwErrorAt rhs
                        "arrayElement tuple destructuring requires ABI-decodable tuple members"
                offset := offset + elemHeadWords
          let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
            name?.map (fun name => (name, valueExpr))
          let boundStmts ← boundPairs.mapM fun (name, valueExpr) =>
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
          pure (some (#[indexStmt] ++ boundStmts, (indexName, .uint256)))
      | _ => pure none
  | _ => pure none

private def arrayElementTupleReturnStmts?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (rhs : Term) : CommandElabM (Option (Array Term × TypedLocal)) := do
  match stripParens rhs with
  | `(term| arrayElement $name:term $index:term) =>
      let paramName := ← expectStringOrIdent name
      match params.find? (fun p => p.name == paramName) with
      | some { ty := .array (.tuple elemTys), .. } =>
          let elementWords ←
            match staticAbiWordCount? (.tuple elemTys) with
            | some n => pure n
            | none =>
                throwErrorAt rhs
                  "arrayElement tuple return requires a static ABI-word tuple element type"
          let indexName := freshSyntheticLocalName "arrayElement_index" params locals mutableLocals
          let indexExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals index
          let indexStmt ←
            `(Compiler.CompilationModel.Stmt.letVar $(strTerm indexName) $indexExpr)
          let indexLocal ←
            `(Compiler.CompilationModel.Expr.localVar $(strTerm indexName))
          let mut offset := 0
          let mut valueExprs : Array Term := #[]
          for elemTy in elemTys do
            let elemWords ←
              match staticAbiWordCount? elemTy with
              | some n => pure n
              | none =>
                  throwErrorAt rhs
                    "arrayElement tuple return requires static ABI-word tuple members"
            if elemWords != 1 then
              throwErrorAt rhs
                "arrayElement tuple return currently supports top-level single-word tuple members"
            valueExprs := valueExprs.push (← `(Compiler.CompilationModel.Expr.arrayElementWord
              $(strTerm paramName)
              $indexLocal
              $(natTerm elementWords)
              $(natTerm offset)))
            offset := offset + elemWords
          let returnStmt ←
            `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ])
          pure (some (#[indexStmt, returnStmt], (indexName, .uint256)))
      | _ => pure none
  | _ => pure none

private def tupleLiteralOrStructValueExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let structValueExprs? : CommandElabM (Option (Array Term)) := do
    match stripParens rhs with
    | `(term| structMembers $field:term $key:term $members:term) => do
        let fieldName := ← expectStringOrIdent field
        let memberNames := ← expectStringList members
        let exprs ← memberNames.mapM fun memberName => do
          let _ ← lookupStructMemberDecl fields fieldName memberName false
          `(Compiler.CompilationModel.Expr.structMember
              $(strTerm fieldName)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(strTerm memberName))
        pure (some exprs)
    | `(term| structMembers2 $field:term $key1:term $key2:term $members:term) => do
        let fieldName := ← expectStringOrIdent field
        let memberNames := ← expectStringList members
        let exprs ← memberNames.mapM fun memberName => do
          let _ ← lookupStructMemberDecl fields fieldName memberName true
          `(Compiler.CompilationModel.Expr.structMember2
              $(strTerm fieldName)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
              $(strTerm memberName))
        pure (some exprs)
    | _ => pure none
  match tupleElemsFromTerm? rhs with
  | some elems =>
      pure (some (← elems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)))
  | none =>
      match ← arrayElementTupleElemExprs? fields constDecls immutableDecls params locals rhs with
      | some exprs => pure (some exprs)
      | none => structValueExprs?

private def tupleValueExprs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Array Term) := do
  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
  | some exprs => pure exprs
  | none =>
      match stripParens rhs with
      | `(term| $id:ident) =>
          match (← tupleParamElemExprs? params (toString id.getId)) with
          | some exprs => pure exprs
          | none => throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, or structMembers/structMembers2 source"
      | _ =>
          throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, or structMembers/structMembers2 source"

private def tupleReturnValueExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
  | some exprs => pure (some exprs)
  | none =>
      match stripParens rhs with
      | `(term| $id:ident) =>
          tupleParamElemExprs? params (toString id.getId)
      | _ =>
          pure none

private def tupleInternalCallAssignStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option Term) := do
  let rhs := stripParens rhs
  let initialUsedNames := (params.toList.map (fun p => p.name)) ++ (typedLocalNames locals).toList ++ (names.filterMap id).toList
  let (_, targetNamesRev) := names.toList.zipIdx.foldl
    (fun (acc : List String × List String) (name?, idx) =>
      let (usedNames, targetNamesRev) := acc
      let targetName := match name? with
        | some name => name
        | none => freshDiscardName usedNames idx
      (targetName :: usedNames, targetName :: targetNamesRev))
    (initialUsedNames, [])
  let targetNames := targetNamesRev.reverse
  let resultNameTerms := targetNames.toArray.map strTerm
  match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
  | some (fn, argTerms) =>
      ensureSupportsInternalHelperSpec rhs fn
      let argExprs ← argTerms.mapM
        (translatePureExprWithTypes fields constDecls immutableDecls params locals)
      pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
        [ $[$resultNameTerms],* ]
        $(strTerm (internalHelperSpecNameFor fn))
        [ $[$argExprs],* ])))
  | none =>
      match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
      | some (qualifiedName, argTerms) =>
          let _ ← unsafe qualifiedTupleBindTypedLocals rhs.raw qualifiedName names
          let argExprs ← argTerms.mapM
            (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
            [ $[$resultNameTerms],* ]
            $(strTerm (qualifiedInternalHelperName functions qualifiedName))
            [ $[$argExprs],* ])))
      | none =>
          pure none

/-- Try to translate a tuple‐destructured `tryExternalCall "name" [args]` RHS into
    a `Stmt.tryExternalCallBind` term.  Returns `none` when the RHS is not a
    `tryExternalCall` application.  Returns the statement term and the inferred
    types for each bound name (Bool for success flag, Uint256 for all result
    vars — precise return types require external decl lookup which happens in
    the validation pass).  (#1727, Axis 1 Step 5f) -/
private def tryExternalCallBindStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option (Term × Array ValueType)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| tryExternalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argExprs ← match stripParens args with
        | `(term| [ $[$xs],* ]) =>
            xs.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
        | _ => throwErrorAt args "expected list literal [..]"
      -- names[0] is the success flag, names[1..] are result vars
      let initialUsedNames := (params.toList.map (fun p => p.name)) ++ (typedLocalNames locals).toList ++ (names.filterMap id).toList
      let (_, targetNamesRev) := names.toList.zipIdx.foldl
        (fun (acc : List String × List String) (name?, idx) =>
          let (usedNames, targetNamesRev) := acc
          let targetName := match name? with
            | some name => name
            | none => freshDiscardName usedNames idx
          (targetName :: usedNames, targetName :: targetNamesRev))
        (initialUsedNames, [])
      let targetNames := targetNamesRev.reverse
      let successVar := match targetNames.head? with
        | some n => n
        | none => "_try_success"
      let resultVars := targetNames.drop 1
      let successVarTerm := strTerm successVar
      let resultVarTerms := resultVars.toArray.map strTerm
      let stmt ← `(Compiler.CompilationModel.Stmt.tryExternalCallBind
          $successVarTerm
          [ $[$resultVarTerms],* ]
          $(strTerm extName)
          [ $[$argExprs],* ])
      let resultTys ←
        match externalDecls.find? (fun ext => ext.name == extName) with
        | some ext =>
            if ext.returnTys.size != resultVars.length then
              throwErrorAt rhs s!"tryExternalCall '{extName}' binds {resultVars.length} result value(s), but the external declaration returns {ext.returnTys.size}"
            pure ext.returnTys
        | none =>
            -- Validation reports the unknown external with full context; keep
            -- translation moving with word-shaped placeholders.
            pure (Array.replicate resultVars.length .uint256)
      let tys := #[ValueType.bool] ++ resultTys
      pure (some (stmt, tys))
  | _ => pure none

private def expectExprList
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM (Array Term) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      xs.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
  | _ => throwErrorAt stx "expected list literal [..]"

private def translateBindSource
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (rhs : Term) : CommandElabM Term := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 | .scalar .int256 | .scalar (.newtype _ .uint256) | .scalar (.adt _ _) =>
          `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; encode as Uint256 and use getStorage"
      | .scalar .address | .scalar (.newtype _ .address) =>
          throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address | .scalar (.newtype _ .address) =>
          `(Compiler.CompilationModel.Expr.storageAddr $(strTerm f.name))
      | .scalar .uint256 | .scalar (.newtype _ .uint256) =>
          throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; use getStorage"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .dynamicArray _ => throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2/getMappingN"
  | `(term| getStorageArrayLength $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Expr.storageArrayLength $(strTerm f.name))
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getStorageArrayElement $field:ident $index:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Expr.storageArrayElement
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index))
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a storage dynamic array"
  | `(term| getMapping $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Uint256-keyed; use getMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUint $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUintAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingWord $field:ident $key:term $wordOffset:num) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingWord
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $wordOffset)
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .dynamicArray _ =>
          throwErrorAt rhs s!"field '{f.name}' is a storage dynamic array; use getStorageArrayLength/getStorageArrayElement"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
      | .mappingChain _ =>
          throwErrorAt rhs s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use getMappingN"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping2
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| getMappingN $field:ident $keys:term) => do
      let f ← lookupStorageField fields (toString field.getId)
      let keyTerms ← expectMappingKeyTerms keys
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size != keyTypes.length then
            throwErrorAt rhs s!"field '{f.name}' expects {keyTypes.length} mapping keys, but getMappingN received {keyTerms.size}"
          let keyExprs ← keyTerms.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Expr.mappingChain
              $(strTerm f.name)
              [ $[$keyExprs],* ])
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
          | _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
          $(strTerm memberName))
  | `(term| msgSender) | `(term| Verity.msgSender) => `(Compiler.CompilationModel.Expr.caller)
  | `(term| msgValue) | `(term| Verity.msgValue) => `(Compiler.CompilationModel.Expr.msgValue)
  | `(term| selfBalance) | `(term| Verity.selfBalance) =>
      `(Compiler.CompilationModel.Expr.selfBalance)
  | `(term| blockTimestamp) | `(term| Verity.blockTimestamp) =>
      `(Compiler.CompilationModel.Expr.blockTimestamp)
  | `(term| blockNumber) | `(term| Verity.blockNumber) =>
      `(Compiler.CompilationModel.Expr.blockNumber)
  | `(term| blobbasefee) | `(term| Verity.blobbasefee) =>
      `(Compiler.CompilationModel.Expr.blobbasefee)
  | `(term| contractAddress) | `(term| Verity.contractAddress) =>
      `(Compiler.CompilationModel.Expr.contractAddress)
  | `(term| chainid) | `(term| Verity.chainid) =>
      `(Compiler.CompilationModel.Expr.chainid)
  | `(term| tload $offset:term) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset))
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals rhs with
      | some (fn, argTerms) =>
          ensureSupportsInternalHelperSpec rhs fn
          let argExprs ← argTerms.mapM
            (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Expr.internalCall
              $(strTerm (internalHelperSpecNameFor fn))
              [ $[$argExprs],* ])
      | none =>
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, argTerms) =>
              let argExprs ← argTerms.mapM
                (translatePureExprWithTypes fields constDecls immutableDecls params locals)
              `(Compiler.CompilationModel.Expr.internalCall
                  $(strTerm (qualifiedInternalHelperName functions qualifiedName))
                  [ $[$argExprs],* ])
          | none =>
              throwErrorAt rhs
                "unsupported bind source; expected getStorage/getStorageAddr/getStorageArrayLength/getStorageArrayElement/getMapping/getMappingAddr/getMappingUint/getMappingUintAddr/getMappingWord/getMapping2/getMappingN/structMember/structMember2/msgSender/msgValue/selfBalance/tload/ecrecover, a direct internal helper call, or a qualified library helper call"

private def translateSafeRequireBind
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (varName : String)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| requireSomeUint $optExpr:term $msg:term) =>
      let msgLit ← strTerm <$> expectStringLiteral msg
      let optExpr := stripParens optExpr
      match optExpr with
      | `(term| safeAdd $a:term $b:term) =>
          let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $valueExpr $aExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | `(term| safeSub $a:term $b:term) =>
          let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | `(term| safeMul $a:term $b:term) =>
          let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.mul $aExpr $bExpr)
          let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
          let divisorZeroExpr : Term ← `(Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr)
          let quotientExpr : Term ← `(Compiler.CompilationModel.Expr.div $valueExpr $bExpr)
          let noOverflowExpr : Term ← `(Compiler.CompilationModel.Expr.eq $quotientExpr $aExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.logicalOr $divisorZeroExpr $noOverflowExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | `(term| safeDiv $a:term $b:term) =>
          let aExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.div $aExpr $bExpr)
          let zeroExpr : Term ← `(Compiler.CompilationModel.Expr.literal 0)
          let guardExpr : Term ←
            `(Compiler.CompilationModel.Expr.logicalNot
                (Compiler.CompilationModel.Expr.eq $bExpr $zeroExpr))
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | _ =>
          throwErrorAt rhs "unsupported requireSomeUint source; expected safeAdd, safeSub, safeMul, or safeDiv"
  | _ => pure none

private def lookupFunctionByNameAndArity
    (functions : Array FunctionDecl)
    (name : String)
    (arity : Nat) : Option FunctionDecl :=
  functions.find? fun fn => fn.name == name && fn.params.size == arity

mutual
private partial def validateDoSeqExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (doSeq : DoSeq) : CommandElabM Unit := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals elems
      pure ()
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def validateDoElemsExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array TypedLocal) := do
  let mut branchLocals := locals
  for elem in elems do
    branchLocals ← validateDoElemExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params branchLocals elem
  pure branchLocals

private partial def validateDoElemExprTypes
    (ownerName : String)
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (errorDecls : Array ErrorDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (elem : TSyntax `doElem) : CommandElabM (Array TypedLocal) := do
  let tupleCase? ← do
    let stx := elem.raw
    if stx.getKind == `Lean.Parser.Term.doLet then
      let decl := stx[2]
      let patDecl := decl[0]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          let rhs : Term := ⟨patDecl[4]⟩
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              let typedNames ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
              pure (some (locals ++ typedNames))
          | none =>
              match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs) with
              | some valueTys =>
                  if names.size != valueTys.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueTys.size} values"
                  for (name?, ty) in names.zip valueTys do
                    if let some name := name? then
                      requireSupportedLocalBindingType patDecl s!"local binding '{name}'" ty
                  let typedNames := (names.zip valueTys).filterMap fun (name?, ty) =>
                    name?.map (fun name => (name, ty))
                  pure (some (locals ++ typedNames))
              | none => pure none
      | none => pure none
    else if stx.getKind == `Lean.Parser.Term.doLetArrow then
      let patDecl := stx[2]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          let rhs : Term := ⟨patDecl[2][0]⟩
          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
          | some (qualifiedName, _) =>
              let typedNames ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
              pure (some (locals ++ typedNames))
          | none =>
              match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs) with
              | some valueTys =>
                  if names.size != valueTys.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueTys.size} values"
                  for (name?, ty) in names.zip valueTys do
                    if let some name := name? then
                      requireSupportedLocalBindingType patDecl s!"local binding '{name}'" ty
                  let typedNames := (names.zip valueTys).filterMap fun (name?, ty) =>
                    name?.map (fun name => (name, ty))
                  pure (some (locals ++ typedNames))
              | none => pure none
      | none => pure none
    else
      pure none
  match tupleCase? with
  | some typedLocals => pure typedLocals
  | none => match elem with
      | `(doElem| let mut $name:ident := $rhs:term) =>
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
          pure <| locals.push (toString name.getId, ty)
      | `(doElem| let $name:ident := $rhs:term) =>
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
          pure <| locals.push (toString name.getId, ty)
      | `(doElem| let $name:ident ← $rhs:term) =>
          let ty ← inferBindSourceType fields constDecls immutableDecls externalDecls functions params locals rhs
          requireSupportedLocalBindingType name s!"local binding '{toString name.getId}'" ty
          pure <| locals.push (toString name.getId, ty)
      | `(doElem| $name:ident := $rhs:term) =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          pure locals
      | `(doElem| return $value:term) =>
          let _ ←
            match (← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals value) with
            | some _ => pure .unit
            | none => inferPureExprType fields constDecls immutableDecls externalDecls params locals value
          pure locals
      | `(doElem| pure ()) =>
          pure locals
      | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
          requireBoolType cond "if condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond)
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals thenBranch
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals elseBranch
          pure locals
      | `(doElem| forEach $name:term $count:term $body:term) =>
          requireWordLikeType count "forEach count" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals count)
          match stripParens body with
          | `(term| do $[$inner:doElem]*) =>
              let _ ← validateDoElemsExprTypes
                ownerName fields constDecls immutableDecls externalDecls errorDecls functions params
                (locals.push (← expectStringOrIdent name, .uint256))
                inner
              pure locals
          | _ => throwErrorAt body "forEach body must be a do block"
      | `(doElem| requireError $cond:term $errorName:ident($args,*)) =>
          requireBoolType cond "requireError condition" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals cond)
          for arg in args.getElems do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems
          pure locals
      | `(doElem| revert $errorName:ident($args,*)) =>
          for arg in args.getElems do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems
          pure locals
      | `(doElem| revertError $errorName:ident($args,*)) =>
          for arg in args.getElems do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg
          validateCustomErrorCall ownerName (toString errorName.getId)
            params errorDecls args.getElems
          pure locals
      | `(doElem| tryCatch $attempt:term $handler:term) => do
          requireWordLikeType attempt "tryCatch attempt"
            (← inferPureExprType fields constDecls immutableDecls externalDecls params locals attempt)
          let (payloadName?, catchElems) ← parseTryCatchHandler handler
          validateTryCatchHandlerDoesNotUsePayload handler payloadName? catchElems
          let _ ← validateDoElemsExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals catchElems
          pure locals
      | `(doElem| unsafe $_reason:str do $body:doSeq) =>
          validateDoSeqExprTypes ownerName fields constDecls immutableDecls externalDecls errorDecls functions params locals body
          pure locals
      | `(doElem| $stmt:term) =>
          validateEffectStmtExprTypes fields constDecls immutableDecls externalDecls functions params locals stmt
          pure locals
      | _ => throwErrorAt elem "unsupported do element"

private partial def validateEffectStmtExprTypes
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Unit := do
  let stx := stripParens stx
  match stx with
  | `(term| safeTransfer $token:term $to:term $amount:term) =>
      for arg in [token, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| safeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
      for arg in [token, fromAddr, to, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| safeApprove $token:term $spender:term $amount:term) =>
      for arg in [token, spender, amount] do
        requireWordLikeType arg "ERC-20 helper" (← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg)
  | `(term| setStorage $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.adtInfo?, f.ty with
      | some _, _ => pure ()
      | none, .scalar (.adt _ _) => pure ()
      | _, _ =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
          pure ()
  | `(term| setStorageAddr $_field:ident $value:term)
    | `(term| require $value:term $_msg) =>
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| setPackedStorage $_field:ident $_wordOffset:num $value:term) =>
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| pushStorageArray $_field:ident $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| popStorageArray $_field:ident) =>
      pure ()
  | `(term| setStorageArrayElement $_field:ident $index:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals index
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
      pure ()
  | `(term| setMapping $_field:ident $key:term $value:term) | `(term| setMappingAddr $_field:ident $key:term $value:term)
    | `(term| setMappingUint $_field:ident $key:term $value:term) | `(term| setMappingUintAddr $_field:ident $key:term $value:term)
    | `(term| setMappingWord $_field:ident $key:term $_wordOffset:num $value:term)
    | `(term| setStructMember $_field:term $key:term $_member:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| setMapping2 $_field:ident $key1:term $key2:term $value:term)
    | `(term| setStructMember2 $_field:term $key1:term $key2:term $_member:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key1
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key2
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| setMappingN $_field:ident $keys:term $value:term) => do
      for key in (← expectMappingKeyTerms keys) do
        let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals key
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| mstore $offset:term $value:term) | `(term| tstore $offset:term $value:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals offset
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals value
  | `(term| calldatacopy $destOffset:term $sourceOffset:term $size:term)
    | `(term| returndataCopy $destOffset:term $sourceOffset:term $size:term) => do
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals destOffset
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals sourceOffset
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals size
  | `(term| rawLog $topics:term $dataOffset:term $dataSize:term) => do
      match stripParens topics with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt topics "expected list literal [..]"
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals dataOffset
      let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals dataSize
  | `(term| returnValues $values:term) | `(term| emit $_eventName:term $values:term) => do
      match stripParens values with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt values "expected list literal [..]"
      pure ()
  | `(term| ecmDo $_module:term $args:term) => do
      validateWordLikeExprListLiteral fields constDecls immutableDecls externalDecls params locals
        args "ECM argument"
      pure ()
  | `(term| returnArray $name:term) => do
      let ty ← requireDirectParamRef name "returnArray" params
      requireSupportedReturnArrayType name "returnArray" ty
  | `(term| returnBytes $name:term) => do
      let ty ← requireDirectParamRef name "returnBytes" params
      requireSupportedReturnBytesType name "returnBytes" ty
  | `(term| returnStorageWords $name:term) => do
      let ty ← requireDirectParamRef name "returnStorageWords" params
      requireSupportedReturnStorageWordsType name "returnStorageWords" ty
  | `(term| externalCallBind $_names:term $_fnName:term $args:term)
    | `(term| tryExternalCallBind $_successVar:term $_names:term $_fnName:term $args:term) =>
      match stripParens args with
      | `(term| [ $[$xs],* ]) =>
          for x in xs do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals x
      | _ => throwErrorAt args "expected list literal [..]"
  | `(term| revertReturndata) =>
      pure ()
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals stx with
      | some (fn, argTerms) =>
          ensureSupportsInternalHelperSpec stx fn
          if fn.returnTy != .unit then
            throwErrorAt stx
              s!"helper call '{fn.name}' returns {renderValueType fn.returnTy}; use `let ... ← {fn.name} ...` or tuple destructuring"
          for arg in argTerms do
            let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals arg
          pure ()
      | none =>
          let _ ← inferPureExprType fields constDecls immutableDecls externalDecls params locals stx
          pure ()
end

private def validateFunctionBodyExprTypes
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM Unit := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes fn.name fields constDecls immutableDecls externalDecls errorDecls functions fn.params #[] elems
      pure ()
  | _ => throwErrorAt fn.body "function body must be a do block"

private def validateConstantExprTypes
    (constDecls : Array ConstantDecl) : CommandElabM Unit := do
  for constant in constDecls do
    let inferredTy ← inferPureExprType #[] constDecls #[] #[] #[] #[] constant.body
    requireDeclaredValueType constant.body s!"constant '{constant.name}'" constant.ty inferredTy

private def validateConstructorBodyExprTypes
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (ctor : ConstructorDecl) : CommandElabM Unit := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      let _ ← validateDoElemsExprTypes "constructor" fields constDecls immutableDecls externalDecls errorDecls functions ctor.params #[] elems
      pure ()
  | _ => throwErrorAt ctor.body "constructor body must be a do block"

private def translateERC20BindStmt?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (varName : String)
    (rhs : Term) : CommandElabM (Option Term) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| balanceOf $token:term $owner:term) =>
      match lookupFunctionByNameAndArity functions "balanceOf" 2 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let ownerExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals owner
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.balanceOfModule $(strTerm varName))
            [$tokenExpr, $ownerExpr]))
  | `(term| allowance $token:term $owner:term $spender:term) =>
      match lookupFunctionByNameAndArity functions "allowance" 3 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let ownerExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals owner
          let spenderExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals spender
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.allowanceModule $(strTerm varName))
            [$tokenExpr, $ownerExpr, $spenderExpr]))
  | `(term| totalSupply $token:term) =>
      match lookupFunctionByNameAndArity functions "totalSupply" 1 with
      | some localFn =>
          throwErrorAt rhs
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | none =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          pure <| some (← `(Compiler.CompilationModel.Stmt.ecm
            (Compiler.Modules.ERC20.totalSupplyModule $(strTerm varName))
            [$tokenExpr]))
  | _ => pure none

private def adtConstructorApp? (stx : Term) : Option (Ident × Array Term) :=
  let stx := stripParens stx
  match stx with
  | `(term| $ctor:ident) => some (ctor, #[])
  | `(term| $ctor:ident $args:term*) => some (ctor, args)
  | _ => none

private def adtConstructorSyntax? (stx : Term) : Option (String × Array Term) :=
  let stx := stripParens stx
  match stx with
  | `(term| $variant:str) => some (variant.getString, #[])
  | `(term| ($variant:str, [ $[$args:term],* ])) => some (variant.getString, args)
  | `(term| adt $variant:str) => some (variant.getString, #[])
  | `(term| adt $variant:str [ $[$args:term],* ]) => some (variant.getString, args)
  | _ =>
      match adtConstructorApp? stx with
      | some (variant, args) =>
          if toString variant.getId == "adt" then
            match args with
            | #[arg] =>
                match stripParens arg with
                | `(term| $variant:str) => some (variant.getString, #[])
                | _ => none
            | #[arg, argList] =>
                match stripParens arg, stripParens argList with
                | `(term| $variant:str), `(term| [ $[$payloadArgs:term],* ]) =>
                    some (variant.getString, payloadArgs)
                | _, _ => none
            | _ => none
          else
            some (toString variant.getId, args)
      | none => none

private def translateAdtConstructForStorage
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (adtName : String)
    (value : Term) : CommandElabM Term := do
  match adtConstructorSyntax? value with
  | some (variantName, args) =>
      let argExprs ← args.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
      `(Compiler.CompilationModel.Expr.adtConstruct
          $(strTerm adtName)
          $(strTerm variantName)
          [ $[$argExprs],* ])
  | none =>
      throwErrorAt value
        s!"ADT storage assignment for '{adtName}' must use a variant constructor so payload slots are preserved"

private def storageFieldAdtName? (field : StorageFieldDecl) : Option String :=
  match field.adtInfo? with
  | some (adtName, _) => some adtName
  | none =>
      match field.ty with
      | .scalar (.adt adtName _) => some adtName
      | _ => none

private def translateEffectStmt
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| safeTransfer $token:term $to:term $amount:term) =>
      match lookupFunctionByNameAndArity functions "safeTransfer" 3 with
      | some localFn =>
          throwErrorAt stx
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | _ =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
          let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
          `(Compiler.CompilationModel.Stmt.ecm
              Compiler.Modules.ERC20.safeTransferModule
              [$tokenExpr, $toExpr, $amountExpr])
  | `(term| safeTransferFrom $token:term $fromAddr:term $to:term $amount:term) =>
      match lookupFunctionByNameAndArity functions "safeTransferFrom" 4 with
      | some localFn =>
          throwErrorAt stx
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | _ =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let fromExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals fromAddr
          let toExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals to
          let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
          `(Compiler.CompilationModel.Stmt.ecm
              Compiler.Modules.ERC20.safeTransferFromModule
              [$tokenExpr, $fromExpr, $toExpr, $amountExpr])
  | `(term| safeApprove $token:term $spender:term $amount:term) =>
      match lookupFunctionByNameAndArity functions "safeApprove" 3 with
      | some localFn =>
          throwErrorAt stx
            s!"ERC-20 helper form '{localFn.name}' conflicts with contract function '{localFn.name}'; rename the function or avoid the direct helper syntax here"
      | _ =>
          let tokenExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals token
          let spenderExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals spender
          let amountExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals amount
          `(Compiler.CompilationModel.Stmt.ecm
              Compiler.Modules.ERC20.safeApproveModule
              [$tokenExpr, $spenderExpr, $amountExpr])
  | `(term| ecmDo $module:term $args:term) =>
      validateEffectOnlyEcmModuleTerm module
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.ecm
          $module
          [ $[$argExprs],* ])
  | `(term| setStorage $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match storageFieldAdtName? f with
      | some adtName =>
          `(Compiler.CompilationModel.Stmt.setStorage
              $(strTerm f.name)
              $(← translateAdtConstructForStorage fields constDecls immutableDecls params locals adtName value))
      | none =>
          match f.ty with
          | .scalar .uint256 | .scalar .int256 | .scalar (.newtype _ .uint256) =>
              `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
          | .scalar (.adt adtName _) =>
              `(Compiler.CompilationModel.Stmt.setStorage
                  $(strTerm f.name)
                  $(← translateAdtConstructForStorage fields constDecls immutableDecls params locals adtName value))
          | .scalar .address | .scalar (.newtype _ .address) =>
              throwErrorAt stx s!"field '{f.name}' is Address-valued; use setStorageAddr"
          | .dynamicArray _ =>
              throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
          | _ =>
              throwErrorAt stx s!"field '{f.name}' is not Uint256; use setStorageAddr"
  | `(term| setStorageAddr $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address | .scalar (.newtype _ .address) =>
          `(Compiler.CompilationModel.Stmt.setStorageAddr $(strTerm f.name) $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .scalar .uint256 | .scalar (.newtype _ .uint256) =>
          throwErrorAt stx s!"field '{f.name}' is Uint256-valued; use setStorage"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | _ =>
          throwErrorAt stx s!"field '{f.name}' is not Address; use setStorage"
  | `(term| setPackedStorage $field:ident $wordOffset:num $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar _ =>
          `(Compiler.CompilationModel.Stmt.setStorageWord
              $(strTerm f.name)
              $(natTerm (← natFromSyntax wordOffset))
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; setPackedStorage requires a scalar root slot"
      | .mappingAddressToUint256 | .mappingUintToUint256 | .mapping2AddressToAddressToUint256
      | .mappingChain _ | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a mapping; setPackedStorage requires a scalar root slot"
  | `(term| setMapping $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Uint256-keyed; use setMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUint $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUintAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingWord $field:ident $key:term $wordOffset:num $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingWord
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
              $wordOffset
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .dynamicArray _ =>
          throwErrorAt stx s!"field '{f.name}' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
      | .mappingChain _ =>
          throwErrorAt stx s!"field '{f.name}' uses {storageTypeMappingDepth? f.ty |>.getD 0} mapping keys; use setMappingN"
  | `(term| setMapping2 $field:ident $key1:term $key2:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping2
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | _ => throwErrorAt stx s!"field '{f.name}' is not a double mapping"
  | `(term| setMappingN $field:ident $keys:term $value:term) => do
      let f ← lookupStorageField fields (toString field.getId)
      let keyTerms ← expectMappingKeyTerms keys
      match storageTypeMappingKeyTypes? f.ty with
      | some keyTypes =>
          if keyTerms.size != keyTypes.length then
            throwErrorAt stx s!"field '{f.name}' expects {keyTypes.length} mapping keys, but setMappingN received {keyTerms.size}"
          let keyExprs ← keyTerms.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Stmt.setMappingChain
              $(strTerm f.name)
              [ $[$keyExprs],* ]
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | none =>
          match f.ty with
          | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
              throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
          | _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| pushStorageArray $field:ident $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.storageArrayPush
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| popStorageArray $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.storageArrayPop $(strTerm f.name))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| setStorageArrayElement $field:ident $index:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .dynamicArray _ =>
          `(Compiler.CompilationModel.Stmt.setStorageArrayElement
              $(strTerm f.name)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals index)
              $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
      | _ => throwErrorAt stx s!"field '{f.name}' is not a storage dynamic array"
  | `(term| require $cond $msg) =>
      `(Compiler.CompilationModel.Stmt.require
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond)
          $(strTerm (← expectStringLiteral msg)))
  | `(term| mstore $offset:term $value:term) =>
      `(Compiler.CompilationModel.Stmt.mstore
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| tstore $offset:term $value:term) =>
      `(Compiler.CompilationModel.Stmt.tstore
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals offset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| calldatacopy $destOffset:term $sourceOffset:term $size:term) =>
      `(Compiler.CompilationModel.Stmt.calldatacopy
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size))
  | `(term| returndataCopy $destOffset:term $sourceOffset:term $size:term) =>
      `(Compiler.CompilationModel.Stmt.returndataCopy
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals size))
  | `(term| revertReturndata) =>
      `(Compiler.CompilationModel.Stmt.revertReturndata)
  | `(term| returnValues $values:term) =>
      let valueExprs ← expectExprList fields constDecls immutableDecls params locals values
      `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ])
  | `(term| returnArray $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnArray $(strTerm (← expectStringOrIdent name)))
  | `(term| returnBytes $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnBytes $(strTerm (← expectStringOrIdent name)))
  | `(term| returnStorageWords $name:term) =>
      `(Compiler.CompilationModel.Stmt.returnStorageWords $(strTerm (← expectStringOrIdent name)))
  | `(term| emit $eventName:term $args:term) =>
      let evName := ← expectStringOrIdent eventName
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.emit $(strTerm evName) [ $[$argExprs],* ])
  | `(term| rawLog $topics:term $dataOffset:term $dataSize:term) =>
      let topicExprs ← expectExprList fields constDecls immutableDecls params locals topics
      `(Compiler.CompilationModel.Stmt.rawLog
          [ $[$topicExprs],* ]
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals dataOffset)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals dataSize))
  | `(term| externalCallBind $names:term $fnName:term $args:term) =>
      let resultNames := ← expectStringList names
      let resultNameTerms := resultNames.map strTerm
      let targetFn := ← expectStringOrIdent fnName
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.externalCallBind
          [ $[$resultNameTerms],* ]
          $(strTerm targetFn)
          [ $[$argExprs],* ])
  | `(term| setStructMember $field:term $key:term $member:term $value:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Stmt.setStructMember
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key)
          $(strTerm memberName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | `(term| setStructMember2 $field:term $key1:term $key2:term $member:term $value:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Stmt.setStructMember2
          $(strTerm fieldName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key1)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals key2)
          $(strTerm memberName)
          $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value))
  | _ =>
      match ← resolveLocalFunctionApp? fields constDecls immutableDecls externalDecls functions params locals stx with
      | some (fn, argTerms) =>
          ensureSupportsInternalHelperSpec stx fn
          if fn.returnTy != .unit then
            throwErrorAt stx
              s!"helper call '{fn.name}' returns {renderValueType fn.returnTy}; use `let ... ← {fn.name} ...` or tuple destructuring"
          let argExprs ← argTerms.mapM
            (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          `(Compiler.CompilationModel.Stmt.internalCall
              $(strTerm (internalHelperSpecNameFor fn))
              [ $[$argExprs],* ])
      | none =>
          throwErrorAt stx "unsupported statement in do block"

mutual
private partial def translateDoElems
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array Term × Array TypedLocal × Array String) := do
  let mut branchLocals := locals
  let mut branchMutableLocals := mutableLocals
  let mut stmts : Array Term := #[]
  for elem in elems do
    let (newStmts, newLocals, newMutableLocals) ←
      translateDoElem fields constDecls immutableDecls externalDecls functions params branchLocals branchMutableLocals elem
    stmts := stmts ++ newStmts
    branchLocals := newLocals
    branchMutableLocals := newMutableLocals
  pure (stmts, branchLocals, branchMutableLocals)

private partial def translateDoSeqToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (doSeq : DoSeq) : CommandElabM (Array Term) := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls externalDecls functions params locals mutableLocals elems)).1
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def translateDoElem
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (params : Array ParamDecl)
    (locals : Array TypedLocal)
    (mutableLocals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Array Term × Array TypedLocal × Array String) := do
  let localNames := typedLocalNames locals
  let tupleCase? ← do
    let stx := elem.raw
    if stx.getKind == `Lean.Parser.Term.doLet then
      let decl := stx[2]
      let patDecl := decl[0]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames localNames names stx
          let rhs : Term := ⟨patDecl[4]⟩
          let rhs := stripParens rhs
          match rhs with
          | `(term| $id:ident) =>
              match (← tupleParamElemExprs? params (toString id.getId)) with
              | some valueExprs =>
                  if names.size != valueExprs.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                  let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                    name?.map (fun name => (name, valueExpr))
                  let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                    `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                  let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                  match valueTys with
                  | some tys =>
                      let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                      pure (some (stmts, locals ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
              | none =>
                  match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
                  | some stmt =>
                      let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                      match valueTys with
                      | some tys =>
                          let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                          pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                      | none =>
                          match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                          | some (qualifiedName, _) =>
                              let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none => throwErrorAt rhs "unable to infer tuple local types"
                  | none =>
                      match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
                      | some (stmt, tys) =>
                          let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                          pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                      | none => throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, structMembers/structMembers2 source, internal helper call, or tryExternalCall"
          | _ =>
              match (← arrayElementTupleDestructureStmts? fields constDecls immutableDecls params locals mutableLocals rhs names) with
              | some (stmts, syntheticLocal) =>
                  let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                  match valueTys with
                  | some tys =>
                      let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                      pure (some (stmts, locals.push syntheticLocal ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
              | none =>
                  match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
                  | some valueExprs =>
                      if names.size != valueExprs.size then
                        throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                      let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                        name?.map (fun name => (name, valueExpr))
                      let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                        `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                      let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                      match valueTys with
                      | some tys =>
                          let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                          pure (some (stmts, locals ++ typedPairs, mutableLocals))
                      | none => throwErrorAt rhs "unable to infer tuple local types"
                  | none =>
                      match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
                      | some stmt =>
                          let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                          match valueTys with
                          | some tys =>
                              let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none =>
                              match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                              | some (qualifiedName, _) =>
                                  let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                              | none => throwErrorAt rhs "unable to infer tuple local types"
                      | none =>
                          match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
                          | some (stmt, tys) =>
                              let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                              pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                          | none =>
                              let valueExprs ← tupleValueExprs fields constDecls immutableDecls params locals rhs
                              if names.size != valueExprs.size then
                                throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                              let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                                name?.map (fun name => (name, valueExpr))
                              let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                                `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                              let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
                              match valueTys with
                              | some tys =>
                                  let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                                  pure (some (stmts, locals ++ typedPairs, mutableLocals))
                              | none => throwErrorAt rhs "unable to infer tuple local types"
      | none => pure none
    else if stx.getKind == `Lean.Parser.Term.doLetArrow then
      let patDecl := stx[2]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames localNames names stx
          let rhs : Term := ⟨patDecl[2][0]⟩
          match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls externalDecls functions params locals rhs names) with
          | some stmt =>
              let valueTys ← inferTupleSourceTypes? fields constDecls immutableDecls externalDecls functions params locals rhs
              match valueTys with
              | some tys =>
                  let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
              | none =>
                  match ← resolveQualifiedFunctionApp? fields constDecls immutableDecls externalDecls params locals rhs with
                  | some (qualifiedName, _) =>
                      let typedPairs ← unsafe qualifiedTupleBindTypedLocals patDecl qualifiedName names
                      pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
                  | none => throwErrorAt rhs "unable to infer tuple local types"
          | none =>
              match (← tryExternalCallBindStmt? fields constDecls immutableDecls externalDecls params locals rhs names) with
              | some (stmt, tys) =>
                  let typedPairs := (names.zip tys).filterMap fun (name?, ty) => name?.map (fun name => (name, ty))
                  pure (some (#[(stmt)], locals ++ typedPairs, mutableLocals))
              | none => throwErrorAt rhs "tuple bind sources must be internal helper calls or tryExternalCall"
      | none => pure none
    else
      pure none
  match tupleCase? with
  | some result => pure result
  | none => match elem with
      | `(doElem| let mut $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          let rhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
              locals.push (varName, ty),
              mutableLocals.push varName)
      | `(doElem| let $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          let rhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
          let ty ← inferPureExprType fields constDecls immutableDecls externalDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
              locals.push (varName, ty),
              mutableLocals)
      | `(doElem| let $name:ident ← $rhs:term) =>
          let varName := toString name.getId
          if localNames.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          match stripParens rhs with
          | `(term| ecmCall $moduleFactory:term $args:term) =>
              let argExprs ← expectExprList fields constDecls immutableDecls params locals args
              let moduleTerm ← `(term| (($moduleFactory) $(strTerm varName)))
              validateSingleResultEcmModuleTerm moduleTerm varName
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.ecm
                        $moduleTerm
                        [ $[$argExprs],* ]))],
                  locals.push (varName, .uint256),
                  mutableLocals)
          | `(term| ecrecover $hash:term $v:term $r:term $s:term) =>
              let hashExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals hash
              let vExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals v
              let rExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals r
              let sExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals s
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.ecm
                        (Compiler.Modules.Precompiles.ecrecoverModule $(strTerm varName))
                        [$hashExpr, $vExpr, $rExpr, $sExpr]))],
                  locals.push (varName, .address),
                  mutableLocals)
          | `(term| tryExternalCall $extName:term $args:term) =>
              -- Zero-return tryExternalCall: `let success ← tryExternalCall "fn" [args]`
              -- produces Stmt.tryExternalCallBind successVar [] externalName args
              let targetFn := ← expectStringOrIdent extName
              let argExprs ← expectExprList fields constDecls immutableDecls params locals args
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.tryExternalCallBind
                        $(strTerm varName)
                        []
                        $(strTerm targetFn)
                        [ $[$argExprs],* ]))],
                  locals.push (varName, .bool),
                  mutableLocals)
          | _ =>
              let safeBind? ← translateSafeRequireBind fields constDecls immutableDecls params locals varName rhs
              match safeBind? with
              | some safeStmts => pure (safeStmts, locals.push (varName, .uint256), mutableLocals)
              | none =>
                  match (← translateERC20BindStmt? fields constDecls immutableDecls functions params locals varName rhs) with
              | some stmt =>
                  pure (#[(stmt)], locals.push (varName, .uint256), mutableLocals)
              | none =>
                      let rhsExpr ← translateBindSource fields constDecls immutableDecls externalDecls functions params locals rhs
                      let ty ← inferBindSourceType fields constDecls immutableDecls externalDecls functions params locals rhs
                      pure
                        (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
                          locals.push (varName, ty),
                          mutableLocals)
      | `(doElem| $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if !localNames.contains varName then
            throwErrorAt name s!"cannot assign unknown variable '{varName}'"
          if !mutableLocals.contains varName then
            throwErrorAt name s!"cannot assign immutable variable '{varName}'; declare it with 'let mut'"
          let rhsExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName) $rhsExpr))],
              locals,
              mutableLocals)
      | `(doElem| return $value:term) =>
          match (← arrayElementTupleReturnStmts? fields constDecls immutableDecls params locals mutableLocals value) with
          | some (stmts, syntheticLocal) =>
              pure (stmts, locals.push syntheticLocal, mutableLocals)
          | none =>
              match (← tupleReturnValueExprs? fields constDecls immutableDecls params locals value) with
              | some valueExprs =>
                  pure (#[(← `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ]))], locals, mutableLocals)
              | none =>
                  pure (#[(← `(Compiler.CompilationModel.Stmt.return $(← translatePureExprWithTypes fields constDecls immutableDecls params locals value)))], locals, mutableLocals)
      | `(doElem| pure ()) =>
          pure (#[], locals, mutableLocals)
      | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
          let condExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals cond
          let thenStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls functions params locals mutableLocals thenBranch
          let elseStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls functions params locals mutableLocals elseBranch
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.ite
              $condExpr
              [ $[$thenStmts],* ]
              [ $[$elseStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| tryCatch $attempt:term $handler:term) => do
          let trySuccessName :=
            freshSyntheticLocalName "verity_try_success" params locals mutableLocals
          let (payloadName?, catchElems) ← parseTryCatchHandler handler
          validateTryCatchHandlerDoesNotUsePayload handler payloadName? catchElems
          let attemptExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals attempt
          let catchTranslation ←
            translateDoElems fields constDecls immutableDecls externalDecls functions params locals mutableLocals catchElems
          let catchStmts := catchTranslation.1
          pure
            (#[
              (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm trySuccessName) $attemptExpr)),
              (← `(Compiler.CompilationModel.Stmt.ite
                    (Compiler.CompilationModel.Expr.eq
                      (Compiler.CompilationModel.Expr.localVar $(strTerm trySuccessName))
                      (Compiler.CompilationModel.Expr.literal 0))
                    [ $[$catchStmts],* ]
                    []))
            ],
            locals,
            mutableLocals)
      | `(doElem| forEach $name:term $count:term $body:term) =>
          let loopVar := ← expectStringOrIdent name
          let countExpr ← translatePureExprWithTypes fields constDecls immutableDecls params locals count
          let bodyStmts ←
            match stripParens body with
            | `(term| do $[$inner:doElem]*) =>
                pure (← (translateDoElems fields constDecls immutableDecls externalDecls functions params (locals.push (loopVar, .uint256)) mutableLocals inner)).1
            | _ => throwErrorAt body "forEach body must be a do block"
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.forEach
                $(strTerm loopVar)
                $countExpr
                [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| requireError $cond:term $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.requireError
                    $(← translatePureExprWithTypes fields constDecls immutableDecls params locals cond)
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revert $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revertError $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExprWithTypes fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| unsafe $reason:str do $body:doSeq) =>
          let bodyStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls externalDecls functions params locals mutableLocals body
          let reasonStr := reason.getString
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.unsafeBlock
                    $(Lean.Quote.quote reasonStr)
                    [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| $stmt:term) =>
          pure (#[(← translateEffectStmt fields constDecls immutableDecls externalDecls functions params locals stmt)], locals, mutableLocals)
      | _ => throwErrorAt elem "unsupported do element"
end

private def translateBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let guardPrelude ← initGuardPreludeStmtTerms fields fn
      let rolePrelude ← roleGuardPreludeStmtTerms fields fn
      let stmts := guardPrelude ++ rolePrelude ++ (← translateDoElems fields constDecls immutableDecls externalDecls functions fn.params #[] #[] elems).1
      let mut stmts := stmts
      if fn.returnTy == .unit then
        stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.stop))
      pure stmts
  | _ => throwErrorAt fn.body "function body must be a do block"

private def translateConstructorBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (ctor : ConstructorDecl) : CommandElabM (Array Term) := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls externalDecls functions ctor.params #[] #[] elems)).1
  | _ => throwErrorAt ctor.body "constructor body must be a do block"

private def immutableInitStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (ctorParams : Array ParamDecl) : CommandElabM (Array Term) := do
  immutableDecls.zipIdx.mapM fun (imm, idx) => do
    let slotField := immutableStorageFieldDecl fields imm idx
    let valueExpr ← translatePureExpr fields constDecls #[] ctorParams #[] imm.body
    match imm.ty with
    | .uint256 | .int256 | .uint8 | .bytes32 | .bool =>
        `(Compiler.CompilationModel.Stmt.setStorage $(strTerm slotField.name) $valueExpr)
    | .address =>
        `(Compiler.CompilationModel.Stmt.setStorageAddr $(strTerm slotField.name) $valueExpr)
    | _ =>
        throwErrorAt imm.ident s!"immutable '{imm.name}' uses unsupported type"

def mkSuffixedIdent (base : Ident) (suffix : String) : CommandElabM Ident :=
  let rec appendSuffix : Name → Name
    | .anonymous => .str .anonymous suffix
    | .str p s => .str p (s ++ suffix)
    | .num p n => .str p (toString n ++ suffix)
  pure <| mkIdent <| appendSuffix base.getId

private def mkContractFnType (params : Array ParamDecl) (retTy : ValueType) : CommandElabM Term := do
  let mut ty ← `(Verity.Contract $(← contractValueTypeTerm retTy))
  for param in params.reverse do
    ty ← `(($(← contractValueTypeTerm param.ty)) → $ty)
  pure ty

private def mkTupleProjectionTerm (base : Term) (elemTys : List ValueType) (idx : Nat) : CommandElabM Term := do
  let rec go (tupleTerm : Term) (remaining : List ValueType) (targetIdx : Nat) : CommandElabM Term := do
    match remaining with
    | [] => throwError "tuple projection index out of bounds"
    | [_] =>
        if targetIdx == 0 then
          pure tupleTerm
        else
          throwError "tuple projection index out of bounds"
    | _ :: rest =>
        if targetIdx == 0 then
          `(Prod.fst $tupleTerm)
        else
          go (← `(Prod.snd $tupleTerm)) rest (targetIdx - 1)
  go base elemTys idx

private def injectTupleParamAliases (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut wrappedBody := body
  for param in params.reverse do
    match param.ty with
    | .tuple elemTys =>
        let baseTerm : Term := mkIdent param.ident.getId
        for (_elemTy, idx) in (elemTys.toArray.zipIdx).reverse do
          let aliasName := mkIdent <| Name.str .anonymous s!"{param.name}_{idx}"
          let projection ← mkTupleProjectionTerm baseTerm elemTys idx
          wrappedBody ← `(term| let $aliasName := $projection; $wrappedBody)
    | _ => pure ()
  pure wrappedBody

private def mkContractFnValue (params : Array ParamDecl) (body : Term) : CommandElabM Term := do
  let mut value ← injectTupleParamAliases params body
  for param in params.reverse do
    let pid := param.ident
    value ← `(fun ($pid : $(← contractValueTypeTerm param.ty)) => $value)
  pure value

private def mkModelParamsTerm (params : Array ParamDecl) : CommandElabM Term := do
  let xs ← params.mapM fun p => do
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $(← modelParamTypeTerm p.ty))
  `([ $[$xs],* ])

private def mkStorageDefCommand (field : StorageFieldDecl) : CommandElabM Cmd := do
  let rec mkStorageMappingTy (keys : List MappingKeyType) : CommandElabM Term := do
    match keys with
    | [] => `(Uint256)
    | keyTy :: rest =>
        `(($(← storageKeyTypeContractTerm keyTy) → $(← mkStorageMappingTy rest)))
  let storageTy ←
    match field.ty with
    | .scalar .uint256 => `(Uint256)
    | .scalar .int256 => `(Uint256)
    | .scalar .uint8 => throwError "storage field cannot be Uint8; use Uint256 encoding"
    | .scalar .address => `(Address)
    | .scalar .bytes32 => throwError "storage field cannot be Bytes32; use Uint256 encoding"
    | .scalar .bool => throwError "storage field cannot be Bool; use Uint256 (0/1) encoding"
    | .scalar .string => throwError "storage field cannot be String; use Uint256 encoding"
    | .scalar .bytes => throwError "storage field cannot be Bytes; use Uint256 encoding"
    | .scalar (.array _) => throwError "storage field cannot be Array; use mapping encodings"
    | .scalar (.tuple _) => throwError "storage field cannot be Tuple; use mapping encodings"
    | .scalar (.struct _ _) => throwError "storage field cannot be named struct; use mapping encodings"
    | .scalar .unit => throwError "storage field cannot be Unit"
    | .scalar (.newtype _ baseType) =>
        -- Newtypes erased to base type for storage (#1727 Step 3b)
        match baseType with
        | .uint256 => `(Uint256)
        | .address => `(Address)
        | _ => throwError "storage field with newtype base type not supported; use Uint256 or Address"
    | .scalar (.adt _ _) => `(Uint256)  -- ADTs stored as tag value in storage (#1727 Step 5b)
    | .dynamicArray .uint256 => `(List Uint256)
    | .dynamicArray .address => `(List Address)
    | .dynamicArray .bool => `(List Bool)
    | .dynamicArray .uint8 => throwError "storage dynamic arrays currently support only Uint256 elements on the macro path"
    | .dynamicArray .bytes32 => `(List Uint256)
    | .mappingAddressToUint256 => `(Address → Uint256)
    | .mapping2AddressToAddressToUint256 => `(Address → Address → Uint256)
    | .mappingUintToUint256 => `(Uint256 → Uint256)
    | .mappingChain keyTypes => mkStorageMappingTy keyTypes
    | .mappingStruct .address _ => `(Address → Uint256)
    | .mappingStruct .uint256 _ => `(Uint256 → Uint256)
    | .mappingStruct2 .address .address _ => `(Address → Address → Uint256)
    | .mappingStruct2 .address .uint256 _ => `(Address → Uint256 → Uint256)
    | .mappingStruct2 .uint256 .address _ => `(Uint256 → Address → Uint256)
    | .mappingStruct2 .uint256 .uint256 _ => `(Uint256 → Uint256 → Uint256)
  let fid := field.ident
  `(command| def $fid : Verity.StorageSlot $storageTy := ⟨$(natTerm field.slotNum)⟩)

private def packedOptionTerm (packed : Option (Nat × Nat)) : CommandElabM Term := do
  match packed with
  | none => `(none)
  | some (offset, width) => `(some ($(natTerm offset), $(natTerm width)))

private def mkStructMemberReadBranches
    (fields : Array StorageFieldDecl)
    (nested : Bool)
    (fallbackTerm : Term) : CommandElabM Term := do
  let mut acc := fallbackTerm
  for field in fields.reverse do
    match nested, field.ty with
    | false, .mappingStruct _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.structMemberAt $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key
            else
              $acc)
    | true, .mappingStruct2 _ _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.structMember2At $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key1 key2
            else
              $acc)
    | _, _ => pure ()
  pure acc

private def mkStructMemberWriteBranches
    (fields : Array StorageFieldDecl)
    (nested : Bool)
    (fallbackTerm : Term) : CommandElabM Term := do
  let mut acc := fallbackTerm
  for field in fields.reverse do
    match nested, field.ty with
    | false, .mappingStruct _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.setStructMemberAt $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key value
            else
              $acc)
    | true, .mappingStruct2 _ _ members =>
        for member in members.reverse do
          let packedTerm ← packedOptionTerm member.packed
          acc ← `(if field == $(strTerm field.name) && member == $(strTerm member.name) then
              _root_.Contracts.setStructMember2At $(natTerm field.slotNum) $(natTerm member.wordOffset)
                $packedTerm key1 key2 value
            else
              $acc)
    | _, _ => pure ()
  pure acc

private def hasStructMapping (fields : Array StorageFieldDecl) : Bool :=
  fields.any fun field =>
    match field.ty with
    | .mappingStruct _ _ => true
    | _ => false

private def hasStructMapping2 (fields : Array StorageFieldDecl) : Bool :=
  fields.any fun field =>
    match field.ty with
    | .mappingStruct2 _ _ _ => true
    | _ => false

def mkExecutableStructMappingCommandsPublic (fields : Array StorageFieldDecl) :
    CommandElabM (Array Cmd) := do
  let mut cmds : Array Cmd := #[]
  if hasStructMapping fields then
    let readFallback : Term ← `(pure default)
    let writeFallback : Term ← `(pure ())
    let readBranches ← mkStructMemberReadBranches fields false readFallback
    let writeBranches ← mkStructMemberWriteBranches fields false writeFallback
    cmds := cmds.push (← `(command|
      def structMember {κ α : Type} [Inhabited α] [_root_.Contracts.StorageKey κ]
          [_root_.Contracts.StorageWord α] (field : String) (key : κ) (member : String) :
          Verity.Contract α :=
        $readBranches))
    cmds := cmds.push (← `(command|
      def setStructMember {κ α : Type} [_root_.Contracts.StorageKey κ]
          [_root_.Contracts.StorageWord α] (field : String) (key : κ) (member : String)
          (value : α) : Verity.Contract Unit :=
        $writeBranches))
  if hasStructMapping2 fields then
    let readFallback : Term ← `(pure default)
    let writeFallback : Term ← `(pure ())
    let readBranches ← mkStructMemberReadBranches fields true readFallback
    let writeBranches ← mkStructMemberWriteBranches fields true writeFallback
    cmds := cmds.push (← `(command|
      def structMember2 {κ₁ κ₂ α : Type} [Inhabited α] [_root_.Contracts.StorageKey κ₁]
          [_root_.Contracts.StorageKey κ₂] [_root_.Contracts.StorageWord α] (field : String)
          (key1 : κ₁) (key2 : κ₂) (member : String) : Verity.Contract α :=
        $readBranches))
    cmds := cmds.push (← `(command|
      def setStructMember2 {κ₁ κ₂ α : Type} [_root_.Contracts.StorageKey κ₁]
          [_root_.Contracts.StorageKey κ₂] [_root_.Contracts.StorageWord α] (field : String)
          (key1 : κ₁) (key2 : κ₂) (member : String) (value : α) : Verity.Contract Unit :=
        $writeBranches))
  pure cmds

private def mkModelFieldTerm (field : StorageFieldDecl) : CommandElabM Term := do
  `(Compiler.CompilationModel.Field.mk
      $(strTerm field.name)
      $(← modelFieldTypeTerm field.ty)
      (some $(natTerm field.slotNum))
      none
      [])

private def mkModelErrorTerm (err : ErrorDecl) : CommandElabM Term := do
  let paramTerms ← err.params.mapM modelParamTypeTerm
  `(Compiler.CompilationModel.ErrorDef.mk
      $(strTerm err.name)
      [ $[$paramTerms],* ])

private def mkModelExternalTerm (ext : ExternalDecl) : CommandElabM Term := do
  let paramTerms ← ext.params.mapM modelParamTypeTerm
  let returnTerms ← ext.returnTys.mapM modelParamTypeTerm
  let returnTypeTerm ←
    match ext.returnTys.toList with
    | [] => `(none)
    | [retTy] => `(some $(← modelParamTypeTerm retTy))
    | _ => `(none)
  `(Compiler.CompilationModel.ExternalFunction.mk
      $(strTerm ext.name)
      [ $[$paramTerms],* ]
      $returnTypeTerm
      [ $[$returnTerms],* ]
      Compiler.ProofStatus.assumed
      [])

private def mkModelLocalObligationTerm (obligation : LocalObligationDecl) : CommandElabM Term := do
  let proofStatusTerm ←
    match obligation.proofStatus with
    | .proved => `(Compiler.ProofStatus.proved)
    | .assumed => `(Compiler.ProofStatus.assumed)
    | .unchecked => `(Compiler.ProofStatus.unchecked)
  `(Compiler.CompilationModel.LocalObligation.mk
      $(strTerm obligation.name)
      $(strTerm obligation.obligation)
      $proofStatusTerm)

private def mkAdtVariantTerm (variant : AdtVariantDecl) (tag : Nat) : CommandElabM Term := do
  let fieldTerms ← variant.fields.mapM fun p => do
    let tyTerm ← modelParamTypeTerm p.ty
    `(Compiler.CompilationModel.Param.mk $(strTerm p.name) $tyTerm)
  `(Compiler.CompilationModel.AdtVariant.mk
      $(strTerm variant.name)
      $(natTerm tag)
      [ $[$fieldTerms],* ])

private def mkAdtTypeDefTerm (adtDecl : AdtDecl) : CommandElabM Term := do
  let mut variantTerms : Array Term := #[]
  for (variant, idx) in adtDecl.variants.zipIdx do
    variantTerms := variantTerms.push (← mkAdtVariantTerm variant idx)
  `(Compiler.CompilationModel.AdtTypeDef.mk
      $(strTerm adtDecl.name)
      [ $[$variantTerms],* ])

private partial def collectQualifiedFunctionAppsFromSyntax (stx : Syntax) : Array Name :=
  let fromChildren : Array Name :=
    match stx with
    | .node _ _ args =>
        args.foldl (fun acc child => acc ++ collectQualifiedFunctionAppsFromSyntax child) #[]
    | _ => #[]
  match stx with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ _ raw _ =>
          if isQualifiedFunctionName raw && (nameComponents raw).head? != some "Verity" then
            fromChildren.push raw
          else
            fromChildren
      | _ => fromChildren
  | _ => fromChildren

private def uniqueNames (names : Array Name) : Array Name :=
  names.foldl
    (fun acc name => if acc.any (· == name) then acc else acc.push name)
    #[]

private def collectQualifiedFunctionAppsFromFunction (fn : FunctionDecl) : Array Name :=
  collectQualifiedFunctionAppsFromSyntax fn.body.raw

private def collectQualifiedFunctionAppsFromConstructor (ctor : ConstructorDecl) : Array Name :=
  collectQualifiedFunctionAppsFromSyntax ctor.body.raw

private def mkQualifiedInternalFunctionTerm
    (usedNames : List String)
    (name : Name) : CommandElabM Term := do
  let modelIdent : Ident := mkIdent (qualifiedFunctionModelName name)
  `(({ $modelIdent with
        name := $(strTerm (qualifiedInternalHelperNameFromUsed usedNames name))
        isInternal := true } : Compiler.CompilationModel.FunctionSpec))

private def mkSpecCommand
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl)
    (adtDecls : Array AdtDecl)
    (storageNamespace : Option Nat) : CommandElabM Cmd := do
  let immutableFields := immutableDecls.zipIdx.map (fun (imm, idx) => immutableStorageFieldDecl fields imm idx)
  let allFields := fields ++ immutableFields
  let fieldTerms ← allFields.mapM mkModelFieldTerm
  let errorTerms ← errorDecls.mapM mkModelErrorTerm
  let externalTerms ← externalDecls.mapM mkModelExternalTerm
  let constructorTerm ←
    match ctor, immutableDecls.isEmpty with
    | none, true => `(none)
    | some ctor, _ =>
        let ctorParams ← mkModelParamsTerm ctor.params
        let ctorPayable ← if ctor.isPayable then `(true) else `(false)
        let ctorLocalObligationTerms ← ctor.localObligations.mapM mkModelLocalObligationTerm
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls ctor.params
        let ctorBodyTerms ← translateConstructorBodyToStmtTerms fields constDecls immutableDecls externalDecls functions ctor
        let ctorAllTerms := immutableInitTerms ++ ctorBodyTerms
        `(some {
          params := $ctorParams
          isPayable := $ctorPayable
          localObligations := [ $[$ctorLocalObligationTerms],* ]
          body := [ $[$ctorAllTerms],* ]
        })
    | none, false =>
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls #[]
        `(some {
          params := []
          isPayable := false
          localObligations := []
          body := [ $[$immutableInitTerms],* ]
        })
  let functionModelIds ← functions.mapM fun fn => mkSuffixedIdent fn.ident "_model"
  let internalFunctionTerms ← functions.filterMapM fun fn => do
    if supportsInternalHelperSpec fn then
      let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
      let modelParams ← mkModelParamsTerm fn.params
      let localObligationTerms ← fn.localObligations.mapM mkModelLocalObligationTerm
      let payableTerm ← if fn.isPayable then `(true) else `(false)
      let viewTerm ← if fn.isView then `(true) else `(false)
      let noExternalCallsTerm ← if fn.noExternalCalls then `(true) else `(false)
      let allowPostInteractionWritesTerm ← if fn.allowPostInteractionWrites then `(true) else `(false)
      let nonReentrantLockTerm ← match fn.nonReentrantLock with
        | some lockIdent => `(some $(strTerm (toString lockIdent.getId)))
        | none => `(none)
      let ceiSafeTerm ← if fn.ceiSafe then `(true) else `(false)
      let requiresRoleTerm ← match fn.requiresRole with
        | some roleIdent => `(some $(strTerm (toString roleIdent.getId)))
        | none => `(none)
      let internalModifiesTerms : Array Term := fn.modifies.map fun ident => strTerm (toString ident.getId)
      let returnTypeTerm ← modelReturnTypeTerm fn.returnTy
      let returnsTerm ← modelReturnsTerm fn.returnTy
      pure <| some (← `( ({
        name := $(strTerm (internalHelperSpecNameFor fn))
        params := $modelParams
        returnType := $returnTypeTerm
        «returns» := $returnsTerm
        isPayable := $payableTerm
        isView := $viewTerm
        noExternalCalls := $noExternalCallsTerm
        allowPostInteractionWrites := $allowPostInteractionWritesTerm
        nonReentrantLock := $nonReentrantLockTerm
        ceiSafe := $ceiSafeTerm
        requiresRole := $requiresRoleTerm
        modifies := [ $[$internalModifiesTerms],* ]
        localObligations := [ $[$localObligationTerms],* ]
        body := $modelBodyName
        isInternal := true
      } : Compiler.CompilationModel.FunctionSpec) ))
    else
      pure none
  let qualifiedFunctionNames :=
    uniqueNames <|
      (functions.foldl (fun acc fn => acc ++ collectQualifiedFunctionAppsFromFunction fn) #[]) ++
      (match ctor with
      | some ctorDecl => collectQualifiedFunctionAppsFromConstructor ctorDecl
      | none => #[])
  let localInternalFunctionNames := (functions.map internalHelperSpecNameFor).toList
  let qualifiedInternalFunctionTerms ←
    qualifiedFunctionNames.mapM (mkQualifiedInternalFunctionTerm localInternalFunctionNames)
  let adtTypeTerms ← adtDecls.mapM mkAdtTypeDefTerm
  let functionModelTerms : Array Term := functionModelIds.map fun id => ⟨id.raw⟩
  let allFunctionTerms := functionModelTerms ++ internalFunctionTerms ++ qualifiedInternalFunctionTerms
  let namespaceTerm ← match storageNamespace with
    | some ns => `(some $(natTerm ns))
    | none => `(none)
  `(command| def spec : Compiler.CompilationModel.CompilationModel := {
    name := $(strTerm contractName)
    fields := [ $[$fieldTerms],* ]
    «errors» := [ $[$errorTerms],* ]
    «constructor» := $constructorTerm
    functions := [ $[$allFunctionTerms],* ]
    «externals» := [ $[$externalTerms],* ]
    adtTypes := [ $[$adtTypeTerms],* ]
    storageNamespace := $namespaceTerm
  })

private def mkFindIdxFieldSimpCommands
    (contractIdent : Ident)
    (fields : Array StorageFieldDecl) : CommandElabM (Array Cmd) := do
  let contractName := toString contractIdent.getId
  let fieldTerms ← fields.mapM mkModelFieldTerm
  let fieldListTerm : Term ← `(([ $[$fieldTerms],* ] : List Compiler.CompilationModel.Field))
  let mut cmds : Array Cmd := #[]
  let mut idx := 0
  for field in fields do
    let baseName := s!"findIdx_{field.name}_{contractName}"
    let theoremName := mkIdent (Name.mkSimple baseName)
    let theoremNameDecide := mkIdent (Name.mkSimple (baseName ++ "_decide"))
    let idxTerm := natTerm idx
    let fieldNameTerm := strTerm field.name

    let eqCmd : Cmd ← `(command|
      @[simp] theorem $theoremName :
          List.findIdx? (fun x : Compiler.CompilationModel.Field => x.name == $fieldNameTerm)
            $fieldListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push eqCmd

    let decideCmd : Cmd ← `(command|
      @[simp] theorem $theoremNameDecide :
          List.findIdx? (fun x : Compiler.CompilationModel.Field => decide (x.name = $fieldNameTerm))
            $fieldListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push decideCmd
    idx := idx + 1
  pure cmds

private def mkFindIdxParamSimpCommandsForScope
    (contractName : String)
    (scopeName : String)
    (params : Array ParamDecl) : CommandElabM (Array Cmd) := do
  let paramNameTerms : Array Term := params.map (fun p => strTerm p.name)
  let paramListTerm : Term ← `(([ $[$paramNameTerms],* ] : List String))
  let mut cmds : Array Cmd := #[]
  let mut idx := 0
  for param in params do
    let baseName := s!"findIdx_param_{param.name}_{scopeName}_{contractName}"
    let theoremName := mkIdent (Name.mkSimple baseName)
    let theoremNameDecide := mkIdent (Name.mkSimple (baseName ++ "_decide"))
    let idxTerm := natTerm idx
    let paramNameTerm := strTerm param.name

    let eqCmd : Cmd ← `(command|
      @[simp] theorem $theoremName :
          List.findIdx? (fun x => x == $paramNameTerm)
            $paramListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push eqCmd

    let decideCmd : Cmd ← `(command|
      @[simp] theorem $theoremNameDecide :
          List.findIdx? (fun x => decide (x = $paramNameTerm))
            $paramListTerm = some $idxTerm := by
        decide)
    cmds := cmds.push decideCmd
    idx := idx + 1
  pure cmds

private def mkFindIdxParamSimpCommands
    (contractIdent : Ident)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM (Array Cmd) := do
  let contractName := toString contractIdent.getId
  let mut cmds : Array Cmd := #[]
  match ctor with
  | some ctorDecl =>
      let ctorCmds ← mkFindIdxParamSimpCommandsForScope contractName "constructor" ctorDecl.params
      cmds := cmds ++ ctorCmds
  | none => pure ()
  for fn in functions do
    let fnCmds ← mkFindIdxParamSimpCommandsForScope contractName (toString fn.ident.getId) fn.params
    cmds := cmds ++ fnCmds
  pure cmds

/-- Convert a big-endian `ByteArray` to a `Nat`, treating byte 0 as most
    significant.  Used for storage namespace computation (#1730, Axis 4). -/
private def byteArrayToNatBE (ba : ByteArray) : Nat :=
  ba.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Compute the storage namespace for a contract.
    `storageNamespace("Foo") = keccak256("Foo.storage.v0")` as a 256-bit Nat.
    The result can be used as a base offset so different contracts never collide
    in the shared 2^256 storage address space.
    (#1730, Axis 4 Step 4a) -/
def computeStorageNamespace (contractName : String) : Nat :=
  byteArrayToNatBE (KeccakEngine.keccak256_str s!"{contractName}.storage.v0")

/-- Compute a storage namespace from an explicit user-provided namespace key. -/
def computeStorageNamespaceKey (key : String) : Nat :=
  byteArrayToNatBE (KeccakEngine.keccak256_str key)

def parseContractSyntax
    (stx : Syntax)
    : CommandElabM
        (Ident × Array NewtypeDecl × Array StructDecl × Array AdtDecl × Array StorageFieldDecl × Array ErrorDecl × Array ConstantDecl × Array ImmutableDecl × Array ExternalDecl × Option ConstructorDecl × Array FunctionDecl × Option Nat) := do
  match stx with
  | `(command| verity_contract $contractName:ident where $[types $[$newtypeDecls:verityNewtype]*]? $[inductive $[$adtDecls:verityAdtDecl]*]? $[$nsSpec:verityNamespaceSpec]? storage $[$storageFields:verityStorageField]* $[$structDecls:verityStructDecl]* $[errors $[$errorDecls:verityError]*]? $[constants $[$constantDecls:verityConstant]*]? $[immutables $[$immutableDecls:verityImmutable]*]? $[linked_externals $[$externalDecls:verityExternal]*]? $[$ctor:verityConstructor]? $[$entrypoints:veritySpecialEntrypoint]* $[$functions:verityFunction]*) =>
      -- Parse newtypes first — they are needed by all downstream type resolution
      let parsedNewtypes ←
        match newtypeDecls with
        | some decls => decls.mapM parseNewtype
        | none => pure #[]
      -- Validate: no duplicate type names
      let mut seenNames : Array String := #[]
      for nt in parsedNewtypes do
        if seenNames.contains nt.name then
          throwErrorAt nt.ident s!"duplicate type name '{nt.name}'"
        seenNames := seenNames.push nt.name
      -- Validate: type names don't shadow built-in types
      let builtinTypeNames := #["Uint256", "Int256", "Uint8", "Address", "Bytes32", "Bool", "String", "Bytes", "Unit", "Array", "Tuple"]
      for nt in parsedNewtypes do
        if builtinTypeNames.contains nt.name then
          throwErrorAt nt.ident s!"type name '{nt.name}' shadows a built-in type"
      let mut parsedStructs : Array StructDecl := #[]
      for structStx in structDecls do
        let parsedStruct ← parseStructDecl parsedNewtypes parsedStructs structStx
        if seenNames.contains parsedStruct.name then
          throwErrorAt parsedStruct.ident s!"duplicate type name '{parsedStruct.name}'"
        if builtinTypeNames.contains parsedStruct.name then
          throwErrorAt parsedStruct.ident s!"struct name '{parsedStruct.name}' shadows a built-in type"
        seenNames := seenNames.push parsedStruct.name
        parsedStructs := parsedStructs.push parsedStruct
      -- Parse ADT declarations (#1727, Axis 1 Step 5a)
      let parsedAdts ←
        match adtDecls with
        | some decls => decls.mapM (parseAdtDecl parsedNewtypes)
        | none => pure #[]
      -- Validate: no duplicate ADT names
      for adtDecl in parsedAdts do
        if seenNames.contains adtDecl.name then
          throwErrorAt adtDecl.ident s!"duplicate type name '{adtDecl.name}'"
        seenNames := seenNames.push adtDecl.name
      -- Validate: ADT names don't shadow built-in types
      for adtDecl in parsedAdts do
        if builtinTypeNames.contains adtDecl.name then
          throwErrorAt adtDecl.ident s!"ADT name '{adtDecl.name}' shadows a built-in type"
      -- Compute namespace offset (#1730, Axis 4 Steps 4b/4c): when `storage_namespace`
      -- is present, every user-declared slot N becomes (namespaceBase + N).
      -- With `storage_namespace "custom"`, the custom string replaces the default
      -- "{ContractName}.storage.v0" key.
      let namespaceOffset : Nat ←
        match nsSpec with
        | some spec =>
            -- `storage_namespace` alone → default; `storage_namespace "key"` → custom.
            -- Match the syntax category directly so the custom string is not lost
            -- behind parser wrapper nodes.
            match spec with
            | `(verityNamespaceSpec| storage_namespace $customKey:str) =>
                match customKey.raw.isStrLit? with
                | some key => pure (computeStorageNamespaceKey key)
                | none => throwErrorAt customKey "expected storage namespace string literal"
            | `(verityNamespaceSpec| storage_namespace) =>
                pure (computeStorageNamespace (toString contractName.getId))
            | _ =>
                throwErrorAt spec "unsupported storage namespace syntax"
        | none => pure 0
      let parsedErrors ←
        match errorDecls with
        | some decls => decls.mapM (parseError parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      let parsedConstants ←
        match constantDecls with
        | some decls => decls.mapM (parseConstant parsedNewtypes)
        | none => pure #[]
      let parsedImmutables ←
        match immutableDecls with
        | some decls => decls.mapM (parseImmutable parsedNewtypes)
        | none => pure #[]
      let parsedExternals ←
        match externalDecls with
        | some decls => decls.mapM (parseExternal parsedNewtypes parsedStructs parsedAdts)
        | none => pure #[]
      -- Apply namespace offset to parsed storage fields (#1730, Axis 4 Step 4b)
      let parsedFields ← storageFields.mapM (parseStorageField parsedNewtypes parsedStructs parsedAdts)
      let parsedFields := parsedFields.map fun field =>
        { field with slotNum := field.slotNum + namespaceOffset }
      -- Compute the Option Nat for the spec's storageNamespace field (#1730, Axis 4 Step 4d)
      let namespaceOpt : Option Nat :=
        if nsSpec.isSome then some namespaceOffset else none
      pure
        ( contractName
        , parsedNewtypes
        , parsedStructs
        , parsedAdts
        , parsedFields
        , parsedErrors
        , parsedConstants
        , parsedImmutables
        , parsedExternals
        , (← ctor.mapM (parseConstructor parsedNewtypes parsedStructs parsedAdts))
          , assignOverloadInternalIdents
              ((← entrypoints.mapM parseSpecialEntrypoint) ++
                (← functions.mapM (parseFunction parsedNewtypes parsedStructs parsedAdts)))
          , namespaceOpt
          )
  | _ => throwErrorAt stx "invalid verity_contract declaration"

private def mkConstantDefCommand (constant : ConstantDecl) : CommandElabM Cmd := do
  `(command| def $constant.ident : $(← contractValueTypeTerm constant.ty) := $constant.body)

def mkStorageDefCommandPublic (field : StorageFieldDecl) : CommandElabM Cmd :=
  mkStorageDefCommand field

def mkConstantDefCommandPublic (constant : ConstantDecl) : CommandElabM Cmd :=
  mkConstantDefCommand constant

def mkStructDefCommandPublic (decl : StructDecl) : CommandElabM Cmd := do
  let structId := decl.ident
  let fieldIds := decl.fields.map (·.ident)
  let fieldTys ← decl.fields.mapM (fun field => contractValueTypeTerm field.ty)
  `(command| structure $structId where
      $[$fieldIds:ident : $fieldTys:term]*
      deriving Repr, Inhabited)

/-- Generate a `def storageNamespace : Nat := <keccak-value>` command for
    the current contract.  Uses the resolved namespace value from
    `parseContractSyntax` to respect custom `storage_namespace "key"`.
    (#1730, Axis 4 Step 4a) -/
def mkStorageNamespaceCommand (contractName : String) (resolvedNamespace : Option Nat := none) : CommandElabM Cmd := do
  let _ := contractName
  let ns := resolvedNamespace.getD 0
  let id : Ident := mkIdent (Name.mkSimple "storageNamespace")
  `(command| def $id : Nat := $(natTerm ns))

def validateConstantDeclsPublic (constDecls : Array ConstantDecl) : CommandElabM Unit := do
  for constant in constDecls do
    validateConstantBody constDecls constant.body [constant.name]
  validateConstantExprTypes constDecls

def validateGeneratedDefNamesPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (functions : Array FunctionDecl) : CommandElabM Unit := do
  let reservedGeneratedNames : Array String := #["spec", "storageNamespace"]
  let mut generatedHelperNames : Array String := reservedGeneratedNames
  if hasStructMapping fields then
    generatedHelperNames := generatedHelperNames.push "structMember"
    generatedHelperNames := generatedHelperNames.push "setStructMember"
  if hasStructMapping2 fields then
    generatedHelperNames := generatedHelperNames.push "structMember2"
    generatedHelperNames := generatedHelperNames.push "setStructMember2"

  let mut storageNames : Array String := #[]
  for field in fields do
    if generatedHelperNames.contains field.name then
      throwErrorAt field.ident
        s!"storage field '{field.name}' conflicts with reserved generated declaration '{field.name}'"
    if storageNames.contains field.name then
      throwErrorAt field.ident s!"duplicate storage field declaration '{field.name}'"
    storageNames := storageNames.push field.name

  let mut constantNames : Array String := #[]
  for constant in constDecls do
    if generatedHelperNames.contains constant.name then
      throwErrorAt constant.ident
        s!"constant '{constant.name}' conflicts with reserved generated declaration '{constant.name}'"
    if storageNames.contains constant.name then
      throwErrorAt constant.ident
        s!"constant '{constant.name}' conflicts with a storage field of the same name"
    if constantNames.contains constant.name then
      throwErrorAt constant.ident
        s!"duplicate constant declaration '{constant.name}'"
    constantNames := constantNames.push constant.name

  let mut immutableNames : Array String := #[]
  for imm in immutableDecls do
    if generatedHelperNames.contains imm.name then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with reserved generated declaration '{imm.name}'"
    immutableNames := immutableNames.push imm.name

  let mut functionNames : Array String := #[]
  let mut functionSignatures : Array String := #[]
  let mut functionAbiSignatures : Array String := #[]
  for fn in functions do
    let generatedFnName := toString fn.ident.getId
    let signature := functionSignatureKey fn
    let abiSignature := functionAbiSignatureKey fn
    if generatedHelperNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with reserved generated declaration '{fn.name}'"
    if storageNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with a storage field of the same name"
    if constantNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with a contract constant of the same name"
    if immutableNames.contains fn.name then
      throwErrorAt fn.ident
        s!"function '{fn.name}' conflicts with an immutable of the same name"
    if storageNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with a storage field of the same name"
    if constantNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with a contract constant of the same name"
    if immutableNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with an immutable of the same name"
    if generatedHelperNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates internal declaration '{generatedFnName}' that conflicts with reserved generated declaration '{generatedFnName}'"
    if functionSignatures.contains signature then
      throwErrorAt fn.ident
        s!"duplicate function declaration '{signature}'"
    if functionAbiSignatures.contains abiSignature then
      throwErrorAt fn.ident
        s!"duplicate function ABI signature '{abiSignature}' after ABI erasure"
    if functionNames.contains generatedFnName then
      throwErrorAt fn.ident
        s!"function '{fn.name}' generates duplicate internal declaration '{generatedFnName}'"
    functionNames := functionNames.push generatedFnName
    functionSignatures := functionSignatures.push signature
    functionAbiSignatures := functionAbiSignatures.push abiSignature

    let helperNames :=
      #[ s!"{generatedFnName}_modelBody"
       , s!"{generatedFnName}_model"
       , s!"{generatedFnName}_bridge"
       , s!"{generatedFnName}_semantic_preservation"
       , s!"{generatedFnName}_is_view"
       , s!"{generatedFnName}_no_calls"
       , s!"{generatedFnName}_modifies"
       , s!"{generatedFnName}_frame"
       , s!"{generatedFnName}_frame_rfl"
       , s!"{generatedFnName}_effects"
       , s!"{generatedFnName}_cei_compliant"
       , s!"{generatedFnName}_nonreentrant"
       , s!"{generatedFnName}_cei_safe"
       , s!"{generatedFnName}_requires_role"
       ]
    for helperName in helperNames do
      if storageNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a storage field of the same name"
      if constantNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a contract constant of the same name"
      if immutableNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with an immutable of the same name"
      if functionNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates helper '{helperName}' that conflicts with a function of the same name"
      if generatedHelperNames.contains helperName then
        throwErrorAt fn.ident
          s!"function '{fn.name}' generates duplicate helper declaration '{helperName}'"
      generatedHelperNames := generatedHelperNames.push helperName

def validateImmutableDeclsPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (ctor : Option ConstructorDecl := none) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  let ctorParams := ctor.map (·.params) |>.getD #[]
  for imm in immutableDecls do
    validateImmutableType imm
    let inferredTy ← inferPureExprType fields constDecls #[] #[] ctorParams #[] imm.body
    requireDeclaredValueType imm.body s!"immutable '{imm.name}'" imm.ty inferredTy
    if fields.any (fun field => field.name == imm.name) then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with a storage field of the same name"
    if constDecls.any (fun constant => constant.name == imm.name) then
      throwErrorAt imm.ident
        s!"immutable '{imm.name}' conflicts with a contract constant of the same name"
    if seenNames.contains imm.name then
      throwErrorAt imm.ident
        s!"duplicate immutable declaration '{imm.name}'"
    seenNames := seenNames.push imm.name

def validateExternalDeclsPublic
    (externalDecls : Array ExternalDecl) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  for ext in externalDecls do
    if seenNames.contains ext.name then
      throwErrorAt ext.ident
        s!"duplicate external declaration '{ext.name}'"
    -- Multi-return externals are allowed; the auto-revert expression form (externalCall)
    -- only supports single-return, but tryExternalCall supports any return count.
    -- (#1727, Axis 1 Step 5f)
    for paramTy in ext.params do
      validateExternalExecutableType ext.ident ext.name paramTy "parameter"
    for returnTy in ext.returnTys do
      validateExternalExecutableType ext.ident ext.name returnTy "return"
    seenNames := seenNames.push ext.name

private def validateLocalObligationDecls
    (owner : String)
    (obligations : Array LocalObligationDecl) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  for obligation in obligations do
    if obligation.obligation.isEmpty then
      throwErrorAt obligation.ident
        s!"{owner} local obligation '{obligation.name}' must not be empty"
    if seenNames.contains obligation.name then
      throwErrorAt obligation.ident
        s!"duplicate local obligation '{obligation.name}' on {owner}"
    seenNames := seenNames.push obligation.name

def validateFunctionDeclsPublic
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM Unit := do
  match ctor with
  | some ctor =>
      for param in ctor.params do
        rejectExecutableBoundaryAdt param.ident s!"constructor parameter '{param.name}'" param.ty
      validateLocalObligationDecls "constructor" ctor.localObligations
      validateConstructorBodyExprTypes fields errorDecls constDecls immutableDecls externalDecls functions ctor
  | none => pure ()
  for fn in functions do
    for param in fn.params do
      rejectExecutableBoundaryAdt param.ident s!"function '{fn.name}' parameter '{param.name}'" param.ty
    rejectExecutableBoundaryAdt fn.ident s!"function '{fn.name}' return type" fn.returnTy
    validateLocalObligationDecls s!"function '{fn.name}'" fn.localObligations
    -- Validate modifies field names exist in the storage section
    for modField in fn.modifies do
      let modName := toString modField.getId
      let allFieldNames := fields.map (·.name)
      if !allFieldNames.contains modName then
        throwErrorAt modField s!"function '{fn.name}': modifies references unknown storage field '{modName}'; known fields: {allFieldNames.toList}"
    -- view functions must not use modifies (they already imply no writes)
    if fn.isView && !fn.modifies.isEmpty then
      throwErrorAt fn.ident s!"function '{fn.name}' is marked view and modifies(...); view already guarantees no state writes"
    -- Validate nonreentrant lock field references a valid storage field of scalar uint256 type
    match fn.nonReentrantLock with
    | some lockField =>
        let lockName := toString lockField.getId
        let allFieldNames := fields.map (·.name)
        match fields.find? (fun field => field.name == lockName) with
        | none =>
          throwErrorAt lockField s!"function '{fn.name}': nonreentrant references unknown storage field '{lockName}'; known fields: {allFieldNames.toList}"
        | some field =>
            match field.ty with
            | .scalar .uint256 => pure ()
            | _ =>
                throwErrorAt lockField s!"function '{fn.name}': nonreentrant lock field '{lockName}' must be a scalar Uint256 storage field"
    | none => pure ()
    -- cei_safe and allow_post_interaction_writes are mutually exclusive with nonreentrant
    if fn.ceiSafe && fn.allowPostInteractionWrites then
      throwErrorAt fn.ident s!"function '{fn.name}': cei_safe and allow_post_interaction_writes are mutually exclusive"
    if fn.nonReentrantLock.isSome && fn.allowPostInteractionWrites then
      throwErrorAt fn.ident s!"function '{fn.name}': nonreentrant and allow_post_interaction_writes are mutually exclusive"
    if fn.nonReentrantLock.isSome && fn.ceiSafe then
      throwErrorAt fn.ident s!"function '{fn.name}': nonreentrant and cei_safe are mutually exclusive"
    validateFunctionBodyExprTypes fields errorDecls constDecls immutableDecls externalDecls functions fn

def mkFunctionCommandsPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (functions : Array FunctionDecl)
    (fn : FunctionDecl) : CommandElabM (Array Cmd) := do
  let fnType ← mkContractFnType fn.params fn.returnTy
  let fnRoleGuardedBody ← mkRoleGuardedBody fields fn
  let fnDecl := { fn with body := fnRoleGuardedBody }
  let fnGuardedBody ← mkInitGuardedBody fields fnDecl
  let fnBody ← mkImmutableBoundBody fields immutableDecls fn fnGuardedBody
  let fnValue ← mkContractFnValue fn.params fnBody
  let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
  let modelName ← mkSuffixedIdent fn.ident "_model"
  let stmtTerms ← translateBodyToStmtTerms fields constDecls immutableDecls externalDecls functions fn
  let modelParams ← mkModelParamsTerm fn.params
  let localObligationTerms ← fn.localObligations.mapM mkModelLocalObligationTerm
  let payableTerm ← if fn.isPayable then `(true) else `(false)
  let viewTerm ← if fn.isView then `(true) else `(false)
  let noExternalCallsTerm ← if fn.noExternalCalls then `(true) else `(false)
  let allowPostInteractionWritesTerm ← if fn.allowPostInteractionWrites then `(true) else `(false)
  let nonReentrantLockTerm ← match fn.nonReentrantLock with
    | some lockIdent => `(some $(strTerm (toString lockIdent.getId)))
    | none => `(none)
  let ceiSafeTerm ← if fn.ceiSafe then `(true) else `(false)
  let requiresRoleTerm ← match fn.requiresRole with
    | some roleIdent => `(some $(strTerm (toString roleIdent.getId)))
    | none => `(none)
  let modifiesTerms : Array Term := fn.modifies.map fun ident => strTerm (toString ident.getId)
  let returnTypeTerm ← modelReturnTypeTerm fn.returnTy
  let returnsTerm ← modelReturnsTerm fn.returnTy

  let fnCmd : Cmd ← `(command| def $fn.ident : $fnType := $fnValue)
  let bodyCmd : Cmd ← `(command| def $modelBodyName : List Compiler.CompilationModel.Stmt := [ $[$stmtTerms],* ])
  let modelCmd : Cmd ← `(command| def $modelName : Compiler.CompilationModel.FunctionSpec := {
    name := $(strTerm fn.name)
    params := $modelParams
    returnType := $returnTypeTerm
    «returns» := $returnsTerm
    isPayable := $payableTerm
    isView := $viewTerm
    noExternalCalls := $noExternalCallsTerm
    allowPostInteractionWrites := $allowPostInteractionWritesTerm
    nonReentrantLock := $nonReentrantLockTerm
    ceiSafe := $ceiSafeTerm
    requiresRole := $requiresRoleTerm
    modifies := [ $[$modifiesTerms],* ]
    localObligations := [ $[$localObligationTerms],* ]
    body := $modelBodyName
  })
  pure #[fnCmd, bodyCmd, modelCmd]

def mkSpecCommandPublic
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl)
    (adtDecls : Array AdtDecl)
    (storageNamespace : Option Nat) : CommandElabM Cmd :=
  mkSpecCommand contractName fields errorDecls constDecls immutableDecls externalDecls ctor functions adtDecls storageNamespace

def mkFindIdxFieldSimpCommandsPublic
    (contractIdent : Ident)
    (fields : Array StorageFieldDecl) : CommandElabM (Array Cmd) :=
  mkFindIdxFieldSimpCommands contractIdent fields

def mkFindIdxParamSimpCommandsPublic
    (contractIdent : Ident)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM (Array Cmd) :=
  mkFindIdxParamSimpCommands contractIdent ctor functions

/-- Public wrapper for `contractValueTypeTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def contractValueTypeTermPublic (ty : ValueType) : CommandElabM Term :=
  contractValueTypeTerm ty

/-- Public wrapper for `strTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def strTermPublic (s : String) : Term := strTerm s

/-- Public wrapper for `natTerm`, used by the semantic bridge
    theorem generator in `Bridge.lean` (Issue #998). -/
def natTermPublic (n : Nat) : Term := natTerm n

end Verity.Macro
