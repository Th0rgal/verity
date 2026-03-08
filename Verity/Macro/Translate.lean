import Lean
import Compiler.Modules.Precompiles
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
  | uint8
  | address
  | bytes32
  | bool
  | string
  | bytes
  | array (elemTy : ValueType)
  | tuple (elemTys : List ValueType)
  | unit
  deriving BEq

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
  | mappingAddressToUint256
  | mapping2AddressToAddressToUint256
  | mappingUintToUint256
  | mappingStruct (keyType : MappingKeyType) (members : List StructMemberDecl)
  | mappingStruct2 (outerKey : MappingKeyType) (innerKey : MappingKeyType) (members : List StructMemberDecl)
  deriving BEq

structure StorageFieldDecl where
  ident : Ident
  name : String
  ty : StorageType
  slotNum : Nat

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

inductive InitGuardDecl where
  | initializer (fieldIdent : Ident) (fieldName : String)
  | reinitializer (fieldIdent : Ident) (fieldName : String) (version : Nat)

structure FunctionDecl where
  ident : Ident
  name : String
  params : Array ParamDecl
  returnTy : ValueType
  initGuard? : Option InitGuardDecl := none
  body : Term

structure ConstructorDecl where
  params : Array ParamDecl
  isPayable : Bool := false
  body : Term

private def strTerm (s : String) : Term := ⟨Syntax.mkStrLit s⟩
private def natTerm (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩

private def natFromSyntax (stx : Syntax) : CommandElabM Nat :=
  match stx.isNatLit? with
  | some n => pure n
  | none => throwErrorAt stx "expected natural literal"

private partial def valueTypeFromSyntax (ty : Term) : CommandElabM ValueType := do
  match ty with
  | `(term| Uint256) => pure .uint256
  | `(term| Uint8) => pure .uint8
  | `(term| Address) => pure .address
  | `(term| Bytes32) => pure .bytes32
  | `(term| Bool) => pure .bool
  | `(term| String) => pure .string
  | `(term| Bytes) => pure .bytes
  | `(term| Array $elemTy:term) =>
      let elem ← valueTypeFromSyntax elemTy
      match elem with
      | .unit => throwErrorAt ty "unsupported type '{ty}'; Array Unit is not allowed"
      | .array _ => throwErrorAt ty "unsupported type '{ty}'; nested arrays are not supported"
      | _ => pure (.array elem)
  | `(term| Tuple [ $[$elemTys:term],* ]) =>
      let elems ← elemTys.mapM valueTypeFromSyntax
      if elems.size < 2 then
        throwErrorAt ty "tuple types must have at least 2 elements"
      pure (.tuple elems.toList)
  | `(term| Unit) => pure .unit
  | _ => throwErrorAt ty "unsupported type '{ty}'; expected Uint256, Uint8, Address, Bytes32, Bool, String, Bytes, Array <type>, Tuple [...], or Unit"

private def storageTypeFromSyntax (ty : Term) : CommandElabM StorageType := do
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
  | `(term| Address → Uint256) => pure .mappingAddressToUint256
  | `(term| Address → Address → Uint256) => pure .mapping2AddressToAddressToUint256
  | `(term| Uint256 → Uint256) => pure .mappingUintToUint256
  | _ => do
      let vt ← valueTypeFromSyntax ty
      match vt with
      | .tuple _ => throwErrorAt ty "storage fields cannot be Tuple; use mapping encodings"
      | _ => pure (.scalar vt)

private def modelMappingKeyTypeTerm : MappingKeyType → CommandElabM Term
  | .address => `(Compiler.CompilationModel.MappingKeyType.address)
  | .uint256 => `(Compiler.CompilationModel.MappingKeyType.uint256)

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
  | .scalar .uint8 => throwError "storage fields cannot be Uint8; use Uint256 encoding"
  | .scalar .address => `(Compiler.CompilationModel.FieldType.address)
  | .scalar .bytes32 => throwError "storage fields cannot be Bytes32; use Uint256 encoding"
  | .scalar .bool => throwError "storage fields cannot be Bool; use Uint256 (0/1) encoding"
  | .scalar .string => throwError "storage fields cannot be String; use Uint256 encoding"
  | .scalar .bytes => throwError "storage fields cannot be Bytes; use Uint256 encoding"
  | .scalar (.array _) => throwError "storage fields cannot be Array; use mapping encodings"
  | .scalar (.tuple _) => throwError "storage fields cannot be Tuple; use mapping encodings"
  | .scalar .unit => throwError "storage fields cannot be Unit"
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
  | .unit => throwError "function parameters cannot be Unit"

private def modelReturnTypeTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `(none)
  | .uint256 => `(some Compiler.CompilationModel.FieldType.uint256)
  | .uint8 => `(none)
  | .address => `(some Compiler.CompilationModel.FieldType.address)
  | .bytes32 => `(none)
  | .bool => `(none)
  | .string => `(none)
  | .bytes => `(none)
  | .array _ => `(none)
  | .tuple _ => `(none)

private partial def modelReturnsTerm (ty : ValueType) : CommandElabM Term :=
  match ty with
  | .unit => `([])
  | .uint256 => `([Compiler.CompilationModel.ParamType.uint256])
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
end

private def parseStorageField (stx : Syntax) : CommandElabM StorageFieldDecl := do
  match stx with
  | `(verityStorageField| $name:ident : $ty:term := slot $slotNum:num) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← storageTypeFromSyntax ty
        slotNum := ← natFromSyntax slotNum
      }
  | _ => throwErrorAt stx "invalid storage field declaration"

private def parseParam (stx : Syntax) : CommandElabM ParamDecl := do
  match stx with
  | `(verityParam| $name:ident : $ty:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax ty
      }
  | _ => throwErrorAt stx "invalid parameter declaration"

private def parseError (stx : Syntax) : CommandElabM ErrorDecl := do
  match stx with
  | `(verityError| error $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM valueTypeFromSyntax
      }
  | _ => throwErrorAt stx "invalid custom error declaration"

private def parseConstant (stx : Syntax) : CommandElabM ConstantDecl := do
  match stx with
  | `(verityConstant| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax ty
        body := body
      }
  | _ => throwErrorAt stx "invalid constant declaration"

private def parseImmutable (stx : Syntax) : CommandElabM ImmutableDecl := do
  match stx with
  | `(verityImmutable| $name:ident : $ty:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        ty := ← valueTypeFromSyntax ty
        body := body
      }
  | _ => throwErrorAt stx "invalid immutable declaration"

private def parseExternal (stx : Syntax) : CommandElabM ExternalDecl := do
  match stx with
  | `(verityExternal| external $name:ident ($[$params:term],*) -> ($[$returnTys:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM valueTypeFromSyntax
        returnTys := ← returnTys.mapM valueTypeFromSyntax
      }
  | `(verityExternal| external $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM valueTypeFromSyntax
        returnTys := #[]
      }
  | _ => throwErrorAt stx "invalid external declaration"

private def parseFunction (stx : Syntax) : CommandElabM FunctionDecl := do
  match stx with
  | `(verityFunction| function $name:ident ($[$params:verityParam],*) initializer($field:ident) : $retTy:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM parseParam
        returnTy := ← valueTypeFromSyntax retTy
        initGuard? := some (.initializer field (toString field.getId))
        body := body
      }
  | `(verityFunction| function $name:ident ($[$params:verityParam],*) reinitializer($field:ident, $version:num) : $retTy:term := $body:term) => do
      let versionNat ← natFromSyntax version
      if versionNat == 0 then
        throwErrorAt version "reinitializer version must be greater than 0"
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM parseParam
        returnTy := ← valueTypeFromSyntax retTy
        initGuard? := some (.reinitializer field (toString field.getId) versionNat)
        body := body
      }
  | `(verityFunction| function $name:ident ($[$params:verityParam],*) : $retTy:term := $body:term) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM parseParam
        returnTy := ← valueTypeFromSyntax retTy
        body := body
      }
  | _ => throwErrorAt stx "invalid function declaration"

private def parseConstructor (stx : Syntax) : CommandElabM ConstructorDecl := do
  match stx with
  | `(verityConstructor| constructor ($[$params:verityParam],*) payable := $body:term) =>
      pure {
        params := ← params.mapM parseParam
        isPayable := true
        body := body
      }
  | `(verityConstructor| constructor ($[$params:verityParam],*) := $body:term) =>
      pure {
        params := ← params.mapM parseParam
        body := body
      }
  | _ => throwErrorAt stx "invalid constructor declaration"

private def immutableHiddenName (imm : ImmutableDecl) : String :=
  s!"__immutable_{imm.name}"

private def immutableSlotIndex (fields : Array StorageFieldDecl) (idx : Nat) : Nat :=
  let nextUserSlot := fields.foldl (fun maxSlot field => max maxSlot (field.slotNum + 1)) 0
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
      | .uint256 => .scalar .uint256
      | .address => .scalar .address
      | _ => .scalar imm.ty
    slotNum := immutableSlotIndex fields idx
  }

private def validateImmutableType (imm : ImmutableDecl) : CommandElabM Unit :=
  match imm.ty with
  | .uint256 | .address => pure ()
  | _ =>
      throwErrorAt imm.ident
        s!"contract immutables currently support only Uint256 and Address; '{imm.name}' uses unsupported type"

private def externalExecutableWordType? : ValueType → Bool
  | .uint256 | .uint8 | .address | .bytes32 | .bool => true
  | _ => false

private def validateExternalExecutableType
    (extIdent : Ident)
    (extName : String)
    (ty : ValueType)
    (role : String) : CommandElabM Unit := do
  if !externalExecutableWordType? ty then
    throwErrorAt extIdent
      s!"linked external '{extName}' uses unsupported {role} type; executable externalCall currently supports only Uint256, Uint8, Address, Bytes32, and Bool"

private partial def stripParens (stx : Term) : Term :=
  match stx with
  | `(term| ($inner)) => stripParens inner
  | _ => stx

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

private def mkImmutableBoundBody
    (fields : Array StorageFieldDecl)
    (immutableDecls : Array ImmutableDecl)
    (fn : FunctionDecl)
    (body : Term) : CommandElabM Term := do
  let visibleImmutables := immutableDecls.filter fun imm =>
    !fn.params.any (fun p => p.name == imm.name)
  match body with
  | `(term| do $[$elems:doElem]*) =>
      let preludeElems ← visibleImmutables.zipIdx.mapM fun (imm, idx) => do
        let slotField := immutableStorageFieldDecl fields imm idx
        match imm.ty with
        | .uint256 => `(doElem| let $(imm.ident) ← getStorage $(slotField.ident))
        | .address => `(doElem| let $(imm.ident) ← getStorageAddr $(slotField.ident))
        | _ => throwErrorAt imm.ident s!"immutable '{imm.name}' uses unsupported type"
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

private def tupleElemsFromTerm? (stx : Term) : Option (Array Term) :=
  tupleElemsFromSyntax? (stripParens stx).raw |>.map (·.map (fun syn => ⟨syn⟩))

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

mutual
private partial def validateConstantBody
    (constDecls : Array ConstantDecl)
    (stx : Term)
    (visiting : List String := []) : CommandElabM Unit := do
  let stx := stripParens stx
  match stx with
  | `(term| constructorArg $idx:num) => throwNonCompileTimeConstantError idx "constructorArg"
  | `(term| blockTimestamp) => throwNonCompileTimeConstantError stx "blockTimestamp"
  | `(term| blockNumber) => throwNonCompileTimeConstantError stx "blockNumber"
  | `(term| blobbasefee) => throwNonCompileTimeConstantError stx "blobbasefee"
  | `(term| contractAddress) => throwNonCompileTimeConstantError stx "contractAddress"
  | `(term| chainid) => throwNonCompileTimeConstantError stx "chainid"
  | `(term| calldatasize) => throwNonCompileTimeConstantError stx "calldatasize"
  | `(term| returndataSize) => throwNonCompileTimeConstantError stx "returndataSize"
  | `(term| zeroAddress) => pure ()
  | `(term| isZeroAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| wordToAddress $a:term) => validateConstantBody constDecls a visiting
  | `(term| addressToWord $a:term) => validateConstantBody constDecls a visiting
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
  | `(term| mod $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
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
  | `(term| min $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
  | `(term| max $a $b) => validateConstantBody constDecls a visiting *> validateConstantBody constDecls b visiting
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
      translatePureExpr fields constDecls immutableDecls #[] #[] constant.body (name :: visiting)

partial def translatePureExpr
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term)
    (visitingConstants : List String := []) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| constructorArg $idx:num) =>
      `(Compiler.CompilationModel.Expr.constructorArg $idx)
  | `(term| blockTimestamp) => `(Compiler.CompilationModel.Expr.blockTimestamp)
  | `(term| blockNumber) => `(Compiler.CompilationModel.Expr.blockNumber)
  | `(term| blobbasefee) => `(Compiler.CompilationModel.Expr.blobbasefee)
  | `(term| contractAddress) => `(Compiler.CompilationModel.Expr.contractAddress)
  | `(term| chainid) => `(Compiler.CompilationModel.Expr.chainid)
  | `(term| calldatasize) => `(Compiler.CompilationModel.Expr.calldatasize)
  | `(term| returndataSize) => `(Compiler.CompilationModel.Expr.returndataSize)
  | `(term| zeroAddress) =>
      if params.any (fun p => p.name == "zeroAddress") || locals.contains "zeroAddress" then
        lookupVarExpr params locals "zeroAddress"
      else
        `(Compiler.CompilationModel.Expr.literal 0)
  | `(term| isZeroAddress $a:term) =>
      `(Compiler.CompilationModel.Expr.eq
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| wordToAddress $a:term) => translatePureExpr fields constDecls immutableDecls params locals a visitingConstants
  | `(term| addressToWord $a:term) => translatePureExpr fields constDecls immutableDecls params locals a visitingConstants
  | `(term| boolToWord $a:term) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          (Compiler.CompilationModel.Expr.literal 1)
          (Compiler.CompilationModel.Expr.literal 0))
  | `(term| $id:ident) =>
      let name := toString id.getId
      if params.any (fun p => p.name == name) || isTupleComponentRef params name || locals.contains name then
        lookupVarExpr params locals name
      else if let some imm := immutableDecls.find? (fun imm => imm.name == name) then
        match imm.ty with
        | .uint256 => `(Compiler.CompilationModel.Expr.storage $(strTerm (immutableHiddenName imm)))
        | .address => `(Compiler.CompilationModel.Expr.storageAddr $(strTerm (immutableHiddenName imm)))
        | _ => throwErrorAt stx s!"immutable '{name}' uses unsupported type"
      else
        translateConstantExpr fields constDecls immutableDecls visitingConstants name
  | `(term| $n:num) => `(Compiler.CompilationModel.Expr.literal $n)
  | `(term| add $a $b) => `(Compiler.CompilationModel.Expr.add $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| sub $a $b) => `(Compiler.CompilationModel.Expr.sub $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mul $a $b) => `(Compiler.CompilationModel.Expr.mul $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| div $a $b) => `(Compiler.CompilationModel.Expr.div $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| mod $a $b) => `(Compiler.CompilationModel.Expr.mod $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitAnd $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitOr $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitXor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| bitNot $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| shl $shift $value) => `(Compiler.CompilationModel.Expr.shl $(← translatePureExpr fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| shr $shift $value) => `(Compiler.CompilationModel.Expr.shr $(← translatePureExpr fields constDecls immutableDecls params locals shift visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals value visitingConstants))
  | `(term| $a == $b) => `(Compiler.CompilationModel.Expr.eq $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a != $b) =>
      `(Compiler.CompilationModel.Expr.logicalNot
          (Compiler.CompilationModel.Expr.eq
            $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
            $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants)))
  | `(term| $a >= $b) => `(Compiler.CompilationModel.Expr.ge $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a > $b) => `(Compiler.CompilationModel.Expr.gt $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a < $b) => `(Compiler.CompilationModel.Expr.lt $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a <= $b) => `(Compiler.CompilationModel.Expr.le $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a && $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| $a || $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalAnd $a $b) => `(Compiler.CompilationModel.Expr.logicalAnd $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalOr $a $b) => `(Compiler.CompilationModel.Expr.logicalOr $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| logicalNot $a) => `(Compiler.CompilationModel.Expr.logicalNot $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| and $a $b) => `(Compiler.CompilationModel.Expr.bitAnd $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| or $a $b) => `(Compiler.CompilationModel.Expr.bitOr $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| xor $a $b) => `(Compiler.CompilationModel.Expr.bitXor $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| not $a) => `(Compiler.CompilationModel.Expr.bitNot $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants))
  | `(term| mload $offset) =>
      `(Compiler.CompilationModel.Expr.mload
          $(← translatePureExpr fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| tload $offset) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExpr fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| calldataload $offset) =>
      `(Compiler.CompilationModel.Expr.calldataload
          $(← translatePureExpr fields constDecls immutableDecls params locals offset visitingConstants))
  | `(term| extcodesize $addr) =>
      `(Compiler.CompilationModel.Expr.extcodesize
          $(← translatePureExpr fields constDecls immutableDecls params locals addr visitingConstants))
  | `(term| keccak256 $offset $size) =>
      `(Compiler.CompilationModel.Expr.keccak256
          $(← translatePureExpr fields constDecls immutableDecls params locals offset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals size visitingConstants))
  | `(term| call $gas $target $value $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.call
          $(← translatePureExpr fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals value visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| staticcall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.staticcall
          $(← translatePureExpr fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| delegatecall $gas $target $inOffset $inSize $outOffset $outSize) =>
      `(Compiler.CompilationModel.Expr.delegatecall
          $(← translatePureExpr fields constDecls immutableDecls params locals gas visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals target visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals inSize visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outOffset visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals outSize visitingConstants))
  | `(term| arrayLength $name:term) =>
      `(Compiler.CompilationModel.Expr.arrayLength $(strTerm (← expectStringOrIdent name)))
  | `(term| arrayElement $name:term $index:term) =>
      `(Compiler.CompilationModel.Expr.arrayElement
          $(strTerm (← expectStringOrIdent name))
          $(← translatePureExpr fields constDecls immutableDecls params locals index visitingConstants))
  | `(term| mulDivDown $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivDown
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| mulDivUp $a $b $c) =>
      `(Compiler.CompilationModel.Expr.mulDivUp
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals c visitingConstants))
  | `(term| wMulDown $a $b) =>
      `(Compiler.CompilationModel.Expr.wMulDown
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| wDivUp $a $b) =>
      `(Compiler.CompilationModel.Expr.wDivUp
          $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| min $a $b) => `(Compiler.CompilationModel.Expr.min $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| max $a $b) => `(Compiler.CompilationModel.Expr.max $(← translatePureExpr fields constDecls immutableDecls params locals a visitingConstants) $(← translatePureExpr fields constDecls immutableDecls params locals b visitingConstants))
  | `(term| ite $cond $thenVal $elseVal) =>
      `(Compiler.CompilationModel.Expr.ite
          $(← translatePureExpr fields constDecls immutableDecls params locals cond visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals thenVal visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals elseVal visitingConstants))
  | `(term| externalCall $name:term $args:term) =>
      let extName := ← expectStringOrIdent name
      let argsExprs ←
        match stripParens args with
        | `(term| [ $[$xs],* ]) => xs.mapM (fun x => translatePureExpr fields constDecls immutableDecls params locals x visitingConstants)
        | _ => throwErrorAt args "expected list literal [..]"
      `(Compiler.CompilationModel.Expr.externalCall $(strTerm extName) [ $[$argsExprs],* ])
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExpr fields constDecls immutableDecls params locals key visitingConstants)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExpr fields constDecls immutableDecls params locals key1 visitingConstants)
          $(← translatePureExpr fields constDecls immutableDecls params locals key2 visitingConstants)
          $(strTerm memberName))
  | _ => throwErrorAt stx "unsupported expression in verity_contract body (see #1003 for planned macro support expansions)"
end

private def tupleLiteralOrStructValueExprs?
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
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
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(strTerm memberName))
        pure (some exprs)
    | `(term| structMembers2 $field:term $key1:term $key2:term $members:term) => do
        let fieldName := ← expectStringOrIdent field
        let memberNames := ← expectStringList members
        let exprs ← memberNames.mapM fun memberName => do
          let _ ← lookupStructMemberDecl fields fieldName memberName true
          `(Compiler.CompilationModel.Expr.structMember2
              $(strTerm fieldName)
              $(← translatePureExpr fields constDecls immutableDecls params locals key1)
              $(← translatePureExpr fields constDecls immutableDecls params locals key2)
              $(strTerm memberName))
        pure (some exprs)
    | _ => pure none
  match tupleElemsFromTerm? rhs with
  | some elems =>
      pure (some (← elems.mapM (translatePureExpr fields constDecls immutableDecls params locals)))
  | none =>
      structValueExprs?

private def tupleValueExprs
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
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
    (locals : Array String)
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
    (params : Array ParamDecl)
    (locals : Array String)
    (rhs : Term)
    (names : Array (Option String)) : CommandElabM (Option Term) := do
  let rhs := stripParens rhs
  let initialUsedNames := (params.toList.map (fun p => p.name)) ++ locals.toList ++ (names.filterMap id).toList
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
  match rhs.raw with
  | .node _ `Lean.Parser.Term.app args =>
      match args.getD 0 Syntax.missing with
      | .ident _ raw _ _ =>
          let argExprs ← (args.getD 1 Syntax.missing).getArgs.mapM
            (translatePureExpr fields constDecls immutableDecls params locals ∘ fun syn => ⟨syn⟩)
          pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
            [ $[$resultNameTerms],* ]
            $(strTerm raw.toString)
            [ $[$argExprs],* ])))
      | _ =>
          pure none
  | .ident _ raw _ _ =>
      pure (some (← `(Compiler.CompilationModel.Stmt.internalCallAssign
        [ $[$resultNameTerms],* ]
        $(strTerm raw.toString)
        [])))
  | _ =>
      pure none

private def expectExprList
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term) : CommandElabM (Array Term) := do
  match stripParens stx with
  | `(term| [ $[$xs],* ]) =>
      xs.mapM (translatePureExpr fields constDecls immutableDecls params locals)
  | _ => throwErrorAt stx "expected list literal [..]"

private def translateBindSource
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (rhs : Term) : CommandElabM Term := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| getStorage $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .uint256 => `(Compiler.CompilationModel.Expr.storage $(strTerm f.name))
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; encode as Uint256 and use getStorage"
      | .scalar .address => throwErrorAt rhs s!"field '{f.name}' is Address; use getStorageAddr"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2"
  | `(term| getStorageAddr $field:ident) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .scalar .address => `(Compiler.CompilationModel.Expr.storageAddr $(strTerm f.name))
      | .scalar .uint256 => throwErrorAt rhs s!"field '{f.name}' is Uint256; use getStorage"
      | .scalar .bool => throwErrorAt rhs s!"field '{f.name}' is Bool; use getStorage"
      | .scalar .unit => throwErrorAt rhs "invalid field type"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | _ => throwErrorAt rhs s!"field '{f.name}' is a mapping; use getMapping/getMapping2"
  | `(term| getMapping $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals key))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals key))
      | .mappingUintToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Uint256-keyed; use getMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUint $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingUintAddr $field:ident $key:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingUint $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals key))
      | .mappingAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is Address-keyed; use getMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember/structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMappingWord $field:ident $key:term $wordOffset:num) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Expr.mappingWord
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $wordOffset)
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt rhs s!"field '{f.name}' is a double mapping; use getMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .scalar _ => throwErrorAt rhs s!"field '{f.name}' is not a mapping"
  | `(term| getMapping2 $field:ident $key1:term $key2:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Expr.mapping2
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key1)
              $(← translatePureExpr fields constDecls immutableDecls params locals key2))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a nested struct mapping; use structMember2"
      | .mappingStruct _ _ =>
          throwErrorAt rhs s!"field '{f.name}' is a struct-valued mapping; use structMember"
      | _ => throwErrorAt rhs s!"field '{f.name}' is not a double mapping"
  | `(term| structMember $field:term $key:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName false
      `(Compiler.CompilationModel.Expr.structMember
          $(strTerm fieldName)
          $(← translatePureExpr fields constDecls immutableDecls params locals key)
          $(strTerm memberName))
  | `(term| structMember2 $field:term $key1:term $key2:term $member:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Expr.structMember2
          $(strTerm fieldName)
          $(← translatePureExpr fields constDecls immutableDecls params locals key1)
          $(← translatePureExpr fields constDecls immutableDecls params locals key2)
          $(strTerm memberName))
  | `(term| msgSender) => `(Compiler.CompilationModel.Expr.caller)
  | `(term| tload $offset:term) =>
      `(Compiler.CompilationModel.Expr.tload
          $(← translatePureExpr fields constDecls immutableDecls params locals offset))
  | _ =>
      throwErrorAt rhs
        "unsupported bind source; expected getStorage/getStorageAddr/getMapping/getMappingAddr/getMappingUint/getMappingUintAddr/getMappingWord/getMapping2/structMember/structMember2/msgSender/tload/ecrecover"

private def translateSafeRequireBind
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (varName : String)
    (rhs : Term) : CommandElabM (Option (Array Term)) := do
  let rhs := stripParens rhs
  match rhs with
  | `(term| requireSomeUint $optExpr:term $msg:term) =>
      let msgLit ← strTerm <$> expectStringLiteral msg
      let optExpr := stripParens optExpr
      match optExpr with
      | `(term| safeAdd $a:term $b:term) =>
          let aExpr ← translatePureExpr fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExpr fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.add $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $valueExpr $aExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | `(term| safeSub $a:term $b:term) =>
          let aExpr ← translatePureExpr fields constDecls immutableDecls params locals a
          let bExpr ← translatePureExpr fields constDecls immutableDecls params locals b
          let valueExpr : Term ← `(Compiler.CompilationModel.Expr.sub $aExpr $bExpr)
          let guardExpr : Term ← `(Compiler.CompilationModel.Expr.ge $aExpr $bExpr)
          pure (some #[
            (← `(Compiler.CompilationModel.Stmt.require $guardExpr $msgLit)),
            (← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $valueExpr))
          ])
      | _ =>
          throwErrorAt rhs "unsupported requireSomeUint source; expected safeAdd or safeSub"
  | _ => pure none

private def translateEffectStmt
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (stx : Term) : CommandElabM Term := do
  let stx := stripParens stx
  match stx with
  | `(term| setStorage $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .scalar .uint256 then
        throwErrorAt stx s!"field '{f.name}' is not Uint256; use setStorageAddr"
      `(Compiler.CompilationModel.Stmt.setStorage $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | `(term| setStorageAddr $field:ident $value) =>
      let f ← lookupStorageField fields (toString field.getId)
      if f.ty != .scalar .address then
        throwErrorAt stx s!"field '{f.name}' is not Address; use setStorage"
      `(Compiler.CompilationModel.Stmt.setStorageAddr $(strTerm f.name) $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | `(term| setMapping $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mappingUintToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Uint256-keyed; use setMappingUintAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUint $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMapping"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingUintAddr $field:ident $key:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingUint
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mappingAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is Address-keyed; use setMappingAddr"
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2"
      | .mappingStruct _ _ | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember/setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMappingWord $field:ident $key:term $wordOffset:num $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mappingAddressToUint256 | .mappingUintToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMappingWord
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key)
              $wordOffset
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mapping2AddressToAddressToUint256 =>
          throwErrorAt stx s!"field '{f.name}' is a double mapping; use setMapping2Word"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .scalar _ => throwErrorAt stx s!"field '{f.name}' is not a mapping"
  | `(term| setMapping2 $field:ident $key1:term $key2:term $value:term) =>
      let f ← lookupStorageField fields (toString field.getId)
      match f.ty with
      | .mapping2AddressToAddressToUint256 =>
          `(Compiler.CompilationModel.Stmt.setMapping2
              $(strTerm f.name)
              $(← translatePureExpr fields constDecls immutableDecls params locals key1)
              $(← translatePureExpr fields constDecls immutableDecls params locals key2)
              $(← translatePureExpr fields constDecls immutableDecls params locals value))
      | .mappingStruct2 _ _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a nested struct mapping; use setStructMember2"
      | .mappingStruct _ _ =>
          throwErrorAt stx s!"field '{f.name}' is a struct-valued mapping; use setStructMember"
      | _ => throwErrorAt stx s!"field '{f.name}' is not a double mapping"
  | `(term| require $cond $msg) =>
      `(Compiler.CompilationModel.Stmt.require
          $(← translatePureExpr fields constDecls immutableDecls params locals cond)
          $(strTerm (← expectStringLiteral msg)))
  | `(term| mstore $offset:term $value:term) =>
      `(Compiler.CompilationModel.Stmt.mstore
          $(← translatePureExpr fields constDecls immutableDecls params locals offset)
          $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | `(term| tstore $offset:term $value:term) =>
      `(Compiler.CompilationModel.Stmt.tstore
          $(← translatePureExpr fields constDecls immutableDecls params locals offset)
          $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | `(term| calldatacopy $destOffset:term $sourceOffset:term $size:term) =>
      `(Compiler.CompilationModel.Stmt.calldatacopy
          $(← translatePureExpr fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExpr fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExpr fields constDecls immutableDecls params locals size))
  | `(term| returndataCopy $destOffset:term $sourceOffset:term $size:term) =>
      `(Compiler.CompilationModel.Stmt.returndataCopy
          $(← translatePureExpr fields constDecls immutableDecls params locals destOffset)
          $(← translatePureExpr fields constDecls immutableDecls params locals sourceOffset)
          $(← translatePureExpr fields constDecls immutableDecls params locals size))
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
          $(← translatePureExpr fields constDecls immutableDecls params locals dataOffset)
          $(← translatePureExpr fields constDecls immutableDecls params locals dataSize))
  | `(term| internalCall $fnName:term $args:term) =>
      let targetFn := ← expectStringOrIdent fnName
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.internalCall $(strTerm targetFn) [ $[$argExprs],* ])
  | `(term| internalCallAssign $names:term $fnName:term $args:term) =>
      let resultNames := ← expectStringList names
      let resultNameTerms := resultNames.map strTerm
      let targetFn := ← expectStringOrIdent fnName
      let argExprs ← expectExprList fields constDecls immutableDecls params locals args
      `(Compiler.CompilationModel.Stmt.internalCallAssign
          [ $[$resultNameTerms],* ]
          $(strTerm targetFn)
          [ $[$argExprs],* ])
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
          $(← translatePureExpr fields constDecls immutableDecls params locals key)
          $(strTerm memberName)
          $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | `(term| setStructMember2 $field:term $key1:term $key2:term $member:term $value:term) =>
      let fieldName := ← expectStringOrIdent field
      let memberName := ← expectStringOrIdent member
      let _ ← lookupStructMemberDecl fields fieldName memberName true
      `(Compiler.CompilationModel.Stmt.setStructMember2
          $(strTerm fieldName)
          $(← translatePureExpr fields constDecls immutableDecls params locals key1)
          $(← translatePureExpr fields constDecls immutableDecls params locals key2)
          $(strTerm memberName)
          $(← translatePureExpr fields constDecls immutableDecls params locals value))
  | _ => throwErrorAt stx "unsupported statement in do block"

mutual
private partial def translateDoElems
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (mutableLocals : Array String)
    (elems : Array (TSyntax `doElem)) : CommandElabM (Array Term × Array String × Array String) := do
  let mut branchLocals := locals
  let mut branchMutableLocals := mutableLocals
  let mut stmts : Array Term := #[]
  for elem in elems do
    let (newStmts, newLocals, newMutableLocals) ←
      translateDoElem fields constDecls immutableDecls params branchLocals branchMutableLocals elem
    stmts := stmts ++ newStmts
    branchLocals := newLocals
    branchMutableLocals := newMutableLocals
  pure (stmts, branchLocals, branchMutableLocals)

private partial def translateDoSeqToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (mutableLocals : Array String)
    (doSeq : DoSeq) : CommandElabM (Array Term) := do
  match doSeq with
  | `(doSeq| $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls params locals mutableLocals elems)).1
  | _ => throwErrorAt doSeq "unsupported branch body; expected do-sequence"

private partial def translateDoElem
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (params : Array ParamDecl)
    (locals : Array String)
    (mutableLocals : Array String)
    (elem : TSyntax `doElem) : CommandElabM (Array Term × Array String × Array String) := do
  let tupleCase? ← do
    let stx := elem.raw
    if stx.getKind == `Lean.Parser.Term.doLet then
      let decl := stx[2]
      let patDecl := decl[0]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames locals names stx
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
                  pure (some (stmts, locals ++ (boundPairs.map (·.1)), mutableLocals))
              | none =>
                      match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls params locals rhs names) with
                  | some stmt =>
                      pure (some (#[(stmt)], locals ++ (names.filterMap (fun x => x)), mutableLocals))
                  | none => throwErrorAt rhs "tuple destructuring currently requires a tuple literal, tuple-typed parameter, structMembers/structMembers2 source, or internal helper call"
          | _ =>
              match (← tupleLiteralOrStructValueExprs? fields constDecls immutableDecls params locals rhs) with
              | some valueExprs =>
                  if names.size != valueExprs.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                  let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                    name?.map (fun name => (name, valueExpr))
                  let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                    `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                  pure (some (stmts, locals ++ (boundPairs.map (·.1)), mutableLocals))
              | none =>
                match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls params locals rhs names) with
                | some stmt =>
                    pure (some (#[(stmt)], locals ++ (names.filterMap (fun x => x)), mutableLocals))
                | none =>
                  let valueExprs ← tupleValueExprs fields constDecls immutableDecls params locals rhs
                  if names.size != valueExprs.size then
                    throwErrorAt patDecl s!"tuple destructuring binds {names.size} names, but the source provides {valueExprs.size} values"
                  let boundPairs := (names.zip valueExprs).filterMap fun (name?, valueExpr) =>
                    name?.map (fun name => (name, valueExpr))
                  let stmts ← boundPairs.mapM fun (name, valueExpr) =>
                    `(Compiler.CompilationModel.Stmt.letVar $(strTerm name) $valueExpr)
                  pure (some (stmts, locals ++ (boundPairs.map (·.1)), mutableLocals))
      | none => pure none
    else if stx.getKind == `Lean.Parser.Term.doLetArrow then
      let patDecl := stx[2]
      match tupleBinderNames? patDecl[0] with
      | some names =>
          ensureFreshLocalNames locals names stx
          let rhs : Term := ⟨patDecl[2][0]⟩
          match (← tupleInternalCallAssignStmt? fields constDecls immutableDecls params locals rhs names) with
          | some stmt =>
              pure (some (#[(stmt)], locals ++ (names.filterMap (fun x => x)), mutableLocals))
          | none => throwErrorAt rhs "tuple bind sources must be internal helper calls"
      | none => pure none
    else
      pure none
  match tupleCase? with
  | some result => pure result
  | none => match elem with
      | `(doElem| let mut $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if locals.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          let rhsExpr ← translatePureExpr fields constDecls immutableDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
              locals.push varName,
              mutableLocals.push varName)
      | `(doElem| let $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if locals.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          let rhsExpr ← translatePureExpr fields constDecls immutableDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
              locals.push varName,
              mutableLocals)
      | `(doElem| let $name:ident ← $rhs:term) =>
          let varName := toString name.getId
          if locals.contains varName then
            throwErrorAt name s!"duplicate local variable '{varName}'"
          match stripParens rhs with
          | `(term| ecrecover $hash:term $v:term $r:term $s:term) =>
              let hashExpr ← translatePureExpr fields constDecls immutableDecls params locals hash
              let vExpr ← translatePureExpr fields constDecls immutableDecls params locals v
              let rExpr ← translatePureExpr fields constDecls immutableDecls params locals r
              let sExpr ← translatePureExpr fields constDecls immutableDecls params locals s
              pure
                (#[(← `(Compiler.CompilationModel.Stmt.ecm
                        (Compiler.Modules.Precompiles.ecrecoverModule $(strTerm varName))
                        [$hashExpr, $vExpr, $rExpr, $sExpr]))],
                  locals.push varName,
                  mutableLocals)
          | _ =>
              let safeBind? ← translateSafeRequireBind fields constDecls immutableDecls params locals varName rhs
              match safeBind? with
              | some safeStmts => pure (safeStmts, locals.push varName, mutableLocals)
              | none =>
                  let rhsExpr ← translateBindSource fields constDecls immutableDecls params locals rhs
                  pure
                    (#[(← `(Compiler.CompilationModel.Stmt.letVar $(strTerm varName) $rhsExpr))],
                      locals.push varName,
                      mutableLocals)
      | `(doElem| $name:ident := $rhs:term) =>
          let varName := toString name.getId
          if !locals.contains varName then
            throwErrorAt name s!"cannot assign unknown variable '{varName}'"
          if !mutableLocals.contains varName then
            throwErrorAt name s!"cannot assign immutable variable '{varName}'; declare it with 'let mut'"
          let rhsExpr ← translatePureExpr fields constDecls immutableDecls params locals rhs
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.assignVar $(strTerm varName) $rhsExpr))],
              locals,
              mutableLocals)
      | `(doElem| return $value:term) =>
          match (← tupleReturnValueExprs? fields constDecls immutableDecls params locals value) with
          | some valueExprs =>
              pure (#[(← `(Compiler.CompilationModel.Stmt.returnValues [ $[$valueExprs],* ]))], locals, mutableLocals)
          | none =>
              pure (#[(← `(Compiler.CompilationModel.Stmt.return $(← translatePureExpr fields constDecls immutableDecls params locals value)))], locals, mutableLocals)
      | `(doElem| pure ()) =>
          pure (#[], locals, mutableLocals)
      | `(doElem| if $cond:term then $thenBranch:doSeq else $elseBranch:doSeq) =>
          let condExpr ← translatePureExpr fields constDecls immutableDecls params locals cond
          let thenStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls params locals mutableLocals thenBranch
          let elseStmts ← translateDoSeqToStmtTerms fields constDecls immutableDecls params locals mutableLocals elseBranch
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.ite
              $condExpr
              [ $[$thenStmts],* ]
              [ $[$elseStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| forEach $name:term $count:term $body:term) =>
          let loopVar := ← expectStringOrIdent name
          let countExpr ← translatePureExpr fields constDecls immutableDecls params locals count
          let bodyStmts ←
            match stripParens body with
            | `(term| do $[$inner:doElem]*) =>
                pure (← (translateDoElems fields constDecls immutableDecls params (locals.push loopVar) mutableLocals inner)).1
            | _ => throwErrorAt body "forEach body must be a do block"
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.forEach
                $(strTerm loopVar)
                $countExpr
                [ $[$bodyStmts],* ]))],
              locals,
              mutableLocals)
      | `(doElem| requireError $cond:term $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExpr fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.requireError
                    $(← translatePureExpr fields constDecls immutableDecls params locals cond)
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revert $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExpr fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| revertError $errorName:ident($args,*)) =>
          let argExprs ← args.getElems.mapM (translatePureExpr fields constDecls immutableDecls params locals)
          pure
            (#[(← `(Compiler.CompilationModel.Stmt.revertError
                    $(strTerm (toString errorName.getId))
                    [ $[$argExprs],* ]))],
              locals,
              mutableLocals)
      | `(doElem| $stmt:term) =>
          pure (#[(← translateEffectStmt fields constDecls immutableDecls params locals stmt)], locals, mutableLocals)
      | _ => throwErrorAt elem "unsupported do element"
end

private def translateBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (fn : FunctionDecl) : CommandElabM (Array Term) := do
  match fn.body with
  | `(term| do $[$elems:doElem]*) =>
      let guardPrelude ← initGuardPreludeStmtTerms fields fn
      let stmts := guardPrelude ++ (← translateDoElems fields constDecls immutableDecls fn.params #[] #[] elems).1
      let mut stmts := stmts
      if fn.returnTy == .unit then
        stmts := stmts.push (← `(Compiler.CompilationModel.Stmt.stop))
      pure stmts
  | _ => throwErrorAt fn.body "function body must be a do block"

private def translateConstructorBodyToStmtTerms
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (ctor : ConstructorDecl) : CommandElabM (Array Term) := do
  match ctor.body with
  | `(term| do $[$elems:doElem]*) =>
      pure (← (translateDoElems fields constDecls immutableDecls ctor.params #[] #[] elems)).1
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
    | .uint256 =>
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
  let storageTy ←
    match field.ty with
    | .scalar .uint256 => `(Uint256)
    | .scalar .uint8 => throwError "storage field cannot be Uint8; use Uint256 encoding"
    | .scalar .address => `(Address)
    | .scalar .bytes32 => throwError "storage field cannot be Bytes32; use Uint256 encoding"
    | .scalar .bool => throwError "storage field cannot be Bool; use Uint256 (0/1) encoding"
    | .scalar .string => throwError "storage field cannot be String; use Uint256 encoding"
    | .scalar .bytes => throwError "storage field cannot be Bytes; use Uint256 encoding"
    | .scalar (.array _) => throwError "storage field cannot be Array; use mapping encodings"
    | .scalar (.tuple _) => throwError "storage field cannot be Tuple; use mapping encodings"
    | .scalar .unit => throwError "storage field cannot be Unit"
    | .mappingAddressToUint256 => `(Address → Uint256)
    | .mapping2AddressToAddressToUint256 => `(Address → Address → Uint256)
    | .mappingUintToUint256 => `(Uint256 → Uint256)
    | .mappingStruct .address _ => `(Address → Uint256)
    | .mappingStruct .uint256 _ => `(Uint256 → Uint256)
    | .mappingStruct2 .address .address _ => `(Address → Address → Uint256)
    | .mappingStruct2 .address .uint256 _ => `(Address → Uint256 → Uint256)
    | .mappingStruct2 .uint256 .address _ => `(Uint256 → Address → Uint256)
    | .mappingStruct2 .uint256 .uint256 _ => `(Uint256 → Uint256 → Uint256)
  let fid := field.ident
  `(command| def $fid : Verity.StorageSlot $storageTy := ⟨$(natTerm field.slotNum)⟩)

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

private def mkSpecCommand
    (contractName : String)
    (fields : Array StorageFieldDecl)
    (errorDecls : Array ErrorDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (externalDecls : Array ExternalDecl)
    (ctor : Option ConstructorDecl)
    (functions : Array FunctionDecl) : CommandElabM Cmd := do
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
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls ctor.params
        let ctorBodyTerms ← translateConstructorBodyToStmtTerms fields constDecls immutableDecls ctor
        let ctorAllTerms := immutableInitTerms ++ ctorBodyTerms
        `(some {
          params := $ctorParams
          isPayable := $ctorPayable
          body := [ $[$ctorAllTerms],* ]
        })
    | none, false =>
        let immutableInitTerms ← immutableInitStmtTerms fields constDecls immutableDecls #[]
        `(some {
          params := []
          isPayable := false
          body := [ $[$immutableInitTerms],* ]
        })
  let functionModelIds ← functions.mapM fun fn => mkSuffixedIdent fn.ident "_model"
  `(command| def spec : Compiler.CompilationModel.CompilationModel := {
    name := $(strTerm contractName)
    fields := [ $[$fieldTerms],* ]
    «errors» := [ $[$errorTerms],* ]
    «constructor» := $constructorTerm
    functions := [ $[$functionModelIds],* ]
    «externals» := [ $[$externalTerms],* ]
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
    let fnCmds ← mkFindIdxParamSimpCommandsForScope contractName fn.name fn.params
    cmds := cmds ++ fnCmds
  pure cmds

def parseContractSyntax
    (stx : Syntax)
    : CommandElabM
        (Ident × Array StorageFieldDecl × Array ErrorDecl × Array ConstantDecl × Array ImmutableDecl × Array ExternalDecl × Option ConstructorDecl × Array FunctionDecl) := do
  match stx with
  | `(command| verity_contract $contractName:ident where storage $[$storageFields:verityStorageField]* $[errors $[$errorDecls:verityError]*]? $[constants $[$constantDecls:verityConstant]*]? $[immutables $[$immutableDecls:verityImmutable]*]? $[linked_externals $[$externalDecls:verityExternal]*]? $[$ctor:verityConstructor]? $[$functions:verityFunction]*) =>
      let parsedErrors ←
        match errorDecls with
        | some decls => decls.mapM parseError
        | none => pure #[]
      let parsedConstants ←
        match constantDecls with
        | some decls => decls.mapM parseConstant
        | none => pure #[]
      let parsedImmutables ←
        match immutableDecls with
        | some decls => decls.mapM parseImmutable
        | none => pure #[]
      let parsedExternals ←
        match externalDecls with
        | some decls => decls.mapM parseExternal
        | none => pure #[]
      pure
        ( contractName
        , (← storageFields.mapM parseStorageField)
        , parsedErrors
        , parsedConstants
        , parsedImmutables
        , parsedExternals
        , (← ctor.mapM parseConstructor)
        , (← functions.mapM parseFunction)
        )
  | _ => throwErrorAt stx "invalid verity_contract declaration"

private def mkConstantDefCommand (constant : ConstantDecl) : CommandElabM Cmd := do
  `(command| def $constant.ident : $(← contractValueTypeTerm constant.ty) := $constant.body)

def mkStorageDefCommandPublic (field : StorageFieldDecl) : CommandElabM Cmd :=
  mkStorageDefCommand field

def mkConstantDefCommandPublic (constant : ConstantDecl) : CommandElabM Cmd :=
  mkConstantDefCommand constant

def validateConstantDeclsPublic (constDecls : Array ConstantDecl) : CommandElabM Unit := do
  for constant in constDecls do
    validateConstantBody constDecls constant.body [constant.name]

def validateImmutableDeclsPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl) : CommandElabM Unit := do
  let mut seenNames : Array String := #[]
  for imm in immutableDecls do
    validateImmutableType imm
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
    if ext.returnTys.size > 1 then
      throwErrorAt ext.ident
        s!"linked external '{ext.name}' currently supports at most one return value; statement-style external bindings are not exposed from verity_contract yet"
    for paramTy in ext.params do
      validateExternalExecutableType ext.ident ext.name paramTy "parameter"
    for returnTy in ext.returnTys do
      validateExternalExecutableType ext.ident ext.name returnTy "return"
    seenNames := seenNames.push ext.name

def mkFunctionCommandsPublic
    (fields : Array StorageFieldDecl)
    (constDecls : Array ConstantDecl)
    (immutableDecls : Array ImmutableDecl)
    (fn : FunctionDecl) : CommandElabM (Array Cmd) := do
  let fnType ← mkContractFnType fn.params fn.returnTy
  let fnGuardedBody ← mkInitGuardedBody fields fn
  let fnBody ← mkImmutableBoundBody fields immutableDecls fn fnGuardedBody
  let fnValue ← mkContractFnValue fn.params fnBody
  let modelBodyName ← mkSuffixedIdent fn.ident "_modelBody"
  let modelName ← mkSuffixedIdent fn.ident "_model"
  let stmtTerms ← translateBodyToStmtTerms fields constDecls immutableDecls fn
  let modelParams ← mkModelParamsTerm fn.params

  let fnCmd : Cmd ← `(command| def $fn.ident : $fnType := $fnValue)
  let bodyCmd : Cmd ← `(command| def $modelBodyName : List Compiler.CompilationModel.Stmt := [ $[$stmtTerms],* ])
  let modelCmd : Cmd ← `(command| def $modelName : Compiler.CompilationModel.FunctionSpec := {
    name := $(strTerm fn.name)
    params := $modelParams
    returnType := $(← modelReturnTypeTerm fn.returnTy)
    «returns» := $(← modelReturnsTerm fn.returnTy)
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
    (functions : Array FunctionDecl) : CommandElabM Cmd :=
  mkSpecCommand contractName fields errorDecls constDecls immutableDecls externalDecls ctor functions

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
