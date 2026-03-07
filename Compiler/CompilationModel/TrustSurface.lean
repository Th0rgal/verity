import Compiler.CompilationModel.Types
import Compiler.CompilationModel.EcmAxiomCollection

namespace Compiler.CompilationModel

private def dedupPreserve (items : List String) : List String :=
  items.foldl (fun acc item => if acc.contains item then acc else acc ++ [item]) []

private partial def collectLowLevelExprMechanics : Expr → List String
  | .call gas target value inOffset inSize outOffset outSize =>
      ["call"] ++ collectLowLevelExprMechanics gas ++ collectLowLevelExprMechanics target ++
        collectLowLevelExprMechanics value ++ collectLowLevelExprMechanics inOffset ++
        collectLowLevelExprMechanics inSize ++ collectLowLevelExprMechanics outOffset ++
        collectLowLevelExprMechanics outSize
  | .staticcall gas target inOffset inSize outOffset outSize =>
      ["staticcall"] ++ collectLowLevelExprMechanics gas ++ collectLowLevelExprMechanics target ++
        collectLowLevelExprMechanics inOffset ++ collectLowLevelExprMechanics inSize ++
        collectLowLevelExprMechanics outOffset ++ collectLowLevelExprMechanics outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      ["delegatecall"] ++ collectLowLevelExprMechanics gas ++ collectLowLevelExprMechanics target ++
        collectLowLevelExprMechanics inOffset ++ collectLowLevelExprMechanics inSize ++
        collectLowLevelExprMechanics outOffset ++ collectLowLevelExprMechanics outSize
  | .returndataSize =>
      ["returndataSize"]
  | .returndataOptionalBoolAt outOffset =>
      ["returndataOptionalBoolAt"] ++ collectLowLevelExprMechanics outOffset
  | .mapping _ key
  | .mappingWord _ key _
  | .mappingPackedWord _ key _ _
  | .structMember _ key _ =>
      collectLowLevelExprMechanics key
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectLowLevelExprMechanics key1 ++ collectLowLevelExprMechanics key2
  | .mappingUint _ key
  | .arrayElement _ key
  | .mload key
  | .calldataload key
  | .extcodesize key =>
      collectLowLevelExprMechanics key
  | .keccak256 offset size =>
      collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics size
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectLowLevelExprMechanics
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b
  | .eq a b | .gt a b | .lt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b =>
      collectLowLevelExprMechanics a ++ collectLowLevelExprMechanics b
  | .mulDivDown a b c | .mulDivUp a b c =>
      collectLowLevelExprMechanics a ++ collectLowLevelExprMechanics b ++ collectLowLevelExprMechanics c
  | .bitNot a | .logicalNot a =>
      collectLowLevelExprMechanics a
  | .ite cond thenVal elseVal =>
      collectLowLevelExprMechanics cond ++ collectLowLevelExprMechanics thenVal ++ collectLowLevelExprMechanics elseVal
  | _ =>
      []

private partial def collectLowLevelStmtMechanics : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .setStorage _ value
  | .setStorageAddr _ value
  | .return value
  | .require value _ =>
      collectLowLevelExprMechanics value
  | .requireError cond _ args =>
      collectLowLevelExprMechanics cond ++ args.flatMap collectLowLevelExprMechanics
  | .revertError _ args =>
      args.flatMap collectLowLevelExprMechanics
  | .mstore offset value =>
      collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics value
  | .calldatacopy destOffset sourceOffset size =>
      collectLowLevelExprMechanics destOffset ++ collectLowLevelExprMechanics sourceOffset ++ collectLowLevelExprMechanics size
  | .returndataCopy destOffset sourceOffset size =>
      ["returndataCopy"] ++ collectLowLevelExprMechanics destOffset ++ collectLowLevelExprMechanics sourceOffset ++ collectLowLevelExprMechanics size
  | .revertReturndata =>
      ["revertReturndata"]
  | .setMapping _ key value
  | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value
  | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      collectLowLevelExprMechanics key ++ collectLowLevelExprMechanics value
  | .setMapping2 _ key1 key2 value
  | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      collectLowLevelExprMechanics key1 ++ collectLowLevelExprMechanics key2 ++ collectLowLevelExprMechanics value
  | .ite cond thenBr elseBr =>
      collectLowLevelExprMechanics cond ++ thenBr.flatMap collectLowLevelStmtMechanics ++ elseBr.flatMap collectLowLevelStmtMechanics
  | .forEach _ count body =>
      collectLowLevelExprMechanics count ++ body.flatMap collectLowLevelStmtMechanics
  | .emit _ args
  | .internalCall _ args
  | .externalCallBind _ _ args
  | .returnValues args
  | .ecm _ args
  | .internalCallAssign _ _ args =>
      args.flatMap collectLowLevelExprMechanics
  | .rawLog topics dataOffset dataSize =>
      topics.flatMap collectLowLevelExprMechanics ++ collectLowLevelExprMechanics dataOffset ++ collectLowLevelExprMechanics dataSize
  | .returnArray _
  | .returnBytes _
  | .returnStorageWords _
  | .stop =>
      []

/-- Collect unique low-level call and returndata mechanics used by a spec. -/
def collectLowLevelMechanics (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  dedupPreserve (allStmts.flatMap collectLowLevelStmtMechanics)

private partial def collectExternalExprNames : Expr → List String
  | .externalCall name args =>
      name :: args.flatMap collectExternalExprNames
  | .call gas target value inOffset inSize outOffset outSize =>
      collectExternalExprNames gas ++ collectExternalExprNames target ++ collectExternalExprNames value ++
        collectExternalExprNames inOffset ++ collectExternalExprNames inSize ++
        collectExternalExprNames outOffset ++ collectExternalExprNames outSize
  | .staticcall gas target inOffset inSize outOffset outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      collectExternalExprNames gas ++ collectExternalExprNames target ++ collectExternalExprNames inOffset ++
        collectExternalExprNames inSize ++ collectExternalExprNames outOffset ++ collectExternalExprNames outSize
  | .returndataOptionalBoolAt outOffset
  | .mload outOffset
  | .calldataload outOffset
  | .extcodesize outOffset =>
      collectExternalExprNames outOffset
  | .keccak256 offset size =>
      collectExternalExprNames offset ++ collectExternalExprNames size
  | .mapping _ key
  | .mappingWord _ key _
  | .mappingPackedWord _ key _ _
  | .structMember _ key _ =>
      collectExternalExprNames key
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectExternalExprNames key1 ++ collectExternalExprNames key2
  | .mappingUint _ key
  | .arrayElement _ key =>
      collectExternalExprNames key
  | .internalCall _ args =>
      args.flatMap collectExternalExprNames
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b
  | .eq a b | .gt a b | .lt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b =>
      collectExternalExprNames a ++ collectExternalExprNames b
  | .mulDivDown a b c | .mulDivUp a b c =>
      collectExternalExprNames a ++ collectExternalExprNames b ++ collectExternalExprNames c
  | .bitNot a | .logicalNot a =>
      collectExternalExprNames a
  | .ite cond thenVal elseVal =>
      collectExternalExprNames cond ++ collectExternalExprNames thenVal ++ collectExternalExprNames elseVal
  | _ =>
      []

private partial def collectExternalStmtNames : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .setStorage _ value
  | .setStorageAddr _ value
  | .return value
  | .require value _ =>
      collectExternalExprNames value
  | .requireError cond _ args =>
      collectExternalExprNames cond ++ args.flatMap collectExternalExprNames
  | .revertError _ args =>
      args.flatMap collectExternalExprNames
  | .mstore offset value =>
      collectExternalExprNames offset ++ collectExternalExprNames value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      collectExternalExprNames destOffset ++ collectExternalExprNames sourceOffset ++ collectExternalExprNames size
  | .setMapping _ key value
  | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value
  | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      collectExternalExprNames key ++ collectExternalExprNames value
  | .setMapping2 _ key1 key2 value
  | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      collectExternalExprNames key1 ++ collectExternalExprNames key2 ++ collectExternalExprNames value
  | .ite cond thenBr elseBr =>
      collectExternalExprNames cond ++ thenBr.flatMap collectExternalStmtNames ++ elseBr.flatMap collectExternalStmtNames
  | .forEach _ count body =>
      collectExternalExprNames count ++ body.flatMap collectExternalStmtNames
  | .emit _ args
  | .internalCall _ args
  | .returnValues args
  | .ecm _ args
  | .internalCallAssign _ _ args =>
      args.flatMap collectExternalExprNames
  | .externalCallBind _ externalName args =>
      externalName :: args.flatMap collectExternalExprNames
  | .rawLog topics dataOffset dataSize =>
      topics.flatMap collectExternalExprNames ++ collectExternalExprNames dataOffset ++ collectExternalExprNames dataSize
  | .returnArray _
  | .returnBytes _
  | .returnStorageWords _
  | .revertReturndata
  | .stop =>
      []

private def collectUsedExternalNames (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  dedupPreserve (allStmts.flatMap collectExternalStmtNames)

/-- Collect linked external declarations that are actually referenced by the spec. -/
def collectUsedExternalAssumptions (spec : CompilationModel) : List (String × List String) :=
  let usedNames := collectUsedExternalNames spec
  let rec gather : List ExternalFunction → List (String × List String)
    | [] => []
    | ext :: rest =>
        let tail := gather rest
        if usedNames.contains ext.name then
          (ext.name, ext.axiomNames) :: tail
        else
          tail
  gather spec.externals

private def escapeJsonChar (c : Char) : String :=
  match c with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | _ => String.singleton c

private def escapeJsonString (s : String) : String :=
  s.data.foldl (fun acc c => acc ++ escapeJsonChar c) ""

private def jsonString (s : String) : String :=
  "\"" ++ escapeJsonString s ++ "\""

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (name, value) => jsonString name ++ ":" ++ value) ++ "}"

private def assumptionJson (entry : String × List String) : String :=
  jsonObject [
    ("name", jsonString entry.1),
    ("axioms", jsonArray (entry.2.map jsonString))
  ]

private def ecmJson (entry : String × String) : String :=
  jsonObject [
    ("module", jsonString entry.1),
    ("assumption", jsonString entry.2)
  ]

/-- Render the machine-readable trust report consumed by CLI/tests. -/
def emitTrustReportJson (specs : List CompilationModel) : String :=
  jsonObject [
    ("contracts", jsonArray (specs.map contractJson))
  ]
where
  contractJson (spec : CompilationModel) : String :=
    jsonObject [
      ("contract", jsonString spec.name),
      ("modeledLowLevelMechanics", jsonArray ((collectLowLevelMechanics spec).map jsonString)),
      ("proofBoundary", jsonObject [
        ("compilerModelsMechanics", "true"),
        ("proofInterpretersModelMechanics", "false"),
        ("calleeBehaviorRequiresAssumptions", "true")
      ]),
      ("externalAssumptions", jsonObject [
        ("linkedExternals", jsonArray ((collectUsedExternalAssumptions spec).map assumptionJson)),
        ("ecmAxioms", jsonArray ((collectEcmAxioms spec).map ecmJson))
      ])
    ]

end Compiler.CompilationModel
