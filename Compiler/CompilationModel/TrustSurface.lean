import Compiler.CompilationModel.Types
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.ProofStatus

namespace Compiler.CompilationModel

private def dedupPreserve (items : List String) : List String :=
  items.foldl (fun acc item => if acc.contains item then acc else acc ++ [item]) []

private def dedupExternalFunctions (items : List ExternalFunction) : List ExternalFunction :=
  items.foldl
    (fun acc item => if acc.any (fun prev => prev.name = item.name) then acc else acc ++ [item])
    []

private def dedupEcmModules (items : List ECM.ExternalCallModule) : List ECM.ExternalCallModule :=
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
  | .blobbasefee =>
      ["blobbasefee"]
  | .tload offset =>
      ["tload"] ++ collectLowLevelExprMechanics offset
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

private partial def collectAxiomatizedExprPrimitives : Expr → List String
  | .keccak256 offset size =>
      ["keccak256"] ++ collectAxiomatizedExprPrimitives offset ++ collectAxiomatizedExprPrimitives size
  | .call gas target value inOffset inSize outOffset outSize =>
      collectAxiomatizedExprPrimitives gas ++ collectAxiomatizedExprPrimitives target ++
        collectAxiomatizedExprPrimitives value ++ collectAxiomatizedExprPrimitives inOffset ++
        collectAxiomatizedExprPrimitives inSize ++ collectAxiomatizedExprPrimitives outOffset ++
        collectAxiomatizedExprPrimitives outSize
  | .staticcall gas target inOffset inSize outOffset outSize =>
      collectAxiomatizedExprPrimitives gas ++ collectAxiomatizedExprPrimitives target ++
        collectAxiomatizedExprPrimitives inOffset ++ collectAxiomatizedExprPrimitives inSize ++
        collectAxiomatizedExprPrimitives outOffset ++ collectAxiomatizedExprPrimitives outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      collectAxiomatizedExprPrimitives gas ++ collectAxiomatizedExprPrimitives target ++
        collectAxiomatizedExprPrimitives inOffset ++ collectAxiomatizedExprPrimitives inSize ++
        collectAxiomatizedExprPrimitives outOffset ++ collectAxiomatizedExprPrimitives outSize
  | .returndataOptionalBoolAt outOffset
  | .mload outOffset
  | .tload outOffset
  | .calldataload outOffset
  | .extcodesize outOffset =>
      collectAxiomatizedExprPrimitives outOffset
  | .mapping _ key
  | .mappingWord _ key _
  | .mappingPackedWord _ key _ _
  | .structMember _ key _ =>
      collectAxiomatizedExprPrimitives key
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectAxiomatizedExprPrimitives key1 ++ collectAxiomatizedExprPrimitives key2
  | .mappingUint _ key
  | .arrayElement _ key =>
      collectAxiomatizedExprPrimitives key
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectAxiomatizedExprPrimitives
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b
  | .eq a b | .gt a b | .lt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b =>
      collectAxiomatizedExprPrimitives a ++ collectAxiomatizedExprPrimitives b
  | .mulDivDown a b c | .mulDivUp a b c =>
      collectAxiomatizedExprPrimitives a ++ collectAxiomatizedExprPrimitives b ++ collectAxiomatizedExprPrimitives c
  | .bitNot a | .logicalNot a =>
      collectAxiomatizedExprPrimitives a
  | .ite cond thenVal elseVal =>
      collectAxiomatizedExprPrimitives cond ++ collectAxiomatizedExprPrimitives thenVal ++
        collectAxiomatizedExprPrimitives elseVal
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
  | .tstore offset value =>
      ["tstore"] ++ collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics value
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

private partial def collectAxiomatizedStmtPrimitives : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .setStorage _ value
  | .setStorageAddr _ value
  | .return value
  | .require value _ =>
      collectAxiomatizedExprPrimitives value
  | .requireError cond _ args =>
      collectAxiomatizedExprPrimitives cond ++ args.flatMap collectAxiomatizedExprPrimitives
  | .revertError _ args =>
      args.flatMap collectAxiomatizedExprPrimitives
  | .mstore offset value =>
      collectAxiomatizedExprPrimitives offset ++ collectAxiomatizedExprPrimitives value
  | .tstore offset value =>
      collectAxiomatizedExprPrimitives offset ++ collectAxiomatizedExprPrimitives value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      collectAxiomatizedExprPrimitives destOffset ++ collectAxiomatizedExprPrimitives sourceOffset ++
        collectAxiomatizedExprPrimitives size
  | .setMapping _ key value
  | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value
  | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      collectAxiomatizedExprPrimitives key ++ collectAxiomatizedExprPrimitives value
  | .setMapping2 _ key1 key2 value
  | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      collectAxiomatizedExprPrimitives key1 ++ collectAxiomatizedExprPrimitives key2 ++
        collectAxiomatizedExprPrimitives value
  | .ite cond thenBr elseBr =>
      collectAxiomatizedExprPrimitives cond ++ thenBr.flatMap collectAxiomatizedStmtPrimitives ++
        elseBr.flatMap collectAxiomatizedStmtPrimitives
  | .forEach _ count body =>
      collectAxiomatizedExprPrimitives count ++ body.flatMap collectAxiomatizedStmtPrimitives
  | .emit _ args
  | .internalCall _ args
  | .externalCallBind _ _ args
  | .returnValues args
  | .ecm _ args
  | .internalCallAssign _ _ args =>
      args.flatMap collectAxiomatizedExprPrimitives
  | .rawLog topics dataOffset dataSize =>
      topics.flatMap collectAxiomatizedExprPrimitives ++ collectAxiomatizedExprPrimitives dataOffset ++
        collectAxiomatizedExprPrimitives dataSize
  | .returnArray _
  | .returnBytes _
  | .returnStorageWords _
  | .revertReturndata
  | .stop =>
      []

private def collectLowLevelMechanicsFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve (stmts.flatMap collectLowLevelStmtMechanics)

private def collectAxiomatizedPrimitivesFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve (stmts.flatMap collectAxiomatizedStmtPrimitives)

/-- Collect unique low-level call and returndata mechanics used by a spec. -/
def collectLowLevelMechanics (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectLowLevelMechanicsFromStmts allStmts

/-- Collect unique axiomatized primitives used directly by a spec. -/
def collectAxiomatizedPrimitives (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectAxiomatizedPrimitivesFromStmts allStmts

private def collectAxiomatizedPrimitivesByStatus
    (spec : CompilationModel)
    (status : Compiler.ProofStatus) : List String :=
  match status with
  | .proved => []
  | .assumed => collectAxiomatizedPrimitives spec
  | .unchecked => []

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
  | .tload outOffset
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
  | .tstore offset value =>
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

private def collectUsedExternalNamesFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve (stmts.flatMap collectExternalStmtNames)

private def collectUsedExternalAssumptionsFromStmts
    (externals : List ExternalFunction)
    (stmts : List Stmt) : List ExternalFunction :=
  let usedNames := collectUsedExternalNamesFromStmts stmts
  dedupExternalFunctions (externals.filter (fun ext => usedNames.contains ext.name))

private def collectUsedExternalNames (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectUsedExternalNamesFromStmts allStmts

/-- Collect linked external declarations that are actually referenced by the spec. -/
def collectUsedExternalAssumptions (spec : CompilationModel) : List ExternalFunction :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectUsedExternalAssumptionsFromStmts spec.externals allStmts

private def collectUsedExternalNamesByStatus
    (spec : CompilationModel)
    (status : Compiler.ProofStatus) : List String :=
  (collectUsedExternalAssumptions spec).foldl
    (fun acc ext => if ext.proofStatus == status then acc ++ [ext.name] else acc)
    []

private partial def collectUsedEcmModulesInStmt : Stmt → List ECM.ExternalCallModule
  | .ecm mod _ => [mod]
  | .ite _ thenBr elseBr =>
      thenBr.flatMap collectUsedEcmModulesInStmt ++ elseBr.flatMap collectUsedEcmModulesInStmt
  | .forEach _ _ body =>
      body.flatMap collectUsedEcmModulesInStmt
  | _ =>
      []

private def collectUsedEcmModulesFromStmts (stmts : List Stmt) : List ECM.ExternalCallModule :=
  dedupEcmModules (stmts.flatMap collectUsedEcmModulesInStmt)

/-- Collect ECM modules that are actually referenced by the spec, including
    constructor bodies. This shared view keeps machine-readable reports and
    compiler summaries aligned. -/
def collectUsedEcmModules (spec : CompilationModel) : List ECM.ExternalCallModule :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectUsedEcmModulesFromStmts allStmts

private def collectUsedEcmModuleNamesByStatus
    (spec : CompilationModel)
    (status : Compiler.ProofStatus) : List String :=
  (collectUsedEcmModules spec).foldl
    (fun acc mod => if mod.proofStatus == status then acc ++ [mod.name] else acc)
    []

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

private def proofStatusString (status : Compiler.ProofStatus) : String :=
  jsonString status.toJsonString

private def assumptionJson (entry : ExternalFunction) : String :=
  jsonObject [
    ("name", jsonString entry.name),
    ("status", proofStatusString entry.proofStatus),
    ("axioms", jsonArray (entry.axiomNames.map jsonString))
  ]

/-- Stable machine-readable assumption name for a trusted primitive boundary. -/
def primitiveAssumptionName (primitive : String) : String :=
  match primitive with
  | "keccak256" => "keccak256_memory_slice_matches_evm"
  | other => s!"{other}_assumed"

private def primitiveAssumptionJson (primitive : String) : String :=
  jsonObject [
    ("primitive", jsonString primitive),
    ("status", proofStatusString .assumed),
    ("assumption", jsonString (primitiveAssumptionName primitive))
  ]

private def ecmJson (entry : String × String) : String :=
  jsonObject [
    ("module", jsonString entry.1),
    ("assumption", jsonString entry.2)
  ]

private def ecmModuleJson (entry : ECM.ExternalCallModule) : String :=
  jsonObject [
    ("module", jsonString entry.name),
    ("status", proofStatusString entry.proofStatus),
    ("axioms", jsonArray (entry.axioms.map jsonString))
  ]

private def proofStatusBucketJson
    (primitives externals modules : List String) : String :=
  jsonObject [
    ("axiomatizedPrimitives", jsonArray (primitives.map jsonString)),
    ("linkedExternals", jsonArray (externals.map jsonString)),
    ("ecmModules", jsonArray (modules.map jsonString))
  ]

private def proofStatusJson (spec : CompilationModel) : String :=
  jsonObject [
    ("proved", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .proved)
      (collectUsedExternalNamesByStatus spec .proved)
      (collectUsedEcmModuleNamesByStatus spec .proved)),
    ("assumed", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .assumed)
      (collectUsedExternalNamesByStatus spec .assumed)
      (collectUsedEcmModuleNamesByStatus spec .assumed)),
    ("unchecked", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .unchecked)
      (collectUsedExternalNamesByStatus spec .unchecked)
      (collectUsedEcmModuleNamesByStatus spec .unchecked))
  ]

private def proofStatusBucketJsonForSite
    (primitives : List String)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule)
    (status : Compiler.ProofStatus) : String :=
  let primitiveBucket :=
    if status == .assumed then primitives.map jsonString else []
  let externalBucket :=
    (externals.filter (fun ext => ext.proofStatus == status)).map (fun ext => jsonString ext.name)
  let moduleBucket :=
    (modules.filter (fun mod => mod.proofStatus == status)).map (fun mod => jsonString mod.name)
  proofStatusBucketJson primitiveBucket externalBucket moduleBucket

private def proofStatusJsonForSite
    (primitives : List String)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule) : String :=
  jsonObject [
    ("proved", proofStatusBucketJsonForSite primitives externals modules .proved),
    ("assumed", proofStatusBucketJsonForSite primitives externals modules .assumed),
    ("unchecked", proofStatusBucketJsonForSite primitives externals modules .unchecked)
  ]

private def hasUncheckedDependenciesForSite
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule) : Bool :=
  externals.any (fun ext => ext.proofStatus == .unchecked) ||
    modules.any (fun mod => mod.proofStatus == .unchecked)

private def ecmAxiomsFromModules (modules : List ECM.ExternalCallModule) : List (String × String) :=
  modules.flatMap (fun mod => mod.axioms.map (fun assumption => (mod.name, assumption)))

private def siteHasTrustSurface (externals : List ExternalFunction) (stmts : List Stmt) : Bool :=
  !(collectLowLevelMechanicsFromStmts stmts).isEmpty ||
    !(collectAxiomatizedPrimitivesFromStmts stmts).isEmpty ||
    !(collectUsedExternalAssumptionsFromStmts externals stmts).isEmpty ||
    !(collectUsedEcmModulesFromStmts stmts).isEmpty

private def usageSitesJson (spec : CompilationModel) : String :=
  let siteJson (kind name : String) (stmts : List Stmt) : String :=
    let mechanics := collectLowLevelMechanicsFromStmts stmts
    let primitives := collectAxiomatizedPrimitivesFromStmts stmts
    let siteExternals := collectUsedExternalAssumptionsFromStmts spec.externals stmts
    let siteModules := collectUsedEcmModulesFromStmts stmts
    jsonObject [
      ("kind", jsonString kind),
      ("name", jsonString name),
      ("modeledLowLevelMechanics", jsonArray (mechanics.map jsonString)),
      ("axiomatizedPrimitives", jsonArray (primitives.map jsonString)),
      ("proofStatus", proofStatusJsonForSite primitives siteExternals siteModules),
      ("hasUncheckedDependencies",
        if hasUncheckedDependenciesForSite siteExternals siteModules then "true" else "false"),
      ("externalAssumptions", jsonObject [
        ("axiomatizedPrimitives", jsonArray (primitives.map primitiveAssumptionJson)),
        ("linkedExternals", jsonArray (siteExternals.map assumptionJson)),
        ("ecmAxioms", jsonArray ((ecmAxiomsFromModules siteModules).map ecmJson)),
        ("ecmModules", jsonArray (siteModules.map ecmModuleJson))
      ])
    ]
  let constructorSites :=
    match spec.constructor with
    | some ctor =>
        if siteHasTrustSurface spec.externals ctor.body then
          [siteJson "constructor" "constructor" ctor.body]
        else
          []
    | none => []
  let functionSites :=
    spec.functions.foldl
      (fun acc fn =>
        if siteHasTrustSurface spec.externals fn.body then
          acc ++ [siteJson "function" fn.name fn.body]
        else
          acc)
      []
  jsonArray (constructorSites ++ functionSites)

/-- True when a contract depends on any foreign surface marked `unchecked`. -/
def hasUncheckedDependencies (spec : CompilationModel) : Bool :=
  !(collectUsedExternalNamesByStatus spec .unchecked).isEmpty ||
    !(collectUsedEcmModuleNamesByStatus spec .unchecked).isEmpty

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
      ("axiomatizedPrimitives", jsonArray ((collectAxiomatizedPrimitives spec).map jsonString)),
      ("proofStatus", proofStatusJson spec),
      ("hasUncheckedDependencies", if hasUncheckedDependencies spec then "true" else "false"),
      ("proofBoundary", jsonObject [
        ("compilerModelsMechanics", "true"),
        ("proofInterpretersModelMechanics", "false"),
        ("calleeBehaviorRequiresAssumptions", "true")
      ]),
      ("usageSites", usageSitesJson spec),
      ("externalAssumptions", jsonObject [
        ("axiomatizedPrimitives",
          jsonArray ((collectAxiomatizedPrimitives spec).map primitiveAssumptionJson)),
        ("linkedExternals", jsonArray ((collectUsedExternalAssumptions spec).map assumptionJson)),
        ("ecmAxioms", jsonArray ((collectEcmAxioms spec).map ecmJson)),
        ("ecmModules", jsonArray ((collectUsedEcmModules spec).map ecmModuleJson))
      ])
    ]

end Compiler.CompilationModel
