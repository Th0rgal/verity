import Compiler.CompilationModel.Types
import Compiler.CompilationModel.EcmAxiomCollection
import Compiler.Json
import Compiler.ProofStatus

namespace Compiler.CompilationModel

open Compiler.Json

private def dedupPreserve (items : List String) : List String :=
  items.foldl (fun acc item => if acc.contains item then acc else acc ++ [item]) []

private def dedupExternalFunctions (items : List ExternalFunction) : List ExternalFunction :=
  items.foldl
    (fun acc item => if acc.any (fun prev => prev.name = item.name) then acc else acc ++ [item])
    []

private def dedupLocalObligations (items : List LocalObligation) : List LocalObligation :=
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
  | .mappingChain _ keys =>
      keys.flatMap collectLowLevelExprMechanics
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectLowLevelExprMechanics key1 ++ collectLowLevelExprMechanics key2
  | .mappingUint _ key
  | .storageArrayElement _ key
  | .arrayElement _ key =>
      collectLowLevelExprMechanics key
  | .mload key =>
      ["mload"] ++ collectLowLevelExprMechanics key
  | .calldataload key =>
      ["calldataload"] ++ collectLowLevelExprMechanics key
  | .extcodesize key =>
      ["extcodesize"] ++ collectLowLevelExprMechanics key
  | .keccak256 offset size =>
      collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics size
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectLowLevelExprMechanics
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .gt a b | .sgt a b | .lt a b | .slt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
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
  | .mappingChain _ keys =>
      keys.flatMap collectAxiomatizedExprPrimitives
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectAxiomatizedExprPrimitives key1 ++ collectAxiomatizedExprPrimitives key2
  | .mappingUint _ key
  | .storageArrayElement _ key
  | .arrayElement _ key =>
      collectAxiomatizedExprPrimitives key
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectAxiomatizedExprPrimitives
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .gt a b | .sgt a b | .lt a b | .slt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
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
  | .storageArrayPush _ value
  | .return value
  | .require value _ =>
      collectLowLevelExprMechanics value
  | .setStorageArrayElement _ index value =>
      collectLowLevelExprMechanics index ++ collectLowLevelExprMechanics value
  | .storageArrayPop _ =>
      []
  | .requireError cond _ args =>
      collectLowLevelExprMechanics cond ++ args.flatMap collectLowLevelExprMechanics
  | .revertError _ args =>
      args.flatMap collectLowLevelExprMechanics
  | .mstore offset value =>
      ["mstore"] ++ collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics value
  | .tstore offset value =>
      ["tstore"] ++ collectLowLevelExprMechanics offset ++ collectLowLevelExprMechanics value
  | .calldatacopy destOffset sourceOffset size =>
      ["calldatacopy"] ++ collectLowLevelExprMechanics destOffset ++
        collectLowLevelExprMechanics sourceOffset ++ collectLowLevelExprMechanics size
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
  | .setMappingChain _ keys value =>
      keys.flatMap collectLowLevelExprMechanics ++ collectLowLevelExprMechanics value
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
  | .storageArrayPush _ value
  | .return value
  | .require value _ =>
      collectAxiomatizedExprPrimitives value
  | .setStorageArrayElement _ index value =>
      collectAxiomatizedExprPrimitives index ++ collectAxiomatizedExprPrimitives value
  | .storageArrayPop _ =>
      []
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
  | .setMappingChain _ keys value =>
      keys.flatMap collectAxiomatizedExprPrimitives ++ collectAxiomatizedExprPrimitives value
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

private def isUnsafeBoundaryMechanic (mechanic : String) : Bool :=
  match mechanic with
  | "call" | "staticcall" | "delegatecall"
  | "returndataSize" | "returndataCopy" | "revertReturndata" | "returndataOptionalBoolAt"
  | "mload" | "mstore" | "calldataload" | "calldatacopy"
  | "extcodesize" | "tload" | "tstore" => true
  | _ => false

/-- Collect assembly-shaped low-level mechanics that require an explicit local obligation. -/
def collectUnsafeBoundaryMechanicsFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve ((collectLowLevelMechanicsFromStmts stmts).filter isUnsafeBoundaryMechanic)

private def isLinearMemoryMechanic (mechanic : String) : Bool :=
  match mechanic with
  | "mload" | "mstore" | "calldatacopy" | "returndataCopy" | "returndataOptionalBoolAt" => true
  | _ => false

private def collectLinearMemoryMechanicsFromMechanics (mechanics : List String) : List String :=
  dedupPreserve (mechanics.filter isLinearMemoryMechanic)

private def isProxyUpgradeabilityMechanic (mechanic : String) : Bool :=
  match mechanic with
  | "delegatecall" => true
  | _ => false

private def collectProxyUpgradeabilityMechanicsFromMechanics (mechanics : List String) : List String :=
  dedupPreserve (mechanics.filter isProxyUpgradeabilityMechanic)

private def isRuntimeIntrospectionMechanic (mechanic : String) : Bool :=
  match mechanic with
  | "blockNumber" | "contractAddress" | "chainid" => true
  | _ => false

private def collectRuntimeIntrospectionMechanicsFromMechanics (mechanics : List String) : List String :=
  dedupPreserve (mechanics.filter isRuntimeIntrospectionMechanic)

private partial def collectEventEmissionExprMechanics : Expr → List String
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectEventEmissionExprMechanics
  | .call gas target value inOffset inSize outOffset outSize =>
      collectEventEmissionExprMechanics gas ++ collectEventEmissionExprMechanics target ++
        collectEventEmissionExprMechanics value ++ collectEventEmissionExprMechanics inOffset ++
        collectEventEmissionExprMechanics inSize ++ collectEventEmissionExprMechanics outOffset ++
        collectEventEmissionExprMechanics outSize
  | .staticcall gas target inOffset inSize outOffset outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      collectEventEmissionExprMechanics gas ++ collectEventEmissionExprMechanics target ++
        collectEventEmissionExprMechanics inOffset ++ collectEventEmissionExprMechanics inSize ++
        collectEventEmissionExprMechanics outOffset ++ collectEventEmissionExprMechanics outSize
  | .returndataOptionalBoolAt outOffset
  | .mload outOffset
  | .tload outOffset
  | .calldataload outOffset
  | .extcodesize outOffset =>
      collectEventEmissionExprMechanics outOffset
  | .keccak256 offset size =>
      collectEventEmissionExprMechanics offset ++ collectEventEmissionExprMechanics size
  | .mapping _ key
  | .mappingWord _ key _
  | .mappingPackedWord _ key _ _
  | .structMember _ key _ =>
      collectEventEmissionExprMechanics key
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectEventEmissionExprMechanics key1 ++ collectEventEmissionExprMechanics key2
  | .mappingChain _ keys =>
      keys.flatMap collectEventEmissionExprMechanics
  | .mappingUint _ key
  | .arrayElement _ key =>
      collectEventEmissionExprMechanics key
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .gt a b | .sgt a b | .lt a b | .slt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
      collectEventEmissionExprMechanics a ++ collectEventEmissionExprMechanics b
  | .mulDivDown a b c | .mulDivUp a b c =>
      collectEventEmissionExprMechanics a ++ collectEventEmissionExprMechanics b ++
        collectEventEmissionExprMechanics c
  | .bitNot a | .logicalNot a =>
      collectEventEmissionExprMechanics a
  | .ite cond thenVal elseVal =>
      collectEventEmissionExprMechanics cond ++ collectEventEmissionExprMechanics thenVal ++
        collectEventEmissionExprMechanics elseVal
  | _ =>
      []

private partial def collectEventEmissionStmtMechanics : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .setStorage _ value
  | .setStorageAddr _ value
  | .storageArrayPush _ value
  | .return value
  | .require value _ =>
      collectEventEmissionExprMechanics value
  | .setStorageArrayElement _ index value =>
      collectEventEmissionExprMechanics index ++ collectEventEmissionExprMechanics value
  | .storageArrayPop _ =>
      []
  | .requireError cond _ args =>
      collectEventEmissionExprMechanics cond ++ args.flatMap collectEventEmissionExprMechanics
  | .revertError _ args =>
      args.flatMap collectEventEmissionExprMechanics
  | .mstore offset value
  | .tstore offset value =>
      collectEventEmissionExprMechanics offset ++ collectEventEmissionExprMechanics value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      collectEventEmissionExprMechanics destOffset ++ collectEventEmissionExprMechanics sourceOffset ++
        collectEventEmissionExprMechanics size
  | .setMapping _ key value
  | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value
  | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      collectEventEmissionExprMechanics key ++ collectEventEmissionExprMechanics value
  | .setMappingChain _ keys value =>
      keys.flatMap collectEventEmissionExprMechanics ++ collectEventEmissionExprMechanics value
  | .setMapping2 _ key1 key2 value
  | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      collectEventEmissionExprMechanics key1 ++ collectEventEmissionExprMechanics key2 ++
        collectEventEmissionExprMechanics value
  | .ite cond thenBr elseBr =>
      collectEventEmissionExprMechanics cond ++
        thenBr.flatMap collectEventEmissionStmtMechanics ++
        elseBr.flatMap collectEventEmissionStmtMechanics
  | .forEach _ count body =>
      collectEventEmissionExprMechanics count ++ body.flatMap collectEventEmissionStmtMechanics
  | .emit _ args
  | .internalCall _ args
  | .externalCallBind _ _ args
  | .returnValues args
  | .ecm _ args
  | .internalCallAssign _ _ args =>
      args.flatMap collectEventEmissionExprMechanics
  | .rawLog topics dataOffset dataSize =>
      ["rawLog"] ++ topics.flatMap collectEventEmissionExprMechanics ++
        collectEventEmissionExprMechanics dataOffset ++ collectEventEmissionExprMechanics dataSize
  | .returnArray _
  | .returnBytes _
  | .returnStorageWords _
  | .revertReturndata
  | .stop =>
      []

private def collectEventEmissionMechanicsFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve (stmts.flatMap collectEventEmissionStmtMechanics)

/-- Collect not-modeled raw event-emission mechanics used by a spec. -/
def collectEventEmissionMechanics (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectEventEmissionMechanicsFromStmts allStmts

private def isDeniedLowLevelMechanic (mechanic : String) : Bool :=
  match mechanic with
  | "call" | "staticcall" | "delegatecall" | "returndataSize" | "returndataCopy"
  | "revertReturndata" | "returndataOptionalBoolAt" => true
  | _ => false

private def collectDeniedLowLevelMechanicsFromMechanics (mechanics : List String) : List String :=
  dedupPreserve (mechanics.filter isDeniedLowLevelMechanic)

/-- Collect unique low-level call and returndata mechanics used by a spec. -/
def collectLowLevelMechanics (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectLowLevelMechanicsFromStmts allStmts

/-- Collect partially modeled linear-memory mechanics used by a spec. -/
def collectLinearMemoryMechanics (spec : CompilationModel) : List String :=
  collectLinearMemoryMechanicsFromMechanics (collectLowLevelMechanics spec)

/-- Collect not-modeled proxy / upgradeability mechanics used by a spec. -/
def collectProxyUpgradeabilityMechanics (spec : CompilationModel) : List String :=
  collectProxyUpgradeabilityMechanicsFromMechanics (collectLowLevelMechanics spec)

private partial def collectRuntimeIntrospectionExprMechanics : Expr → List String
  | .contractAddress => ["contractAddress"]
  | .chainid => ["chainid"]
  | .blockNumber => ["blockNumber"]
  | .externalCall _ args
  | .internalCall _ args =>
      args.flatMap collectRuntimeIntrospectionExprMechanics
  | .call gas target value inOffset inSize outOffset outSize =>
      collectRuntimeIntrospectionExprMechanics gas ++ collectRuntimeIntrospectionExprMechanics target ++
        collectRuntimeIntrospectionExprMechanics value ++ collectRuntimeIntrospectionExprMechanics inOffset ++
        collectRuntimeIntrospectionExprMechanics inSize ++ collectRuntimeIntrospectionExprMechanics outOffset ++
        collectRuntimeIntrospectionExprMechanics outSize
  | .staticcall gas target inOffset inSize outOffset outSize
  | .delegatecall gas target inOffset inSize outOffset outSize =>
      collectRuntimeIntrospectionExprMechanics gas ++ collectRuntimeIntrospectionExprMechanics target ++
        collectRuntimeIntrospectionExprMechanics inOffset ++ collectRuntimeIntrospectionExprMechanics inSize ++
        collectRuntimeIntrospectionExprMechanics outOffset ++ collectRuntimeIntrospectionExprMechanics outSize
  | .returndataOptionalBoolAt outOffset
  | .mload outOffset
  | .tload outOffset
  | .calldataload outOffset
  | .extcodesize outOffset =>
      collectRuntimeIntrospectionExprMechanics outOffset
  | .keccak256 offset size =>
      collectRuntimeIntrospectionExprMechanics offset ++ collectRuntimeIntrospectionExprMechanics size
  | .mapping _ key
  | .mappingWord _ key _
  | .mappingPackedWord _ key _ _
  | .structMember _ key _ =>
      collectRuntimeIntrospectionExprMechanics key
  | .mapping2 _ key1 key2
  | .mapping2Word _ key1 key2 _
  | .structMember2 _ key1 key2 _ =>
      collectRuntimeIntrospectionExprMechanics key1 ++ collectRuntimeIntrospectionExprMechanics key2
  | .mappingChain _ keys =>
      keys.flatMap collectRuntimeIntrospectionExprMechanics
  | .mappingUint _ key
  | .arrayElement _ key =>
      collectRuntimeIntrospectionExprMechanics key
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .gt a b | .sgt a b | .lt a b | .slt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
      collectRuntimeIntrospectionExprMechanics a ++ collectRuntimeIntrospectionExprMechanics b
  | .mulDivDown a b c | .mulDivUp a b c =>
      collectRuntimeIntrospectionExprMechanics a ++ collectRuntimeIntrospectionExprMechanics b ++
        collectRuntimeIntrospectionExprMechanics c
  | .bitNot a | .logicalNot a =>
      collectRuntimeIntrospectionExprMechanics a
  | .ite cond thenVal elseVal =>
      collectRuntimeIntrospectionExprMechanics cond ++ collectRuntimeIntrospectionExprMechanics thenVal ++
        collectRuntimeIntrospectionExprMechanics elseVal
  | _ =>
      []

private partial def collectRuntimeIntrospectionStmtMechanics : Stmt → List String
  | .letVar _ value
  | .assignVar _ value
  | .setStorage _ value
  | .setStorageAddr _ value
  | .storageArrayPush _ value
  | .return value
  | .require value _ =>
      collectRuntimeIntrospectionExprMechanics value
  | .setStorageArrayElement _ index value =>
      collectRuntimeIntrospectionExprMechanics index ++ collectRuntimeIntrospectionExprMechanics value
  | .storageArrayPop _ =>
      []
  | .requireError cond _ args =>
      collectRuntimeIntrospectionExprMechanics cond ++ args.flatMap collectRuntimeIntrospectionExprMechanics
  | .revertError _ args =>
      args.flatMap collectRuntimeIntrospectionExprMechanics
  | .mstore offset value
  | .tstore offset value =>
      collectRuntimeIntrospectionExprMechanics offset ++ collectRuntimeIntrospectionExprMechanics value
  | .calldatacopy destOffset sourceOffset size
  | .returndataCopy destOffset sourceOffset size =>
      collectRuntimeIntrospectionExprMechanics destOffset ++
        collectRuntimeIntrospectionExprMechanics sourceOffset ++
        collectRuntimeIntrospectionExprMechanics size
  | .setMapping _ key value
  | .setMappingWord _ key _ value
  | .setMappingPackedWord _ key _ _ value
  | .setMappingUint _ key value
  | .setStructMember _ key _ value =>
      collectRuntimeIntrospectionExprMechanics key ++ collectRuntimeIntrospectionExprMechanics value
  | .setMappingChain _ keys value =>
      keys.flatMap collectRuntimeIntrospectionExprMechanics ++ collectRuntimeIntrospectionExprMechanics value
  | .setMapping2 _ key1 key2 value
  | .setMapping2Word _ key1 key2 _ value
  | .setStructMember2 _ key1 key2 _ value =>
      collectRuntimeIntrospectionExprMechanics key1 ++ collectRuntimeIntrospectionExprMechanics key2 ++
        collectRuntimeIntrospectionExprMechanics value
  | .ite cond thenBr elseBr =>
      collectRuntimeIntrospectionExprMechanics cond ++
        thenBr.flatMap collectRuntimeIntrospectionStmtMechanics ++
        elseBr.flatMap collectRuntimeIntrospectionStmtMechanics
  | .forEach _ count body =>
      collectRuntimeIntrospectionExprMechanics count ++ body.flatMap collectRuntimeIntrospectionStmtMechanics
  | .emit _ args
  | .internalCall _ args
  | .returnValues args
  | .ecm _ args
  | .internalCallAssign _ _ args =>
      args.flatMap collectRuntimeIntrospectionExprMechanics
  | .externalCallBind _ _ args =>
      args.flatMap collectRuntimeIntrospectionExprMechanics
  | .rawLog topics dataOffset dataSize =>
      topics.flatMap collectRuntimeIntrospectionExprMechanics ++
        collectRuntimeIntrospectionExprMechanics dataOffset ++
        collectRuntimeIntrospectionExprMechanics dataSize
  | .returnArray _
  | .returnBytes _
  | .returnStorageWords _
  | .revertReturndata
  | .stop =>
      []

private def collectRuntimeIntrospectionMechanicsFromStmts (stmts : List Stmt) : List String :=
  dedupPreserve (stmts.flatMap collectRuntimeIntrospectionStmtMechanics)

/-- Collect partially modeled runtime-introspection mechanics used by a spec. -/
def collectRuntimeIntrospectionMechanics (spec : CompilationModel) : List String :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  collectRuntimeIntrospectionMechanicsFromStmts allStmts

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
  | .mappingChain _ keys =>
      keys.flatMap collectExternalExprNames
  | .mappingUint _ key
  | .arrayElement _ key =>
      collectExternalExprNames key
  | .internalCall _ args =>
      args.flatMap collectExternalExprNames
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b | .signextend a b
  | .eq a b | .gt a b | .sgt a b | .lt a b | .slt a b | .ge a b | .le a b
  | .logicalAnd a b | .logicalOr a b
  | .wMulDown a b | .wDivUp a b | .min a b | .max a b | .ceilDiv a b =>
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
  | .storageArrayPush _ value
  | .return value
  | .require value _ =>
      collectExternalExprNames value
  | .setStorageArrayElement _ index value =>
      collectExternalExprNames index ++ collectExternalExprNames value
  | .storageArrayPop _ =>
      []
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
  | .setMappingChain _ keys value =>
      keys.flatMap collectExternalExprNames ++ collectExternalExprNames value
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

private def collectLocalObligationsFromStmts
    (obligations : List LocalObligation)
    (_stmts : List Stmt) : List LocalObligation :=
  obligations

private def collectConstructorLocalObligations (spec : CompilationModel) : List LocalObligation :=
  match spec.constructor with
  | some ctor => ctor.localObligations
  | none => []

/-- Collect local proof obligations attached to functions/constructors. -/
def collectLocalObligations (spec : CompilationModel) : List LocalObligation :=
  let functionObligations := spec.functions.flatMap (·.localObligations)
  dedupLocalObligations (collectConstructorLocalObligations spec ++ functionObligations)

private def collectLocalObligationNamesByStatus
    (spec : CompilationModel)
    (status : Compiler.ProofStatus) : List String :=
  (collectLocalObligations spec).foldl
    (fun acc obligation =>
      if obligation.proofStatus == status then acc ++ [obligation.name] else acc)
    []

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

private def localObligationJson (entry : LocalObligation) : String :=
  jsonObject [
    ("name", jsonString entry.name),
    ("status", proofStatusString entry.proofStatus),
    ("obligation", jsonString entry.obligation)
  ]

private structure AssumptionReportEntry where
  category : String
  siteKind : String
  siteName : String
  name : String
  status : ProofStatus
  detail : String := ""
  assumption : String := ""
  moduleName : String := ""
  axioms : List String := []

private def assumptionReportEntryJson (entry : AssumptionReportEntry) : String :=
  jsonObject [
    ("category", jsonString entry.category),
    ("siteKind", jsonString entry.siteKind),
    ("siteName", jsonString entry.siteName),
    ("name", jsonString entry.name),
    ("status", proofStatusString entry.status),
    ("detail", jsonString entry.detail),
    ("assumption", jsonString entry.assumption),
    ("module", jsonString entry.moduleName),
    ("axioms", jsonArray (entry.axioms.map jsonString))
  ]

private def proofStatusBucketJson
    (primitives externals modules localObligations : List String) : String :=
  jsonObject [
    ("axiomatizedPrimitives", jsonArray (primitives.map jsonString)),
    ("linkedExternals", jsonArray (externals.map jsonString)),
    ("ecmModules", jsonArray (modules.map jsonString)),
    ("localObligations", jsonArray (localObligations.map jsonString))
  ]

private def proofStatusJson (spec : CompilationModel) : String :=
  jsonObject [
    ("proved", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .proved)
      (collectUsedExternalNamesByStatus spec .proved)
      (collectUsedEcmModuleNamesByStatus spec .proved)
      (collectLocalObligationNamesByStatus spec .proved)),
    ("assumed", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .assumed)
      (collectUsedExternalNamesByStatus spec .assumed)
      (collectUsedEcmModuleNamesByStatus spec .assumed)
      (collectLocalObligationNamesByStatus spec .assumed)),
    ("unchecked", proofStatusBucketJson
      (collectAxiomatizedPrimitivesByStatus spec .unchecked)
      (collectUsedExternalNamesByStatus spec .unchecked)
      (collectUsedEcmModuleNamesByStatus spec .unchecked)
      (collectLocalObligationNamesByStatus spec .unchecked))
  ]

private def proofStatusBucketJsonForSite
    (primitives : List String)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule)
    (localObligations : List LocalObligation)
    (status : Compiler.ProofStatus) : String :=
  let primitiveBucket :=
    if status == .assumed then primitives.map jsonString else []
  let externalBucket :=
    (externals.filter (fun ext => ext.proofStatus == status)).map (fun ext => jsonString ext.name)
  let moduleBucket :=
    (modules.filter (fun mod => mod.proofStatus == status)).map (fun mod => jsonString mod.name)
  let localObligationBucket :=
    (localObligations.filter (fun obligation => obligation.proofStatus == status)).map
      (fun obligation => jsonString obligation.name)
  proofStatusBucketJson primitiveBucket externalBucket moduleBucket localObligationBucket

private def proofStatusJsonForSite
    (primitives : List String)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule)
    (localObligations : List LocalObligation) : String :=
  jsonObject [
    ("proved", proofStatusBucketJsonForSite primitives externals modules localObligations .proved),
    ("assumed", proofStatusBucketJsonForSite primitives externals modules localObligations .assumed),
    ("unchecked", proofStatusBucketJsonForSite primitives externals modules localObligations .unchecked)
  ]

private def hasUncheckedDependenciesForSite
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule) : Bool :=
  externals.any (fun ext => ext.proofStatus == .unchecked) ||
    modules.any (fun mod => mod.proofStatus == .unchecked)

private def hasDependenciesForStatusesForSite
    (statuses : List Compiler.ProofStatus)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule) : Bool :=
  externals.any (fun ext => statuses.contains ext.proofStatus) ||
    modules.any (fun mod => statuses.contains mod.proofStatus)

private structure UsageSiteSummary where
  kind : String
  name : String
  mechanics : List String
  eventEmission : List String
  proxyUpgradeability : List String
  runtimeIntrospection : List String
  primitives : List String
  externals : List ExternalFunction
  modules : List ECM.ExternalCallModule
  localObligations : List LocalObligation

private def ecmAxiomsFromModules (modules : List ECM.ExternalCallModule) : List (String × String) :=
  modules.flatMap (fun mod => mod.axioms.map (fun assumption => (mod.name, assumption)))

private def siteHasTrustSurface
    (externals : List ExternalFunction)
    (localObligations : List LocalObligation)
    (stmts : List Stmt) : Bool :=
  !(collectLowLevelMechanicsFromStmts stmts).isEmpty ||
    !(collectEventEmissionMechanicsFromStmts stmts).isEmpty ||
    !(collectProxyUpgradeabilityMechanicsFromMechanics (collectLowLevelMechanicsFromStmts stmts)).isEmpty ||
    !(collectRuntimeIntrospectionMechanicsFromStmts stmts).isEmpty ||
    !(collectAxiomatizedPrimitivesFromStmts stmts).isEmpty ||
    !(collectUsedExternalAssumptionsFromStmts externals stmts).isEmpty ||
    !(collectUsedEcmModulesFromStmts stmts).isEmpty ||
    !(collectLocalObligationsFromStmts localObligations stmts).isEmpty

private def usageSiteSummary
    (spec : CompilationModel)
    (kind name : String)
    (localObligations : List LocalObligation)
    (stmts : List Stmt) :
    UsageSiteSummary :=
  let mechanics := collectLowLevelMechanicsFromStmts stmts
  let eventEmission := collectEventEmissionMechanicsFromStmts stmts
  let proxyUpgradeability := collectProxyUpgradeabilityMechanicsFromMechanics mechanics
  let runtimeIntrospection := collectRuntimeIntrospectionMechanicsFromStmts stmts
  let primitives := collectAxiomatizedPrimitivesFromStmts stmts
  let siteExternals := collectUsedExternalAssumptionsFromStmts spec.externals stmts
  let siteModules := collectUsedEcmModulesFromStmts stmts
  let siteLocalObligations := collectLocalObligationsFromStmts localObligations stmts
  { kind := kind
    name := name
    mechanics := mechanics
    eventEmission := eventEmission
    proxyUpgradeability := proxyUpgradeability
    runtimeIntrospection := runtimeIntrospection
    primitives := primitives
    externals := siteExternals
    modules := siteModules
    localObligations := siteLocalObligations }

private def collectUsageSiteSummaries (spec : CompilationModel) : List UsageSiteSummary :=
  let constructorSites :=
    match spec.constructor with
    | some ctor =>
        if siteHasTrustSurface spec.externals ctor.localObligations ctor.body then
          [usageSiteSummary spec "constructor" "constructor" ctor.localObligations ctor.body]
        else
          []
    | none => []
  let functionSites :=
    spec.functions.foldl
      (fun acc fn =>
        if siteHasTrustSurface spec.externals fn.localObligations fn.body then
          acc ++ [usageSiteSummary spec "function" fn.name fn.localObligations fn.body]
        else
          acc)
      []
  constructorSites ++ functionSites

private def usageSitesJson (spec : CompilationModel) : String :=
  let siteJson (site : UsageSiteSummary) : String :=
    let linearMemoryMechanics := collectLinearMemoryMechanicsFromMechanics site.mechanics
    jsonObject [
      ("kind", jsonString site.kind),
      ("name", jsonString site.name),
      ("modeledLowLevelMechanics", jsonArray (site.mechanics.map jsonString)),
      ("notModeledEventEmission", jsonArray (site.eventEmission.map jsonString)),
      ("notModeledProxyUpgradeability", jsonArray (site.proxyUpgradeability.map jsonString)),
      ("partiallyModeledLinearMemoryMechanics", jsonArray (linearMemoryMechanics.map jsonString)),
      ("partiallyModeledRuntimeIntrospection", jsonArray (site.runtimeIntrospection.map jsonString)),
      ("axiomatizedPrimitives", jsonArray (site.primitives.map jsonString)),
      ("proofStatus", proofStatusJsonForSite site.primitives site.externals site.modules site.localObligations),
      ("localObligations", jsonArray (site.localObligations.map localObligationJson)),
      ("hasUncheckedDependencies",
        if hasUncheckedDependenciesForSite site.externals site.modules then "true" else "false"),
      ("externalAssumptions", jsonObject [
        ("axiomatizedPrimitives", jsonArray (site.primitives.map primitiveAssumptionJson)),
        ("linkedExternals", jsonArray (site.externals.map assumptionJson)),
        ("ecmAxioms", jsonArray ((ecmAxiomsFromModules site.modules).map ecmJson)),
        ("ecmModules", jsonArray (site.modules.map ecmModuleJson))
      ])
    ]
  jsonArray ((collectUsageSiteSummaries spec).map siteJson)

private def assumptionReportEntriesForSite (site : UsageSiteSummary) : List AssumptionReportEntry :=
  let primitiveEntries :=
    site.primitives.map (fun primitive =>
      { category := "axiomatizedPrimitive"
        siteKind := site.kind
        siteName := site.name
        name := primitive
        status := .assumed
        assumption := primitiveAssumptionName primitive })
  let externalEntries :=
    site.externals.map (fun ext =>
      { category := "linkedExternal"
        siteKind := site.kind
        siteName := site.name
        name := ext.name
        status := ext.proofStatus
        axioms := ext.axiomNames })
  let moduleEntries :=
    site.modules.map (fun mod =>
      { category := "ecmModule"
        siteKind := site.kind
        siteName := site.name
        name := mod.name
        status := mod.proofStatus
        axioms := mod.axioms })
  let axiomEntries :=
    site.modules.flatMap (fun mod =>
      mod.axioms.map (fun assumptionName =>
        { category := "ecmAxiom"
          siteKind := site.kind
          siteName := site.name
          name := assumptionName
          status := mod.proofStatus
          moduleName := mod.name }))
  let localObligationEntries :=
    site.localObligations.map (fun obligation =>
      { category := "localObligation"
        siteKind := site.kind
        siteName := site.name
        name := obligation.name
        status := obligation.proofStatus
        detail := obligation.obligation })
  primitiveEntries ++ externalEntries ++ moduleEntries ++ axiomEntries ++ localObligationEntries

private def assumptionReportEntries (spec : CompilationModel) : List AssumptionReportEntry :=
  (collectUsageSiteSummaries spec).flatMap assumptionReportEntriesForSite

private def undischargedAssumptionReportEntries (spec : CompilationModel) : List AssumptionReportEntry :=
  (assumptionReportEntries spec).filter (fun entry => entry.status != .proved)

private def namesByProofStatus
    (status : ProofStatus)
    (externals : List ExternalFunction)
    (modules : List ECM.ExternalCallModule) : (List String × List String) :=
  let externalNames := externals.foldl
    (fun acc ext => if ext.proofStatus == status then acc ++ [ext.name] else acc)
    []
  let moduleNames := modules.foldl
    (fun acc mod => if mod.proofStatus == status then acc ++ [mod.name] else acc)
    []
  (externalNames, moduleNames)

/-- Render localized trust-surface lines for verbose compiler output. -/
def emitVerboseUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            let (provedExternals, provedModules) :=
              namesByProofStatus .proved site.externals site.modules
            let (assumedExternals, assumedModules) :=
              namesByProofStatus .assumed site.externals site.modules
            let (uncheckedExternals, uncheckedModules) :=
              namesByProofStatus .unchecked site.externals site.modules
            let provedLocalObligations :=
              site.localObligations.foldl
                (fun acc obligation =>
                  if obligation.proofStatus == .proved then acc ++ [obligation.name] else acc)
                []
            let assumedLocalObligations :=
              site.localObligations.foldl
                (fun acc obligation =>
                  if obligation.proofStatus == .assumed then acc ++ [obligation.name] else acc)
                []
            let uncheckedLocalObligations :=
              site.localObligations.foldl
                (fun acc obligation =>
                  if obligation.proofStatus == .unchecked then acc ++ [obligation.name] else acc)
                []
            let heading := s!"  {spec.name} [{site.kind}:{site.name}]"
            let mechanicsLines :=
              if site.mechanics.isEmpty then [] else
                [s!"    low-level mechanics: {String.intercalate ", " site.mechanics}"]
            let eventEmissionLines :=
              if site.eventEmission.isEmpty then [] else
                [s!"    not modeled event emission: {String.intercalate ", " site.eventEmission}"]
            let proxyUpgradeabilityLines :=
              if site.proxyUpgradeability.isEmpty then [] else
                [s!"    not modeled proxy / upgradeability: {String.intercalate ", " site.proxyUpgradeability}"]
            let linearMemoryMechanics := collectLinearMemoryMechanicsFromMechanics site.mechanics
            let linearMemoryLines :=
              if linearMemoryMechanics.isEmpty then [] else
                [s!"    partially modeled linear memory: {String.intercalate ", " linearMemoryMechanics}"]
            let runtimeIntrospectionLines :=
              if site.runtimeIntrospection.isEmpty then [] else
                [s!"    partially modeled runtime introspection: {String.intercalate ", " site.runtimeIntrospection}"]
            let primitiveLines :=
              if site.primitives.isEmpty then [] else
                [s!"    axiomatized primitives: {String.intercalate ", " site.primitives}"] ++
                site.primitives.map
                  (fun primitive =>
                    s!"    [primitive:{primitive}][assumed] {primitiveAssumptionName primitive}")
            let provedLocalObligationLines :=
              if provedLocalObligations.isEmpty then [] else
                [s!"    proved local obligations: {String.intercalate ", " provedLocalObligations}"]
            let assumedLocalObligationLines :=
              if assumedLocalObligations.isEmpty then [] else
                [s!"    assumed local obligations: {String.intercalate ", " assumedLocalObligations}"]
            let uncheckedLocalObligationLines :=
              if uncheckedLocalObligations.isEmpty then [] else
                [s!"    unchecked local obligations: {String.intercalate ", " uncheckedLocalObligations}"]
            let provedLines :=
              (if provedExternals.isEmpty then [] else
                [s!"    proved linked externals: {String.intercalate ", " provedExternals}"]) ++
              (if provedModules.isEmpty then [] else
                [s!"    proved ECM modules: {String.intercalate ", " provedModules}"])
            let assumedLines :=
              (if assumedExternals.isEmpty then [] else
                [s!"    assumed linked externals: {String.intercalate ", " assumedExternals}"]) ++
              (if assumedModules.isEmpty then [] else
                [s!"    assumed ECM modules: {String.intercalate ", " assumedModules}"])
            let uncheckedLines :=
              (if uncheckedExternals.isEmpty then [] else
                [s!"    unchecked linked externals: {String.intercalate ", " uncheckedExternals}"]) ++
              (if uncheckedModules.isEmpty then [] else
                [s!"    unchecked ECM modules: {String.intercalate ", " uncheckedModules}"])
            let externalAssumptionLines :=
              site.externals.foldl
                (fun extAcc ext =>
                  let renderedAxioms :=
                    if ext.axiomNames.isEmpty then "(no declared axioms)"
                    else String.intercalate ", " ext.axiomNames
                  extAcc ++
                    [s!"    [linked:{ext.name}][{ext.proofStatus.toJsonString}] {renderedAxioms}"])
                []
            let ecmAxiomLines :=
              site.modules.foldl
                (fun modAcc mod =>
                  let assumptionLines :=
                    mod.axioms.map
                      (fun assumption =>
                        s!"    [ecm:{mod.name}][{mod.proofStatus.toJsonString}] {assumption}")
                  if assumptionLines.isEmpty then
                    modAcc ++ [s!"    [ecm:{mod.name}][{mod.proofStatus.toJsonString}] (no declared axioms)"]
                  else
                    modAcc ++ assumptionLines)
                []
            let localObligationLines :=
              site.localObligations.map
                (fun obligation =>
                  s!"    [local:{obligation.name}][{obligation.proofStatus.toJsonString}] {obligation.obligation}")
            siteAcc ++
              [heading] ++
              mechanicsLines ++
              eventEmissionLines ++
              proxyUpgradeabilityLines ++
              linearMemoryLines ++
              runtimeIntrospectionLines ++
              primitiveLines ++
              provedLocalObligationLines ++
              provedLines ++
              assumedLocalObligationLines ++
              assumedLines ++
              uncheckedLocalObligationLines ++
              uncheckedLines ++
              externalAssumptionLines ++
              ecmAxiomLines ++
              localObligationLines)
          []
      acc ++ siteLines)
    []

/-- Render localized unchecked-foreign-dependency lines for fail-closed diagnostics. -/
private def emitUsageSiteLinesForStatuses
    (specs : List CompilationModel)
    (statuses : List Compiler.ProofStatus) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            let dependencyCategories :=
              statuses.foldl
                (fun categoryAcc status =>
                  let (externals, modules) := namesByProofStatus status site.externals site.modules
                  categoryAcc ++
                    (if externals.isEmpty then [] else
                      [s!"{status.toJsonString} linked externals: {String.intercalate ", " externals}"]) ++
                    (if modules.isEmpty then [] else
                      [s!"{status.toJsonString} ECM modules: {String.intercalate ", " modules}"]))
                []
            if dependencyCategories.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate "; " dependencyCategories}"])
          []
      acc ++ siteLines)
    []

/-- Render localized unchecked-foreign-dependency lines for fail-closed diagnostics. -/
def emitUncheckedUsageSiteLines (specs : List CompilationModel) : List String :=
  emitUsageSiteLinesForStatuses specs [.unchecked]

/-- Render localized assumed-or-unchecked foreign-dependency lines for proof-strict diagnostics. -/
def emitAssumedUsageSiteLines (specs : List CompilationModel) : List String :=
  emitUsageSiteLinesForStatuses specs [.assumed, .unchecked]

/-- Render localized partially modeled linear-memory lines for proof-strict diagnostics. -/
def emitLinearMemoryUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            let linearMemoryMechanics := collectLinearMemoryMechanicsFromMechanics site.mechanics
            if linearMemoryMechanics.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " linearMemoryMechanics}"])
          []
      acc ++ siteLines)
    []

/-- Render localized partially modeled runtime-introspection lines for proof-strict diagnostics. -/
def emitRuntimeIntrospectionUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            if site.runtimeIntrospection.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " site.runtimeIntrospection}"])
          []
      acc ++ siteLines)
    []

/-- Render localized not-modeled event-emission lines for proof-strict diagnostics. -/
def emitEventEmissionUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            if site.eventEmission.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " site.eventEmission}"])
          []
      acc ++ siteLines)
    []

/-- Render localized not-modeled proxy / upgradeability lines for proof-strict diagnostics. -/
def emitProxyUpgradeabilityUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            if site.proxyUpgradeability.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " site.proxyUpgradeability}"])
          []
      acc ++ siteLines)
    []

/-- Render localized axiomatized-primitive lines for proof-strict diagnostics. -/
def emitAxiomatizedPrimitiveUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            if site.primitives.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " site.primitives}"])
          []
      acc ++ siteLines)
    []

/-- Render localized undischarged local-obligation lines for proof-strict diagnostics. -/
def emitLocalObligationUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            let undischarged :=
              site.localObligations.filter (fun obligation => obligation.proofStatus != .proved)
            if undischarged.isEmpty then
              siteAcc
            else
              let rendered :=
                undischarged.map
                  (fun obligation =>
                    s!"{obligation.proofStatus.toJsonString} local obligations: {obligation.name}")
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate "; " rendered}"])
          []
      acc ++ siteLines)
    []

/-- Render localized low-level-mechanics lines for fail-closed diagnostics. -/
def emitLowLevelMechanicsUsageSiteLines (specs : List CompilationModel) : List String :=
  specs.foldl
    (fun acc spec =>
      let siteLines :=
        (collectUsageSiteSummaries spec).foldl
          (fun siteAcc site =>
            let lowLevelMechanics := collectDeniedLowLevelMechanicsFromMechanics site.mechanics
            if lowLevelMechanics.isEmpty then
              siteAcc
            else
              siteAcc ++
                [s!"- {spec.name} [{site.kind}:{site.name}]: {String.intercalate ", " lowLevelMechanics}"])
          []
      acc ++ siteLines)
    []

/-- True when a contract depends on any foreign surface marked `unchecked`. -/
def hasUncheckedDependencies (spec : CompilationModel) : Bool :=
  !(collectUsedExternalNamesByStatus spec .unchecked).isEmpty ||
    !(collectUsedEcmModuleNamesByStatus spec .unchecked).isEmpty

/-- True when a contract depends on any foreign surface that remains assumed or unchecked. -/
def hasAssumedDependencies (spec : CompilationModel) : Bool :=
  hasDependenciesForStatusesForSite [.assumed, .unchecked]
    (collectUsedExternalAssumptions spec)
    (collectUsedEcmModules spec)

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
      ("notModeledEventEmission", jsonArray ((collectEventEmissionMechanics spec).map jsonString)),
      ("notModeledProxyUpgradeability", jsonArray ((collectProxyUpgradeabilityMechanics spec).map jsonString)),
      ("partiallyModeledLinearMemoryMechanics", jsonArray ((collectLinearMemoryMechanics spec).map jsonString)),
      ("partiallyModeledRuntimeIntrospection", jsonArray ((collectRuntimeIntrospectionMechanics spec).map jsonString)),
      ("axiomatizedPrimitives", jsonArray ((collectAxiomatizedPrimitives spec).map jsonString)),
      ("localObligations", jsonArray ((collectLocalObligations spec).map localObligationJson)),
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

/-- Render a flat machine-readable assumption inventory for audit workflows. -/
def emitAssumptionReportJson (specs : List CompilationModel) : String :=
  jsonObject [
    ("contracts", jsonArray (specs.map contractJson))
  ]
where
  contractJson (spec : CompilationModel) : String :=
    jsonObject [
      ("contract", jsonString spec.name),
      ("entries", jsonArray ((assumptionReportEntries spec).map assumptionReportEntryJson)),
      ("undischarged", jsonArray ((undischargedAssumptionReportEntries spec).map assumptionReportEntryJson))
    ]

end Compiler.CompilationModel
