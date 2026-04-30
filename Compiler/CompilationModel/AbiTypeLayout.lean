import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

-- Whether an ABI param type is dynamically sized (requires offset-based encoding).
-- Used by both event encoding and calldata parameter loading.
mutual
  def isDynamicParamType : ParamType → Bool
    | ParamType.uint256 => false
    | ParamType.int256 => false
    | ParamType.uint8 => false
    | ParamType.address => false
    | ParamType.bool => false
    | ParamType.bytes32 => false
    | ParamType.string => true
    | ParamType.array _ => true
    | ParamType.bytes => true
    | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
    | ParamType.tuple elemTys => isDynamicParamTypeList elemTys
    | ParamType.adt _ _ => false  -- ADTs are statically-sized tagged unions
    | ParamType.newtypeOf _ baseType => isDynamicParamType baseType  -- Erased to base type
  termination_by ty => sizeOf ty

  def isDynamicParamTypeList : List ParamType → Bool
    | [] => false
    | ty :: rest => isDynamicParamType ty || isDynamicParamTypeList rest
  termination_by tys => sizeOf tys
end

-- ABI head size in bytes for a param type. Dynamic types occupy one 32-byte
-- offset word; static composites are the sum of their element head sizes.
-- Used by both event encoding and calldata parameter loading.
mutual
  def paramHeadSize : ParamType → Nat
    | ParamType.uint256 => 32
    | ParamType.int256 => 32
    | ParamType.uint8 => 32
    | ParamType.address => 32
    | ParamType.bool => 32
    | ParamType.bytes32 => 32
    | ParamType.string => 32
    | ParamType.array _ => 32
    | ParamType.bytes => 32
    | ParamType.fixedArray elemTy n =>
        if isDynamicParamType elemTy then 32 else n * paramHeadSize elemTy
    | ParamType.tuple elemTys =>
        if isDynamicParamTypeList elemTys then 32 else paramHeadSizeList elemTys
    | ParamType.adt _ maxFields => 32 * (1 + maxFields)  -- ADTs: uint8 tag word + maxFields field words (#1727 Step 5e)
    | ParamType.newtypeOf _ baseType => paramHeadSize baseType  -- Erased to base type
  termination_by ty => sizeOf ty

  def paramHeadSizeList : List ParamType → Nat
    | [] => 0
    | ty :: rest => paramHeadSize ty + paramHeadSizeList rest
  termination_by tys => sizeOf tys
end

def eventIsDynamicType := isDynamicParamType

def eventHeadWordSize := paramHeadSize

/-- Number of 32-byte words in the local head of an ABI value once its dynamic
tail has been entered. Dynamic children occupy one offset word in that head. -/
partial def paramLocalHeadWords : ParamType → Nat
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.address
  | ParamType.bool | ParamType.bytes32 | ParamType.string | ParamType.bytes
  | ParamType.array _ => 1
  | ParamType.fixedArray elemTy n => n * paramLocalHeadWords elemTy
  | ParamType.tuple elemTys => elemTys.foldl (fun acc ty => acc + paramLocalHeadWords ty) 0
  | ParamType.adt _ maxFields => 1 + maxFields
  | ParamType.newtypeOf _ baseType => paramLocalHeadWords baseType

/-- Whether a parameter type is ABI-encoded as exactly one 32-byte word without
needing offset-based dynamic handling. -/
def isSingleWordStaticParamType (ty : ParamType) : Bool :=
  !isDynamicParamType ty && paramHeadSize ty == 32

/-- Dynamic array parameters whose elements can be copied/read word-for-word. -/
def isWordArrayParam : ParamType → Bool
  | ParamType.array elemTy => isSingleWordStaticParamType elemTy
  | _ => false

end Compiler.CompilationModel
