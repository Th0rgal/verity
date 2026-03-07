import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

-- Whether an ABI param type is dynamically sized (requires offset-based encoding).
-- Used by both event encoding and calldata parameter loading.
mutual
  def isDynamicParamType : ParamType → Bool
    | ParamType.uint256 => false
    | ParamType.uint8 => false
    | ParamType.address => false
    | ParamType.bool => false
    | ParamType.bytes32 => false
    | ParamType.string => true
    | ParamType.array _ => true
    | ParamType.bytes => true
    | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
    | ParamType.tuple elemTys => isDynamicParamTypeList elemTys
  termination_by ty => sizeOf ty

  private def isDynamicParamTypeList : List ParamType → Bool
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
  termination_by ty => sizeOf ty

  private def paramHeadSizeList : List ParamType → Nat
    | [] => 0
    | ty :: rest => paramHeadSize ty + paramHeadSizeList rest
  termination_by tys => sizeOf tys
end

def eventIsDynamicType := isDynamicParamType

def eventHeadWordSize := paramHeadSize

end Compiler.CompilationModel
