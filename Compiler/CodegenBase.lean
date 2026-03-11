import Compiler.CodegenCommon

namespace Compiler.Base

open Compiler.Yul

abbrev BackendProfile := Compiler.CodegenCommon.BackendProfile
abbrev YulEmitOptions := Compiler.CodegenCommon.YulEmitOptions

def mappingSlotFuncAt := Compiler.CodegenCommon.mappingSlotFuncAt
def callvalueGuard := Compiler.CodegenCommon.callvalueGuard
def calldatasizeGuard := Compiler.CodegenCommon.calldatasizeGuard
def dispatchBody := Compiler.CodegenCommon.dispatchBody
def defaultDispatchCase := Compiler.CodegenCommon.defaultDispatchCase
def buildSwitch := Compiler.CodegenCommon.buildSwitch
def runtimeCode := Compiler.CodegenCommon.runtimeCode
def emitYul := Compiler.CodegenCommon.emitYul

private def patchBackend : Compiler.CodegenCommon.PatchBackend :=
  { apply := fun base _ =>
      { patched := base
        patchReport := { patched := base.runtimeCode, iterations := 0, manifest := [] } } }

def emitYulWithOptions (contract : IRContract) (options : YulEmitOptions) : YulObject :=
  Compiler.CodegenCommon.emitYulWithOptions patchBackend contract options

def emitYulWithOptionsReport (contract : IRContract) (options : YulEmitOptions) :
    YulObject × Yul.PatchPassReport :=
  Compiler.CodegenCommon.emitYulWithOptionsReport patchBackend contract options

end Compiler.Base
