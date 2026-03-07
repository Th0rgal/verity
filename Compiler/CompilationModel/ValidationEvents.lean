/- 
  Compiler.CompilationModel.ValidationEvents: Event and custom-error shape validation
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiTypeLayout
import Compiler.CompilationModel.EventAbiHelpers
import Compiler.CompilationModel.IssueRefs
import Compiler.CompilationModel.ScopeValidation

namespace Compiler.CompilationModel

def customErrorRequiresDirectParamRef : ParamType → Bool
  | ParamType.uint256 | ParamType.uint8 | ParamType.address | ParamType.bool | ParamType.bytes32 => false
  | _ => true

def validateDirectParamCustomErrorArg
    (fnName errorName : String) (params : List Param)
    (expectedTy : ParamType) (arg : Expr) : Except String Unit := do
  match arg with
  | Expr.param name =>
      match findParamType params name with
      | some ty =>
          if ty != expectedTy then
            throw s!"Compilation error: function '{fnName}' custom error '{errorName}' expects {repr expectedTy} arg to reference a matching parameter, got parameter '{name}' of type {repr ty} ({issue586Ref})."
      | none =>
          throw s!"Compilation error: function '{fnName}' custom error '{errorName}' references unknown parameter '{name}' ({issue586Ref})."
  | _ =>
      throw s!"Compilation error: function '{fnName}' custom error '{errorName}' parameter of type {repr expectedTy} currently requires direct parameter reference ({issue586Ref})."

mutual
def validateCustomErrorArgShapesInStmt (fnName : String) (params : List Param)
    (errors : List ErrorDef) : Stmt → Except String Unit
  | Stmt.requireError _ errorName args | Stmt.revertError errorName args => do
      let errorDef ←
        match errors.find? (·.name == errorName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown custom error '{errorName}' ({issue586Ref})"
      if errorDef.params.length != args.length then
        throw s!"Compilation error: custom error '{errorName}' expects {errorDef.params.length} args, got {args.length}"
      for (ty, arg) in errorDef.params.zip args do
        if customErrorRequiresDirectParamRef ty then
          validateDirectParamCustomErrorArg fnName errorName params ty arg
  | Stmt.ite _ thenBranch elseBranch => do
      validateCustomErrorArgShapesInStmtList fnName params errors thenBranch
      validateCustomErrorArgShapesInStmtList fnName params errors elseBranch
  | Stmt.forEach _ _ body =>
      validateCustomErrorArgShapesInStmtList fnName params errors body
  | _ => pure ()
termination_by s => sizeOf s
decreasing_by all_goals simp_wf; all_goals omega

def validateCustomErrorArgShapesInStmtList (fnName : String) (params : List Param)
    (errors : List ErrorDef) : List Stmt → Except String Unit
  | [] => pure ()
  | s :: ss => do
      validateCustomErrorArgShapesInStmt fnName params errors s
      validateCustomErrorArgShapesInStmtList fnName params errors ss
termination_by ss => sizeOf ss
decreasing_by all_goals simp_wf; all_goals omega
end

def validateCustomErrorArgShapesInFunction (spec : FunctionSpec) (errors : List ErrorDef) :
    Except String Unit := do
  spec.body.forM (validateCustomErrorArgShapesInStmt spec.name spec.params errors)

partial def validateEventArgShapesInStmt (fnName : String) (params : List Param)
    (events : List EventDef) : Stmt → Except String Unit
  | Stmt.emit eventName args => do
      let eventDef ←
        match events.find? (·.name == eventName) with
        | some defn => pure defn
        | none => throw s!"Compilation error: unknown event '{eventName}'"
      if eventDef.params.length != args.length then
        throw s!"Compilation error: event '{eventName}' expects {eventDef.params.length} args, got {args.length}"
      for (eventParam, arg) in eventDef.params.zip args do
        match arg with
        | Expr.param name =>
            match findParamType params name with
            | some ty =>
                if ty != eventParam.ty then
                  throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
            | none =>
                throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
        | _ => pure ()
        if eventParam.kind == EventParamKind.unindexed then
          match eventParam.ty with
          | ParamType.array elemTy =>
              if elemTy == ParamType.bytes then
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else if indexedDynamicArrayElemSupported elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else if eventIsDynamicType elemTy then
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              else
                throw s!"Compilation error: function '{fnName}' event '{eventName}' unindexed array param '{eventParam.name}' has unsupported element type {repr elemTy} ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
                match arg with
                | Expr.param name =>
                    match findParamType params name with
                    | some ty =>
                        if ty != eventParam.ty then
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                    | none =>
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                | _ =>
                    throw s!"Compilation error: function '{fnName}' unindexed composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | ParamType.bytes | ParamType.string =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes | some ParamType.string => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' unindexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' expects bytes/string arg to reference a matching parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' unindexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' unindexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes/string parameter reference ({issue586Ref})."
          | _ => pure ()
        if eventParam.kind == EventParamKind.indexed then
          match eventParam.ty with
          | ParamType.bytes | ParamType.string =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ParamType.bytes | some ParamType.string => pure ()
                  | some ty =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' expects bytes/string arg to reference a matching parameter, got {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' indexed dynamic-bytes event param '{eventParam.name}' in event '{eventName}' currently requires direct bytes/string parameter reference ({issue586Ref})."
          | ParamType.array elemTy =>
              match elemTy with
              | ParamType.bytes =>
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
              | _ =>
                  match arg with
                  | Expr.param name =>
                      match findParamType params name with
                      | some ty =>
                          if ty != eventParam.ty then
                            throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                      | none =>
                          throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
                  | _ =>
                      throw s!"Compilation error: function '{fnName}' indexed dynamic array event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | ParamType.fixedArray _ _ | ParamType.tuple _ =>
              match arg with
              | Expr.param name =>
                  match findParamType params name with
                  | some ty =>
                      if ty != eventParam.ty then
                        throw s!"Compilation error: function '{fnName}' event '{eventName}' param '{eventParam.name}' expects {repr eventParam.ty}, got parameter '{name}' of type {repr ty} ({issue586Ref})."
                  | none =>
                      throw s!"Compilation error: function '{fnName}' event '{eventName}' references unknown parameter '{name}' ({issue586Ref})."
              | _ =>
                  throw s!"Compilation error: function '{fnName}' indexed composite event param '{eventParam.name}' in event '{eventName}' currently requires direct parameter reference ({issue586Ref})."
          | _ => pure ()
  | Stmt.ite _ thenBranch elseBranch => do
      thenBranch.forM (validateEventArgShapesInStmt fnName params events)
      elseBranch.forM (validateEventArgShapesInStmt fnName params events)
  | Stmt.forEach _ _ body =>
      body.forM (validateEventArgShapesInStmt fnName params events)
  | _ => pure ()

def validateEventArgShapesInFunction (spec : FunctionSpec) (events : List EventDef) :
    Except String Unit := do
  spec.body.forM (validateEventArgShapesInStmt spec.name spec.params events)

end Compiler.CompilationModel
