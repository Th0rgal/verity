import Compiler.CompilationModel.Dispatch

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace FunctionShape

def compiledFunctionIR
    (selector : Nat) (spec : FunctionSpec) (returns : List ParamType) (bodyStmts : List YulStmt) :
    IRFunction :=
  { name := spec.name
    selector := selector
    params := spec.params.map Param.toIRParam
    ret := match returns with
      | [single] => single.toIRType
      | _ => IRType.unit
    payable := spec.isPayable
    body := genParamLoads spec.params ++ bodyStmts }

theorem compileFunctionSpec_ok_components
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (selector : Nat) (spec : FunctionSpec) (irFn : IRFunction)
    (hcompile : compileFunctionSpec fields events errors [] selector spec = Except.ok irFn) :
    ∃ returns bodyStmts,
      validateFunctionSpec spec = Except.ok () ∧
      functionReturns spec = Except.ok returns ∧
      compileStmtList fields events errors .calldata [] false
        (spec.params.map (·.name)) [] spec.body = Except.ok bodyStmts ∧
      irFn = compiledFunctionIR selector spec returns bodyStmts := by
  unfold CompilationModel.compileFunctionSpec at hcompile
  cases hvalidate : validateFunctionSpec spec
  · rw [hvalidate] at hcompile
    cases hcompile
  case ok _ =>
    cases hreturns : functionReturns spec
    · rw [hvalidate, hreturns] at hcompile
      cases hcompile
    case ok returns =>
      cases hbody :
          compileStmtList fields events errors .calldata [] false
            (spec.params.map (·.name)) [] spec.body
      · rw [hvalidate, hreturns, hbody] at hcompile
        cases hcompile
      case ok bodyStmts =>
        rw [hvalidate, hreturns, hbody] at hcompile
        injection hcompile with hEq
        refine ⟨returns, bodyStmts, ?_⟩
        exact ⟨by simp, by simp, by simp, hEq.symm⟩

end FunctionShape

end Compiler.Proofs.IRGeneration
