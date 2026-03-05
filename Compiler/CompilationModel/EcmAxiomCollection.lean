import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

/-- Collect all unique (moduleName, axiom) pairs from ECM statements in a spec.
    Used for axiom aggregation reports. -/
def collectEcmAxioms (spec : CompilationModel) : List (String × String) :=
  let stmtsFromFn (fn : FunctionSpec) := fn.body
  let stmtsFromCtor : List Stmt := match spec.constructor with
    | some ctor => ctor.body
    | none => []
  let allStmts := stmtsFromCtor ++ spec.functions.flatMap stmtsFromFn
  let pairs := allStmts.flatMap collectStmtEcmAxioms
  pairs.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []
where
  collectStmtEcmAxioms : Stmt → List (String × String)
    | .ecm mod args =>
        let fromArgs := args.flatMap collectExprEcmAxioms
        mod.axioms.map (fun a => (mod.name, a)) ++ fromArgs
    | .ite _ thenBr elseBr =>
        thenBr.flatMap collectStmtEcmAxioms ++ elseBr.flatMap collectStmtEcmAxioms
    | .forEach _ _ body => body.flatMap collectStmtEcmAxioms
    | _ => []
  collectExprEcmAxioms : Expr → List (String × String)
    | .ite cond a b => collectExprEcmAxioms cond ++ collectExprEcmAxioms a ++ collectExprEcmAxioms b
    | _ => []

end Compiler.CompilationModel
