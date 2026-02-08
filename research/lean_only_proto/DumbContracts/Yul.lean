import DumbContracts.Core
import DumbContracts.Lang

namespace DumbContracts.Yul

inductive Expr where
  | lit : Nat -> Expr
  | var : String -> Expr
  | call : String -> List Expr -> Expr
  deriving Repr

inductive Stmt where
  | block : List Stmt -> Stmt
  | let_ : String -> Expr -> Stmt
  | assign : String -> Expr -> Stmt
  | if_ : Expr -> Stmt -> Stmt
  | switch : Expr -> List (Nat × Stmt) -> Stmt -> Stmt
  | expr : Expr -> Stmt
  | func : String -> List String -> List String -> Stmt -> Stmt
  | leave : Stmt
  deriving Repr

structure Object where
  name : String
  code : Stmt
  deriving Repr

structure Program where
  obj : Object
  deriving Repr

namespace Pretty

partial def indent (s : String) : String :=
  let lines := s.splitOn "\n"
  String.intercalate "\n" (lines.map (fun l => if l = "" then "" else "  " ++ l))

partial def expr : Expr -> String
  | Expr.lit n => toString n
  | Expr.var v => v
  | Expr.call f args =>
      let argsStr := String.intercalate ", " (args.map expr)
      s!"{f}({argsStr})"

partial def stmt : Stmt -> String
  | Stmt.block ss =>
      let body := String.intercalate "\n" (ss.map stmt)
      "{" ++ "\n" ++ indent body ++ "\n" ++ "}"
  | Stmt.let_ v e => s!"let {v} := {expr e}"
  | Stmt.assign v e => s!"{v} := {expr e}"
  | Stmt.if_ c t => s!"if {expr c} {stmt t}"
  | Stmt.switch e cases dflt =>
      let cs := cases.map (fun (n, s) => s!"case {n} {stmt s}")
      let d := s!"default {stmt dflt}"
      let body := String.intercalate "\n" (cs ++ [d])
      s!"switch {expr e}\n{indent body}"
  | Stmt.expr e => expr e
  | Stmt.func name args rets body =>
      let argsStr := String.intercalate ", " args
      let retStr := match rets with
        | [] => ""
        | _ => " -> " ++ String.intercalate ", " rets
      "function " ++ name ++ "(" ++ argsStr ++ ")" ++ retStr ++ " " ++ stmt body
  | Stmt.leave => "leave"

partial def object (o : Object) : String :=
  let codeStr := "code " ++ stmt o.code
  "object \"" ++ o.name ++ "\" {\n" ++ indent codeStr ++ "\n}"

partial def program (p : Program) : String :=
  object p.obj

end Pretty

end DumbContracts.Yul
