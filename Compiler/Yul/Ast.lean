namespace Compiler.Yul

inductive YulExpr
  | lit (n : Nat)
  | hex (n : Nat)
  | str (s : String)
  | ident (name : String)
  | call (func : String) (args : List YulExpr)
  deriving Repr

inductive YulStmt
  | comment (text : String)
  | let_ (name : String) (value : YulExpr)
  | assign (name : String) (value : YulExpr)
  | expr (e : YulExpr)
  | if_ (cond : YulExpr) (body : List YulStmt)
  | switch (expr : YulExpr) (cases : List (Nat × List YulStmt)) (default : Option (List YulStmt))
  | block (stmts : List YulStmt)
  | funcDef (name : String) (params : List String) (rets : List String) (body : List YulStmt)
  deriving Repr

structure YulObject where
  name : String
  deployCode : List YulStmt
  runtimeCode : List YulStmt
  deriving Repr

end Compiler.Yul
