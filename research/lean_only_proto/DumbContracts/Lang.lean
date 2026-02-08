import DumbContracts.Core

namespace DumbContracts.Lang

inductive Expr where
  | lit : Nat -> Expr
  | var : String -> Expr
  | add : Expr -> Expr -> Expr
  | sub : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr
  | div : Expr -> Expr -> Expr
  | eq : Expr -> Expr -> Expr
  | lt : Expr -> Expr -> Expr
  | gt : Expr -> Expr -> Expr
  | and : Expr -> Expr -> Expr
  | or : Expr -> Expr -> Expr
  | not : Expr -> Expr
  | sload : Expr -> Expr
  deriving Repr

inductive Stmt where
  | skip : Stmt
  | seq : Stmt -> Stmt -> Stmt
  | let_ : String -> Expr -> Stmt -> Stmt
  | assign : String -> Expr -> Stmt
  | if_ : Expr -> Stmt -> Stmt -> Stmt
  | sstore : Expr -> Expr -> Stmt
  | revert : Stmt
  | return_ : Expr -> Stmt
  deriving Repr

structure Fun where
  name : String
  args : List String
  body : Stmt
  ret : Option String
  deriving Repr

structure Program where
  funs : List Fun
  entry : Stmt
  deriving Repr

notation:50 a " ;; " b => Stmt.seq a b

end DumbContracts.Lang
