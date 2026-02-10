import Compiler.Yul.Ast

namespace Compiler

inductive IRType
  | uint256
  | address
  | unit
  deriving Repr

structure IRParam where
  name : String
  ty : IRType
  deriving Repr

abbrev IRExpr := Yul.YulExpr
abbrev IRStmt := Yul.YulStmt

structure IRFunction where
  name : String
  selector : Nat
  params : List IRParam
  ret : IRType
  body : List IRStmt
  deriving Repr

structure IRContract where
  name : String
  deploy : List IRStmt
  functions : List IRFunction
  usesMapping : Bool
  deriving Repr

end Compiler
