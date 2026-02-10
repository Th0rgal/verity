import DumbContracts.Lang

namespace DumbContracts.Std

open DumbContracts.Lang

/--
Small convenience helpers for writing contracts as Lean data.
These are definitional wrappers so they should reduce syntax noise
without changing semantics.
-/

def require (cond : Expr) (body : Stmt) : Stmt :=
  Stmt.if_ cond body Stmt.revert

def unless (cond : Expr) (body : Stmt) : Stmt :=
  Stmt.if_ cond Stmt.revert body

def requireAnd (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (Expr.and lhs rhs) body

def revertIf (cond : Expr) : Stmt :=
  Stmt.if_ cond Stmt.revert Stmt.skip

def assert (cond : Expr) : Stmt :=
  Stmt.if_ cond Stmt.skip Stmt.revert

def eq (lhs rhs : Expr) : Expr :=
  Expr.eq lhs rhs

def neq (lhs rhs : Expr) : Expr :=
  Expr.not (Expr.eq lhs rhs)

def requireEq (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (eq lhs rhs) body

def requireNeq (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (neq lhs rhs) body

def requireGt (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (Expr.gt lhs rhs) body

def requireLt (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (Expr.lt lhs rhs) body

def requireGte (lhs rhs : Expr) (body : Stmt) : Stmt :=
  require (Expr.not (Expr.lt lhs rhs)) body

def requireBetween (value lo hi : Expr) (body : Stmt) : Stmt :=
  requireAnd (Expr.gt value lo) (Expr.lt value hi) body

def requireNonZero (value : Expr) (body : Stmt) : Stmt :=
  requireNeq value (Expr.lit 0) body

def requireZero (value : Expr) (body : Stmt) : Stmt :=
  requireEq value (Expr.lit 0) body

/-- Shorthand for loading/storing fixed slots. -/

def letSload (name : String) (slot : Expr) (body : Stmt) : Stmt :=
  Stmt.let_ name (Expr.sload slot) body

def sstoreAdd (slot delta : Expr) : Stmt :=
  Stmt.sstore slot (Expr.add (Expr.sload slot) delta)

def sstoreSub (slot delta : Expr) : Stmt :=
  Stmt.sstore slot (Expr.sub (Expr.sload slot) delta)

def sstoreInc (slot : Expr) : Stmt :=
  sstoreAdd slot (Expr.lit 1)

def sstoreMax (slot a b : Expr) : Stmt :=
  Stmt.if_ (Expr.gt a b) (Stmt.sstore slot a) (Stmt.sstore slot b)

def sstoreMin (slot a b : Expr) : Stmt :=
  Stmt.if_ (Expr.lt a b) (Stmt.sstore slot a) (Stmt.sstore slot b)

def sloadSlot (slot : Nat) : Expr :=
  Expr.sload (Expr.lit slot)

def sstoreSlot (slot : Nat) (value : Expr) : Stmt :=
  Stmt.sstore (Expr.lit slot) value

def sloadVar (name : String) : Expr :=
  Expr.sload (Expr.var name)

def sstoreVar (name : String) (value : Expr) : Stmt :=
  Stmt.sstore (Expr.var name) value

/-- Shorthand for variables and literals. -/

def v (name : String) : Expr :=
  Expr.var name

def n (value : Nat) : Expr :=
  Expr.lit value

end DumbContracts.Std
