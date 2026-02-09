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

def assert (cond : Expr) : Stmt :=
  Stmt.if_ cond Stmt.skip Stmt.revert

/-- Shorthand for loading/storing fixed slots. -/

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
