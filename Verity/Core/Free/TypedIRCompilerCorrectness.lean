import Verity.Core.Free.TypedIRCompiler

namespace Verity.Core.Free
open Compiler.CompilationModel

/-- Generic structural-induction theorem: compiling concatenated statement lists
is equivalent to compiling the prefix then the suffix. -/
theorem compileStmts_append (fields : List Field) (pre post : List Stmt) :
    compileStmts fields (pre ++ post) = (do
      compileStmts fields pre
      compileStmts fields post) := by
  induction pre with
  | nil =>
      simp [compileStmts]
  | cons stmt rest ih =>
      simp [compileStmts, ih]

/-- `compileStmts_append` specialized to any initial compiler state. -/
theorem compileStmts_append_from (fields : List Field) (pre post : List Stmt)
    (st : CompileState) :
    (compileStmts fields (pre ++ post)).run st =
      ((do
          compileStmts fields pre
          compileStmts fields post).run st) := by
  simpa using congrArg (fun m => m.run st) (compileStmts_append fields pre post)

/-- Source semantics for the supported 2.2 subset:
`setStorage fieldName (literal n)` updates the resolved storage slot. -/
def execSourceSetStorageLiteral (world : Verity.ContractState) (slot : Nat) (n : Verity.Core.Uint256) :
    Verity.ContractState :=
  { world with storage := fun i => if i == slot then n else world.storage i }

/-- Compile + execute the same supported subset statement through typed IR. -/
def execCompiledSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState) (n : Nat) :
    TExecResult :=
  match (compileStmts fields [Stmt.setStorage fieldName (Expr.literal n)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute a broader supported subset statement sequence:
`letVar tmp (literal n); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n : Nat) :
    TExecResult :=
  match (compileStmts fields
      [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute a broader supported subset statement sequence:
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetAssignSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n m : Nat) :
    TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.literal m)
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute an arithmetic supported subset sequence:
`letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetAssignAddSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n m : Nat) :
    TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute an arithmetic supported subset sequence:
`letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetAssignSubSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n m : Nat) :
    TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Compile + execute an arithmetic supported subset sequence:
`letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`. -/
def execCompiledLetAssignMulSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState) (n m : Nat) :
    TExecResult :=
  match (compileStmts fields
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for the supported return subset:
`return (literal n)` halts without mutating state. -/
def execSourceReturnLiteral (init : TExecState) (_n : Nat) : TExecResult :=
  .ok init

/-- Compile + execute the supported return subset statement through typed IR. -/
def execCompiledReturnLiteral
    (fields : List Field) (init : TExecState) (n : Nat) : TExecResult :=
  match (compileStmts fields [Stmt.return (Expr.literal n)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported subset:
`letVar tmp (literal n); return (localVar tmp)` binds `tmp` then halts. -/
def execSourceLetReturnLocalLiteral (init : TExecState) (n : Nat) : TExecResult :=
  .ok ({ init with vars := init.vars.set { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256) })

/-- Compile + execute a broader supported subset statement sequence:
`letVar tmp (literal n); return (localVar tmp)`. -/
def execCompiledLetReturnLocalLiteral
    (fields : List Field) (tmp : String) (init : TExecState) (n : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.letVar tmp (Expr.literal n), Stmt.return (Expr.localVar tmp)]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
updates the resolved storage slot based on the equality guard. -/
def execSourceIteEqSetStorageLiterals
    (world : Verity.ContractState) (slot : Nat)
    (n m thenVal elseVal : Nat) : Verity.ContractState :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceSetStorageLiteral world slot thenVal
  else
    execSourceSetStorageLiteral world slot elseVal

/-- Compile + execute a broader supported branch subset statement through typed IR. -/
def execCompiledIteEqSetStorageLiterals
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.setStorage fieldName (Expr.literal thenVal)]
        [Stmt.setStorage fieldName (Expr.literal elseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (eq (literal n) (literal m)) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireEqLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireEqLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.eq (Expr.literal n) (Expr.literal m)) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (logicalNot (eq (literal n) (literal m))) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireNotEqLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if ¬ ((n : Verity.Core.Uint256) == (m : Verity.Core.Uint256)) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireNotEqLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.logicalNot (Expr.eq (Expr.literal n) (Expr.literal m))) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (lt (literal n) (literal m)) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireLtLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if (n : Verity.Core.Uint256) < (m : Verity.Core.Uint256) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireLtLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.lt (Expr.literal n) (Expr.literal m)) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (gt (literal n) (literal m)) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireGtLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if (m : Verity.Core.Uint256) < (n : Verity.Core.Uint256) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireGtLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.gt (Expr.literal n) (Expr.literal m)) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (ge (literal n) (literal m)) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireGeLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if ¬ ((n : Verity.Core.Uint256) < (m : Verity.Core.Uint256)) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireGeLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.ge (Expr.literal n) (Expr.literal m)) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (le (literal n) (literal m)) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireLeLiterals (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  if ¬ ((m : Verity.Core.Uint256) < (n : Verity.Core.Uint256)) then .ok init else .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireLeLiterals
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require (Expr.le (Expr.literal n) (Expr.literal m)) message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (logicalAnd (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireAndEqLtLiterals
    (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    if (p : Verity.Core.Uint256) < (q : Verity.Core.Uint256) then .ok init else .revert message
  else
    .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireAndEqLtLiterals
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require
        (Expr.logicalAnd
          (Expr.eq (Expr.literal n) (Expr.literal m))
          (Expr.lt (Expr.literal p) (Expr.literal q)))
        message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported require subset:
`require (logicalOr (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
halts with revert on guard failure and leaves state unchanged otherwise. -/
def execSourceRequireOrEqLtLiterals
    (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    .ok init
  else if (p : Verity.Core.Uint256) < (q : Verity.Core.Uint256) then
    .ok init
  else
    .revert message

/-- Compile + execute a broader supported require subset statement through typed IR. -/
def execCompiledRequireOrEqLtLiterals
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  match (compileStmts fields
      [Stmt.require
        (Expr.logicalOr
          (Expr.eq (Expr.literal n) (Expr.literal m))
          (Expr.lt (Expr.literal p) (Expr.literal q)))
        message]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Guard family for generalized single-guard `require` literal semantic preservation. -/
inductive RequireBinaryLiteralGuard where
  | eq
  | notEq
  | lt
  | gt
  | ge
  | le
deriving DecidableEq, Repr

/-- Source semantics dispatcher for generalized single-guard `require` literals. -/
def execSourceRequireBinaryLiteralGuard
    (guard : RequireBinaryLiteralGuard)
    (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match guard with
  | .eq => execSourceRequireEqLiterals init n m message
  | .notEq => execSourceRequireNotEqLiterals init n m message
  | .lt => execSourceRequireLtLiterals init n m message
  | .gt => execSourceRequireGtLiterals init n m message
  | .ge => execSourceRequireGeLiterals init n m message
  | .le => execSourceRequireLeLiterals init n m message

/-- Compiled semantics dispatcher for generalized single-guard `require` literals. -/
def execCompiledRequireBinaryLiteralGuard
    (guard : RequireBinaryLiteralGuard)
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) : TExecResult :=
  match guard with
  | .eq => execCompiledRequireEqLiterals fields init n m message
  | .notEq => execCompiledRequireNotEqLiterals fields init n m message
  | .lt => execCompiledRequireLtLiterals fields init n m message
  | .gt => execCompiledRequireGtLiterals fields init n m message
  | .ge => execCompiledRequireGeLiterals fields init n m message
  | .le => execCompiledRequireLeLiterals fields init n m message

/-- Clause payload for list-level semantic preservation over supported
single-guard `require` literals. -/
structure RequireBinaryLiteralClause where
  guard : RequireBinaryLiteralGuard
  lhs : Nat
  rhs : Nat
  message : String
deriving DecidableEq, Repr

/-- Source semantics dispatcher for a list of supported single-guard
`require` literal clauses. Evaluation short-circuits on revert. -/
def execSourceRequireBinaryLiteralClauses
    (init : TExecState) (clauses : List RequireBinaryLiteralClause) : TExecResult :=
  match clauses with
  | [] => .ok init
  | clause :: rest =>
      match execSourceRequireBinaryLiteralGuard clause.guard init clause.lhs clause.rhs clause.message with
      | .ok st => execSourceRequireBinaryLiteralClauses st rest
      | .revert reason => .revert reason

/-- Compiled semantics dispatcher for a list of supported single-guard
`require` literal clauses. Evaluation short-circuits on revert. -/
def execCompiledRequireBinaryLiteralClauses
    (fields : List Field) (init : TExecState) (clauses : List RequireBinaryLiteralClause) : TExecResult :=
  match clauses with
  | [] => .ok init
  | clause :: rest =>
      match execCompiledRequireBinaryLiteralGuard
          clause.guard fields init clause.lhs clause.rhs clause.message with
      | .ok st => execCompiledRequireBinaryLiteralClauses fields st rest
      | .revert reason => .revert reason

/-- Semantic-preservation theorem for the supported 2.2 subset:
compiling and running `setStorage fieldName (literal n)` matches direct source execution,
under explicit field-resolution assumptions. -/
theorem compile_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledSetStorageLiteral fields fieldName init n =
      .ok { init with world := execSourceSetStorageLiteral init.world slot n } := by
  simp [execCompiledSetStorageLiteral, execSourceSetStorageLiteral,
    compileStmts_single_setStorage_literal_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for the supported two-statement subset:
compiling and running `letVar tmp (literal n); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetSetStorageLocalLiteral fields fieldName tmp init n =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot n
            vars := init.vars.set { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256) }) := by
  simp [execCompiledLetSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for a broader supported three-statement subset:
compiling and running
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_assign_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetAssignSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot m
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 } (m : Verity.Core.Uint256) }) := by
  simp [execCompiledLetAssignSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_assign_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for an arithmetic supported three-statement subset:
compiling and running
`letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_assign_add_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetAssignAddSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot
              ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256)) }) := by
  simp [execCompiledLetAssignAddSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_assign_add_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for an arithmetic supported three-statement subset:
compiling and running
`letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_assign_sub_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetAssignSubSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot
              ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256)) }) := by
  simp [execCompiledLetAssignSubSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_assign_sub_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr]

/-- Semantic-preservation theorem for an arithmetic supported three-statement subset:
compiling and running
`letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m)); setStorage fieldName (localVar tmp)`
matches direct source storage update semantics under explicit field-resolution assumptions. -/
theorem compile_let_assign_mul_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledLetAssignMulSetStorageLocalLiteral fields fieldName tmp init n m =
      .ok
        ({ init with
            world := execSourceSetStorageLiteral init.world slot
              ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set init.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256)) }) := by
  simp [execCompiledLetAssignMulSetStorageLocalLiteral, execSourceSetStorageLiteral,
    compileStmts_let_assign_mul_literal_setStorage_local_run, hfind, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr]

/-- Semantic-preservation theorem for a broader supported subset:
compiling and running `return (literal n)` matches direct source return semantics. -/
theorem compile_return_literal_semantics
    (fields : List Field) (init : TExecState) (n : Nat) :
    execCompiledReturnLiteral fields init n = execSourceReturnLiteral init n := by
  simp [execCompiledReturnLiteral, execSourceReturnLiteral,
    compileStmts_single_return_literal_run, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for a broader supported subset:
compiling and running `letVar tmp (literal n); return (localVar tmp)`
matches direct source let-then-return semantics. -/
theorem compile_let_return_local_literal_semantics
    (fields : List Field) (tmp : String) (init : TExecState) (n : Nat) :
    execCompiledLetReturnLocalLiteral fields tmp init n =
      execSourceLetReturnLocalLiteral init n := by
  simp [execCompiledLetReturnLocalLiteral, execSourceLetReturnLocalLiteral,
    compileStmts_let_return_local_literal_run, evalTStmts, defaultEvalFuel]
  simp [evalTStmtsFuel, evalTStmtFuel]

/-- Semantic-preservation theorem for a broader supported branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
matches direct source branch semantics under explicit field-resolution assumptions. -/
theorem compile_ite_eq_setStorage_literals_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqSetStorageLiterals fields fieldName init n m thenVal elseVal =
      .ok { init with world := execSourceIteEqSetStorageLiterals init.world slot n m thenVal elseVal } := by
  simp [execCompiledIteEqSetStorageLiterals, execSourceIteEqSetStorageLiterals,
    execSourceSetStorageLiteral, compileStmts_single_ite_eq_setStorage_literals_run,
    hfind, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (eq (literal n) (literal m)) message`
matches direct source require semantics. -/
theorem compile_require_eq_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireEqLiterals fields init n m message =
      execSourceRequireEqLiterals init n m message := by
  simp [execCompiledRequireEqLiterals, execSourceRequireEqLiterals,
    compileStmts_single_require_eq_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (logicalNot (eq (literal n) (literal m))) message`
matches direct source require semantics. -/
theorem compile_require_not_eq_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireNotEqLiterals fields init n m message =
      execSourceRequireNotEqLiterals init n m message := by
  simp [execCompiledRequireNotEqLiterals, execSourceRequireNotEqLiterals,
    compileStmts_single_require_not_eq_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (lt (literal n) (literal m)) message`
matches direct source require semantics. -/
theorem compile_require_lt_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireLtLiterals fields init n m message =
      execSourceRequireLtLiterals init n m message := by
  simp [execCompiledRequireLtLiterals, execSourceRequireLtLiterals,
    compileStmts_single_require_lt_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hLt : (n : Verity.Core.Uint256) < (m : Verity.Core.Uint256)
  · have hNat : n % Verity.Core.Uint256.modulus < m % Verity.Core.Uint256.modulus := by
      simpa [Verity.Core.Uint256.lt_def] using hLt
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hLt, hNat]
  · have hNat : m % Verity.Core.Uint256.modulus ≤ n % Verity.Core.Uint256.modulus := by
      exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hLt)
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hLt, hNat]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (gt (literal n) (literal m)) message`
matches direct source require semantics. -/
theorem compile_require_gt_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireGtLiterals fields init n m message =
      execSourceRequireGtLiterals init n m message := by
  simp [execCompiledRequireGtLiterals, execSourceRequireGtLiterals,
    compileStmts_single_require_gt_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hGt : (m : Verity.Core.Uint256) < (n : Verity.Core.Uint256)
  · have hNat : m % Verity.Core.Uint256.modulus < n % Verity.Core.Uint256.modulus := by
      simpa [Verity.Core.Uint256.lt_def] using hGt
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hGt, hNat]
  · have hNat : n % Verity.Core.Uint256.modulus ≤ m % Verity.Core.Uint256.modulus := by
      exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hGt)
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hGt, hNat]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (ge (literal n) (literal m)) message`
matches direct source require semantics. -/
theorem compile_require_ge_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireGeLiterals fields init n m message =
      execSourceRequireGeLiterals init n m message := by
  simp [execCompiledRequireGeLiterals, execSourceRequireGeLiterals,
    compileStmts_single_require_ge_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hLt : (n : Verity.Core.Uint256) < (m : Verity.Core.Uint256)
  · have hNat : n % Verity.Core.Uint256.modulus < m % Verity.Core.Uint256.modulus := by
      simpa [Verity.Core.Uint256.lt_def] using hLt
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hLt, hNat]
  · have hNat : m % Verity.Core.Uint256.modulus ≤ n % Verity.Core.Uint256.modulus := by
      exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hLt)
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hLt, hNat]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running `require (le (literal n) (literal m)) message`
matches direct source require semantics. -/
theorem compile_require_le_literals_semantics
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireLeLiterals fields init n m message =
      execSourceRequireLeLiterals init n m message := by
  simp [execCompiledRequireLeLiterals, execSourceRequireLeLiterals,
    compileStmts_single_require_le_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hGt : (m : Verity.Core.Uint256) < (n : Verity.Core.Uint256)
  · have hNat : m % Verity.Core.Uint256.modulus < n % Verity.Core.Uint256.modulus := by
      simpa [Verity.Core.Uint256.lt_def] using hGt
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hGt, hNat]
  · have hNat : n % Verity.Core.Uint256.modulus ≤ m % Verity.Core.Uint256.modulus := by
      exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hGt)
    simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hGt, hNat]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running
`require (logicalAnd (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
matches direct source require semantics. -/
theorem compile_require_and_eq_lt_literals_semantics
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireAndEqLtLiterals fields init n m p q message =
      execSourceRequireAndEqLtLiterals init n m p q message := by
  simp [execCompiledRequireAndEqLtLiterals, execSourceRequireAndEqLtLiterals,
    compileStmts_single_require_and_eq_lt_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hLt : (p : Verity.Core.Uint256) < (q : Verity.Core.Uint256)
    · have hLtNat : p % Verity.Core.Uint256.modulus < q % Verity.Core.Uint256.modulus := by
        simpa [Verity.Core.Uint256.lt_def] using hLt
      simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq, hLt, hLtNat]
    · have hLtNat : q % Verity.Core.Uint256.modulus ≤ p % Verity.Core.Uint256.modulus := by
        exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hLt)
      simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq, hLt, hLtNat]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported require subset:
compiling and running
`require (logicalOr (eq (literal n) (literal m)) (lt (literal p) (literal q))) message`
matches direct source require semantics. -/
theorem compile_require_or_eq_lt_literals_semantics
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireOrEqLtLiterals fields init n m p q message =
      execSourceRequireOrEqLtLiterals init n m p q message := by
  simp [execCompiledRequireOrEqLtLiterals, execSourceRequireOrEqLtLiterals,
    compileStmts_single_require_or_eq_lt_literals_run, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · by_cases hLt : (p : Verity.Core.Uint256) < (q : Verity.Core.Uint256)
    · have hLtNat : p % Verity.Core.Uint256.modulus < q % Verity.Core.Uint256.modulus := by
        simpa [Verity.Core.Uint256.lt_def] using hLt
      simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq, hLt, hLtNat]
    · have hLtNat : q % Verity.Core.Uint256.modulus ≤ p % Verity.Core.Uint256.modulus := by
        exact Nat.not_lt.mp (by simpa [Verity.Core.Uint256.lt_def] using hLt)
      simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq, hLt, hLtNat]

/-- Generalized semantic-preservation theorem for single-guard `require` over
supported binary literal guards (`eq`, `notEq`, `lt`, `gt`, `ge`, `le`). -/
theorem compile_require_binary_literal_guard_semantics
    (guard : RequireBinaryLiteralGuard)
    (fields : List Field) (init : TExecState) (n m : Nat) (message : String) :
    execCompiledRequireBinaryLiteralGuard guard fields init n m message =
      execSourceRequireBinaryLiteralGuard guard init n m message := by
  cases guard <;>
    simp [execCompiledRequireBinaryLiteralGuard, execSourceRequireBinaryLiteralGuard,
      compile_require_eq_literals_semantics,
      compile_require_not_eq_literals_semantics,
      compile_require_lt_literals_semantics,
      compile_require_gt_literals_semantics,
      compile_require_ge_literals_semantics,
      compile_require_le_literals_semantics]

/-- Structural-induction semantic-preservation theorem for sequences of
supported single-guard `require` literal clauses. -/
theorem compile_require_binary_literal_clauses_semantics
    (fields : List Field) (init : TExecState) (clauses : List RequireBinaryLiteralClause) :
    execCompiledRequireBinaryLiteralClauses fields init clauses =
      execSourceRequireBinaryLiteralClauses init clauses := by
  induction clauses generalizing init with
  | nil =>
      simp [execCompiledRequireBinaryLiteralClauses, execSourceRequireBinaryLiteralClauses]
  | cons clause rest ih =>
      simp [execCompiledRequireBinaryLiteralClauses, execSourceRequireBinaryLiteralClauses,
        compile_require_binary_literal_guard_semantics, ih]
      rfl

/-- Unified guard family for semantic-preservation coverage across supported
single-guard and composite-guard `require` literal subsets. -/
inductive RequireLiteralGuardFamily where
  | binary (guard : RequireBinaryLiteralGuard)
  | andEqLt
  | orEqLt
deriving DecidableEq, Repr

/-- Source semantics dispatcher for the unified `require` guard family. -/
def execSourceRequireLiteralGuardFamily
    (family : RequireLiteralGuardFamily)
    (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  match family with
  | .binary guard => execSourceRequireBinaryLiteralGuard guard init n m message
  | .andEqLt => execSourceRequireAndEqLtLiterals init n m p q message
  | .orEqLt => execSourceRequireOrEqLtLiterals init n m p q message

/-- Compiled semantics dispatcher for the unified `require` guard family. -/
def execCompiledRequireLiteralGuardFamily
    (family : RequireLiteralGuardFamily)
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) : TExecResult :=
  match family with
  | .binary guard => execCompiledRequireBinaryLiteralGuard guard fields init n m message
  | .andEqLt => execCompiledRequireAndEqLtLiterals fields init n m p q message
  | .orEqLt => execCompiledRequireOrEqLtLiterals fields init n m p q message

/-- Generalized semantic-preservation theorem over the supported unified
`require` guard family (`eq/notEq/lt/gt/ge/le`, `and(eq,lt)`, `or(eq,lt)`). -/
theorem compile_require_literal_guard_family_semantics
    (family : RequireLiteralGuardFamily)
    (fields : List Field) (init : TExecState) (n m p q : Nat) (message : String) :
    execCompiledRequireLiteralGuardFamily family fields init n m p q message =
      execSourceRequireLiteralGuardFamily family init n m p q message := by
  cases family with
  | binary guard =>
      simpa [execCompiledRequireLiteralGuardFamily, execSourceRequireLiteralGuardFamily]
        using compile_require_binary_literal_guard_semantics guard fields init n m message
  | andEqLt =>
      simpa [execCompiledRequireLiteralGuardFamily, execSourceRequireLiteralGuardFamily]
        using compile_require_and_eq_lt_literals_semantics fields init n m p q message
  | orEqLt =>
      simpa [execCompiledRequireLiteralGuardFamily, execSourceRequireLiteralGuardFamily]
        using compile_require_or_eq_lt_literals_semantics fields init n m p q message

end Verity.Core.Free
