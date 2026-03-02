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

/-- Direct source semantics for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [return (literal elseVal)]`
updates storage on the true branch and halts via return on the false branch. -/
def execSourceIteEqSetStorageThenReturnLiteral
    (init : TExecState) (slot : Nat)
    (n m thenVal elseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    .ok { init with world := execSourceSetStorageLiteral init.world slot thenVal }
  else
    execSourceReturnLiteral init elseVal

/-- Compile + execute a broader supported heterogeneous branch subset through
typed IR. -/
def execCompiledIteEqSetStorageThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.setStorage fieldName (Expr.literal thenVal)]
        [Stmt.return (Expr.literal elseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported heterogeneous branch subset:
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
halts via return on the true branch and updates storage on the false branch. -/
def execSourceIteEqReturnThenSetStorageLiteral
    (init : TExecState) (slot : Nat)
    (n m thenVal elseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceReturnLiteral init thenVal
  else
    .ok { init with world := execSourceSetStorageLiteral init.world slot elseVal }

/-- Compile + execute a broader supported heterogeneous branch subset through
typed IR. -/
def execCompiledIteEqReturnThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.return (Expr.literal thenVal)]
        [Stmt.setStorage fieldName (Expr.literal elseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported branch subset:
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [return (literal elseVal)]`
halts via return on both branches. -/
def execSourceIteEqReturnLiterals
    (init : TExecState)
    (n m thenVal elseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceReturnLiteral init thenVal
  else
    execSourceReturnLiteral init elseVal

/-- Compile + execute a broader supported branch subset through typed IR. -/
def execCompiledIteEqReturnLiterals
    (fields : List Field) (init : TExecState)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.return (Expr.literal thenVal)]
        [Stmt.return (Expr.literal elseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested-branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
halts via nested return-driven control flow. -/
def execSourceIteEqThenIteEqReturnLiterals
    (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqReturnLiterals init p q thenVal elseVal
  else
    execSourceReturnLiteral init outerElseVal

/-- Compile + execute a broader supported nested-branch subset through typed IR. -/
def execCompiledIteEqThenIteEqReturnLiterals
    (fields : List Field) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested-branch subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
updates storage through the inner branch on outer-guard success and halts via
return on the outer false branch. -/
def execSourceIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    .ok { init with world := execSourceIteEqSetStorageLiterals init.world slot p q thenVal elseVal }
  else
    execSourceReturnLiteral init outerElseVal

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.return (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested heterogeneous branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
halts via nested returns on outer-guard success and writes storage on the outer
false branch. -/
def execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    execSourceIteEqReturnLiterals init p q thenVal elseVal
  else
    .ok { init with world := execSourceSetStorageLiteral init.world slot outerElseVal }

/-- Compile + execute a broader supported nested heterogeneous branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} with
  | .error err => .revert err
  | .ok (_, st) => evalTStmts init st.body.toList

/-- Direct source semantics for a broader supported nested storage branch
subset:
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
updates storage through the inner branch on outer-guard success and writes
storage on the outer false branch. -/
def execSourceIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
    (init : TExecState) (slot : Nat)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  if (n : Verity.Core.Uint256) == (m : Verity.Core.Uint256) then
    .ok { init with world := execSourceIteEqSetStorageLiterals init.world slot p q thenVal elseVal }
  else
    .ok { init with world := execSourceSetStorageLiteral init.world slot outerElseVal }

/-- Compile + execute a broader supported nested storage branch subset
through typed IR. -/
def execCompiledIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match (compileStmts fields
      [Stmt.ite
        (Expr.eq (Expr.literal n) (Expr.literal m))
        [Stmt.ite
          (Expr.eq (Expr.literal p) (Expr.literal q))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
        [Stmt.setStorage fieldName (Expr.literal outerElseVal)] ]).run {} with
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

/-- Semantic-preservation theorem for a broader supported heterogeneous branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [return (literal elseVal)]`
matches direct source branch semantics under explicit field-resolution assumptions. -/
theorem compile_ite_eq_setStorage_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqSetStorageThenReturnLiteral fields fieldName init n m thenVal elseVal =
      execSourceIteEqSetStorageThenReturnLiteral init slot n m thenVal elseVal := by
  simp [execCompiledIteEqSetStorageThenReturnLiteral,
    execSourceIteEqSetStorageThenReturnLiteral,
    compileStmts_single_ite_eq_setStorage_then_return_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported heterogeneous branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [setStorage fieldName (literal elseVal)]`
matches direct source branch semantics under explicit field-resolution assumptions. -/
theorem compile_ite_eq_return_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqReturnThenSetStorageLiteral fields fieldName init n m thenVal elseVal =
      execSourceIteEqReturnThenSetStorageLiteral init slot n m thenVal elseVal := by
  simp [execCompiledIteEqReturnThenSetStorageLiteral,
    execSourceIteEqReturnThenSetStorageLiteral,
    compileStmts_single_ite_eq_return_then_setStorage_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [return (literal elseVal)]`
matches direct source branch semantics. -/
theorem compile_ite_eq_return_literals_semantics
    (fields : List Field)
    (init : TExecState) (n m thenVal elseVal : Nat) :
    execCompiledIteEqReturnLiterals fields init n m thenVal elseVal =
      execSourceIteEqReturnLiterals init n m thenVal elseVal := by
  simp [execCompiledIteEqReturnLiterals, execSourceIteEqReturnLiterals,
    compileStmts_single_ite_eq_return_literals_run,
    execSourceReturnLiteral, evalTStmts, defaultEvalFuel]
  by_cases hEq : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEq]

/-- Semantic-preservation theorem for a broader supported nested-branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]`
matches direct source nested-branch semantics. -/
theorem compile_ite_eq_then_ite_eq_return_literals_semantics
    (fields : List Field)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat) :
    execCompiledIteEqThenIteEqReturnLiterals
        fields init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqReturnLiterals
        init n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqReturnLiterals,
    execSourceIteEqThenIteEqReturnLiterals,
    execSourceIteEqReturnLiterals, compileStmts_single_ite_eq_then_ite_eq_return_literals_run,
    execSourceReturnLiteral, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqSetStorageLiteralsThenReturnLiteral,
    execSourceIteEqThenIteEqSetStorageLiteralsThenReturnLiteral,
    execSourceIteEqSetStorageLiterals, compileStmts_single_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested heterogeneous
branch subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteral,
    execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteral,
    execSourceIteEqReturnLiterals,
    compileStmts_single_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_run,
    execSourceSetStorageLiteral, execSourceReturnLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter]

/-- Semantic-preservation theorem for a broader supported nested storage branch
subset:
compiling and running
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]`
matches direct source nested-branch semantics under explicit field-resolution
assumptions. -/
theorem compile_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState) (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName init n m p q thenVal elseVal outerElseVal =
      execSourceIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        init slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral,
    execSourceIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral,
    execSourceIteEqSetStorageLiterals,
    compileStmts_single_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_run,
    execSourceSetStorageLiteral, hfind, evalTStmts, defaultEvalFuel]
  by_cases hEqOuter : (n : Verity.Core.Uint256) = (m : Verity.Core.Uint256)
  · by_cases hEqInner : (p : Verity.Core.Uint256) = (q : Verity.Core.Uint256)
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
    · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter, hEqInner]
  · simp [evalTStmtsFuel, evalTStmtFuel, evalTExpr, hEqOuter]

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

/-- Source semantics for a broader supported sequencing subset:
run one supported `require` guard-family clause, then perform
`setStorage fieldName (literal writeVal)` only on success. -/
def execSourceRequireFamilyThenSetStorageLiteral
    (family : RequireLiteralGuardFamily)
    (init : TExecState) (slot : Nat)
    (n m p q : Nat) (message : String) (writeVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamily family init n m p q message with
  | .ok st => .ok { st with world := execSourceSetStorageLiteral st.world slot writeVal }
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled one-clause `require` guard-family semantics, then run
compiled `setStorage fieldName (literal writeVal)` on success. -/
def execCompiledRequireFamilyThenSetStorageLiteral
    (family : RequireLiteralGuardFamily)
    (fields : List Field) (fieldName : String) (init : TExecState)
    (n m p q : Nat) (message : String) (writeVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamily family fields init n m p q message with
  | .ok st => execCompiledSetStorageLiteral fields fieldName st writeVal
  | .revert reason => .revert reason

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard families followed by `setStorage literal`,
compiled execution matches direct source sequencing semantics under
explicit field-resolution assumptions. -/
theorem compile_require_family_then_setStorage_literal_semantics
    (family : RequireLiteralGuardFamily)
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (n m p q : Nat) (message : String) (writeVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyThenSetStorageLiteral
        family fields fieldName init n m p q message writeVal =
      execSourceRequireFamilyThenSetStorageLiteral
        family init slot n m p q message writeVal := by
  simp [execCompiledRequireFamilyThenSetStorageLiteral,
    execSourceRequireFamilyThenSetStorageLiteral,
    compile_require_literal_guard_family_semantics, compile_setStorage_literal_semantics,
    hfind]
  rfl

/-- Source semantics for a broader supported sequencing subset:
run one supported `require` guard-family clause, then execute
`return (literal retVal)` only on success. -/
def execSourceRequireFamilyThenReturnLiteral
    (family : RequireLiteralGuardFamily)
    (init : TExecState)
    (n m p q : Nat) (message : String) (retVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamily family init n m p q message with
  | .ok st => execSourceReturnLiteral st retVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled one-clause `require` guard-family semantics, then run
compiled `return (literal retVal)` on success. -/
def execCompiledRequireFamilyThenReturnLiteral
    (family : RequireLiteralGuardFamily)
    (fields : List Field) (init : TExecState)
    (n m p q : Nat) (message : String) (retVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamily family fields init n m p q message with
  | .ok st => execCompiledReturnLiteral fields st retVal
  | .revert reason => .revert reason

/-- Clause payload for list-level semantic preservation over the unified
`require` guard family. -/
structure RequireLiteralGuardFamilyClause where
  family : RequireLiteralGuardFamily
  n : Nat
  m : Nat
  p : Nat
  q : Nat
  message : String
deriving DecidableEq, Repr

/-- Source semantics dispatcher for a list of unified `require` guard-family
clauses. Evaluation short-circuits on revert. -/
def execSourceRequireLiteralGuardFamilyClauses
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match clauses with
  | [] => .ok init
  | clause :: rest =>
      match execSourceRequireLiteralGuardFamily
          clause.family init clause.n clause.m clause.p clause.q clause.message with
      | .ok st => execSourceRequireLiteralGuardFamilyClauses st rest
      | .revert reason => .revert reason

/-- Compiled semantics dispatcher for a list of unified `require` guard-family
clauses. Evaluation short-circuits on revert. -/
def execCompiledRequireLiteralGuardFamilyClauses
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  match clauses with
  | [] => .ok init
  | clause :: rest =>
      match execCompiledRequireLiteralGuardFamily
          clause.family fields init clause.n clause.m clause.p clause.q clause.message with
      | .ok st => execCompiledRequireLiteralGuardFamilyClauses fields st rest
      | .revert reason => .revert reason

/-- Structural-induction semantic-preservation theorem for sequences of unified
`require` guard-family clauses (`binary`, `andEqLt`, `orEqLt`). -/
theorem compile_require_literal_guard_family_clauses_semantics
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) :
    execCompiledRequireLiteralGuardFamilyClauses fields init clauses =
      execSourceRequireLiteralGuardFamilyClauses init clauses := by
  induction clauses generalizing init with
  | nil =>
      simp [execCompiledRequireLiteralGuardFamilyClauses, execSourceRequireLiteralGuardFamilyClauses]
  | cons clause rest ih =>
      simp [execCompiledRequireLiteralGuardFamilyClauses,
        execSourceRequireLiteralGuardFamilyClauses,
        compile_require_literal_guard_family_semantics, ih]
      rfl

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then execute
no additional statements. -/
def execSourceRequireFamilyClausesThenNoop
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  execSourceRequireLiteralGuardFamilyClauses init clauses

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then execute
no additional statements. -/
def execCompiledRequireFamilyClausesThenNoop
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) : TExecResult :=
  execCompiledRequireLiteralGuardFamilyClauses fields init clauses

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists with no continuation tail,
compiled execution matches direct source sequencing semantics. -/
theorem compile_require_family_clauses_then_noop_semantics
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) :
    execCompiledRequireFamilyClausesThenNoop fields init clauses =
      execSourceRequireFamilyClausesThenNoop init clauses := by
  simpa [execCompiledRequireFamilyClausesThenNoop, execSourceRequireFamilyClausesThenNoop]
    using compile_require_literal_guard_family_clauses_semantics fields init clauses

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`setStorage fieldName (literal writeVal)` only on success. -/
def execSourceRequireFamilyClausesThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause) (slot : Nat)
    (writeVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => .ok { st with world := execSourceSetStorageLiteral st.world slot writeVal }
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `setStorage fieldName (literal writeVal)` on success. -/
def execCompiledRequireFamilyClausesThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (writeVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledSetStorageLiteral fields fieldName st writeVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [setStorage fieldName (literal elseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqSetStorageLiterals
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m thenVal elseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        { st with
            world := execSourceIteEqSetStorageLiterals st.world slot n m thenVal elseVal }
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [setStorage fieldName (literal elseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqSetStorageLiterals
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledIteEqSetStorageLiterals fields fieldName st n m thenVal elseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [return (literal elseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m thenVal elseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqSetStorageThenReturnLiteral st slot n m thenVal elseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [setStorage fieldName (literal thenVal)]
     [return (literal elseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqSetStorageThenReturnLiteral fields fieldName st n m thenVal elseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [setStorage fieldName (literal elseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m thenVal elseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqReturnThenSetStorageLiteral st slot n m thenVal elseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [setStorage fieldName (literal elseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqReturnThenSetStorageLiteral fields fieldName st n m thenVal elseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [return (literal elseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqReturnLiterals
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqReturnLiterals st n m thenVal elseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [return (literal thenVal)]
     [return (literal elseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqReturnLiterals
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqReturnLiterals fields st n m thenVal elseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqReturnLiterals st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [return (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqReturnLiterals fields st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [return (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [return (literal thenVal)]
          [return (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` only on success. -/
def execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      execSourceIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        st slot n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`ite (eq (literal n) (literal m))
     [ite (eq (literal p) (literal q))
          [setStorage fieldName (literal thenVal)]
          [setStorage fieldName (literal elseVal)]]
     [setStorage fieldName (literal outerElseVal)]` on success. -/
def execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
    (fields : List Field) (fieldName : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st =>
      execCompiledIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName st n m p q thenVal elseVal outerElseVal
  | .revert reason => .revert reason

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by `setStorage literal`,
compiled execution matches direct source sequencing semantics under explicit
field-resolution assumptions. -/
theorem compile_require_family_clauses_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (writeVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenSetStorageLiteral
        fields fieldName init clauses writeVal =
      execSourceRequireFamilyClausesThenSetStorageLiteral
        init clauses slot writeVal := by
  simp [execCompiledRequireFamilyClausesThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_setStorage_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`ite(eq(literal,literal))` with literal-storage branches, compiled execution
matches direct source sequencing semantics under explicit field-resolution
assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_setStorage_literals_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqSetStorageLiterals
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqSetStorageLiterals
        init clauses slot n m thenVal elseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqSetStorageLiterals,
    execSourceRequireFamilyClausesThenIteEqSetStorageLiterals,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_setStorage_literals_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`ite(eq(literal,literal))` with `setStorage` true branch and `return` false
branch, compiled execution matches direct source sequencing semantics under
explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_setStorage_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        init clauses slot n m thenVal elseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral,
    execSourceRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_setStorage_then_return_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`ite(eq(literal,literal))` with `return` true branch and `setStorage` false
branch, compiled execution matches direct source sequencing semantics under
explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_return_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        fields fieldName init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        init clauses slot n m thenVal elseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_return_then_setStorage_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`ite(eq(literal,literal))` with `return` on both branches, compiled execution
matches direct source sequencing semantics. -/
theorem compile_require_family_clauses_then_ite_eq_return_literals_semantics
    (fields : List Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m thenVal elseVal : Nat) :
    execCompiledRequireFamilyClausesThenIteEqReturnLiterals
        fields init clauses n m thenVal elseVal =
      execSourceRequireFamilyClausesThenIteEqReturnLiterals
        init clauses n m thenVal elseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqReturnLiterals,
    execSourceRequireFamilyClausesThenIteEqReturnLiterals,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_return_literals_semantics]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with return-only leaves, compiled execution matches
direct source sequencing semantics. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_semantics
    (fields : List Field)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        fields init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        init clauses n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiterals,
    execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiterals,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_return_literals_semantics]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner storage branches and outer false-branch
return, compiled execution matches direct source sequencing semantics under
explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner return-only branches and outer false-
branch storage write, compiled execution matches direct source sequencing
semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics, hfind]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by nested
`ite(eq(literal,literal))` with inner storage branches and outer false-branch
storage write, compiled execution matches direct source sequencing semantics
under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics
    (fields : List Field) (fieldName : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (n m p q thenVal elseVal outerElseVal : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal =
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal := by
  simp [execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral,
    execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics, hfind]
  rfl

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`return (literal retVal)` only on success. -/
def execSourceRequireFamilyClausesThenReturnLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (retVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceReturnLiteral st retVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `return (literal retVal)` on success. -/
def execCompiledRequireFamilyClausesThenReturnLiteral
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledReturnLiteral fields st retVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal retVal); return (localVar tmp)` only on success. -/
def execSourceRequireFamilyClausesThenLetReturnLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (retVal : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st => execSourceLetReturnLocalLiteral st retVal
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `letVar tmp (literal retVal); return (localVar tmp)` on success. -/
def execCompiledRequireFamilyClausesThenLetReturnLocalLiteral
    (fields : List Field) (tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetReturnLocalLiteral fields tmp st retVal
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal n); setStorage fieldName (localVar tmp)` only on success. -/
def execSourceRequireFamilyClausesThenLetSetStorageLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        ({ st with
            world := execSourceSetStorageLiteral st.world slot n
            vars := st.vars.set { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256) })
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `letVar tmp (literal n); setStorage fieldName (localVar tmp)` on success. -/
def execCompiledRequireFamilyClausesThenLetSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetSetStorageLocalLiteral fields fieldName tmp st n
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`
only on success. -/
def execSourceRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        ({ st with
            world := execSourceSetStorageLiteral st.world slot m
            vars := TVars.set
              (TVars.set st.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 } (m : Verity.Core.Uint256) })
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`
on success. -/
def execCompiledRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetAssignSetStorageLocalLiteral fields fieldName tmp st n m
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` only on success. -/
def execSourceRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        ({ st with
            world := execSourceSetStorageLiteral st.world slot
              ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set st.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).add (m : Verity.Core.Uint256)) })
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` on success. -/
def execCompiledRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetAssignAddSetStorageLocalLiteral fields fieldName tmp st n m
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` only on success. -/
def execSourceRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        ({ st with
            world := execSourceSetStorageLiteral st.world slot
              ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set st.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).sub (m : Verity.Core.Uint256)) })
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` on success. -/
def execCompiledRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetAssignSubSetStorageLocalLiteral fields fieldName tmp st n m
  | .revert reason => .revert reason

/-- Source semantics for a broader supported sequencing subset:
run a list of supported unified `require` guard-family clauses, then perform
`letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` only on success. -/
def execSourceRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
    (init : TExecState) (clauses : List RequireLiteralGuardFamilyClause)
    (slot : Nat) (n m : Nat) : TExecResult :=
  match execSourceRequireLiteralGuardFamilyClauses init clauses with
  | .ok st =>
      .ok
        ({ st with
            world := execSourceSetStorageLiteral st.world slot
              ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256))
            vars := TVars.set
              (TVars.set st.vars { id := 0, ty := Ty.uint256 } (n : Verity.Core.Uint256))
              { id := 1, ty := Ty.uint256 }
                ((n : Verity.Core.Uint256).mul (m : Verity.Core.Uint256)) })
  | .revert reason => .revert reason

/-- Compiled semantics for the same broader supported sequencing subset:
run compiled unified `require` guard-family clause-list semantics, then run
compiled `letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)` on success. -/
def execCompiledRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
    (fields : List Field) (fieldName tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat) : TExecResult :=
  match execCompiledRequireLiteralGuardFamilyClauses fields init clauses with
  | .ok st => execCompiledLetAssignMulSetStorageLocalLiteral fields fieldName tmp st n m
  | .revert reason => .revert reason

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by `return literal`,
compiled execution matches direct source sequencing semantics. -/
theorem compile_require_family_clauses_then_return_literal_semantics
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) :
    execCompiledRequireFamilyClausesThenReturnLiteral
        fields init clauses retVal =
      execSourceRequireFamilyClausesThenReturnLiteral
        init clauses retVal := by
  simp [execCompiledRequireFamilyClausesThenReturnLiteral,
    execSourceRequireFamilyClausesThenReturnLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_return_literal_semantics]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard families followed by `return literal`,
compiled execution matches direct source sequencing semantics. -/
theorem compile_require_family_then_return_literal_semantics
    (family : RequireLiteralGuardFamily)
    (fields : List Field)
    (init : TExecState)
    (n m p q : Nat) (message : String) (retVal : Nat) :
    execCompiledRequireFamilyThenReturnLiteral
        family fields init n m p q message retVal =
      execSourceRequireFamilyThenReturnLiteral
        family init n m p q message retVal := by
  simp [execCompiledRequireFamilyThenReturnLiteral,
    execSourceRequireFamilyThenReturnLiteral,
    compile_require_literal_guard_family_semantics, compile_return_literal_semantics]
  rfl

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal retVal); return (localVar tmp)`, compiled execution
matches direct source sequencing semantics. -/
theorem compile_require_family_clauses_then_let_return_local_literal_semantics
    (fields : List Field) (tmp : String) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat) :
    execCompiledRequireFamilyClausesThenLetReturnLocalLiteral
        fields tmp init clauses retVal =
      execSourceRequireFamilyClausesThenLetReturnLocalLiteral
        init clauses retVal := by
  simp [execCompiledRequireFamilyClausesThenLetReturnLocalLiteral,
    execSourceRequireFamilyClausesThenLetReturnLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_return_local_literal_semantics]

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal n); setStorage fieldName (localVar tmp)`, compiled execution
matches direct source sequencing semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_let_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetSetStorageLocalLiteral
        fields fieldName tmp init clauses n =
      execSourceRequireFamilyClausesThenLetSetStorageLocalLiteral
        init clauses slot n := by
  simp [execCompiledRequireFamilyClausesThenLetSetStorageLocalLiteral,
    execSourceRequireFamilyClausesThenLetSetStorageLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_setStorage_local_literal_semantics, hfind]

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal n); assignVar tmp (literal m); setStorage fieldName (localVar tmp)`,
compiled execution matches direct source sequencing semantics under explicit
field-resolution assumptions. -/
theorem compile_require_family_clauses_then_let_assign_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
        init clauses slot n m := by
  simp [execCompiledRequireFamilyClausesThenLetAssignSetStorageLocalLiteral,
    execSourceRequireFamilyClausesThenLetAssignSetStorageLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_assign_setStorage_local_literal_semantics, hfind]

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal n); assignVar tmp (add (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)`, compiled execution matches direct source
sequencing semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_let_assign_add_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
        init clauses slot n m := by
  simp [execCompiledRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral,
    execSourceRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_assign_add_setStorage_local_literal_semantics, hfind]

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal n); assignVar tmp (sub (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)`, compiled execution matches direct source
sequencing semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_let_assign_sub_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
        init clauses slot n m := by
  simp [execCompiledRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral,
    execSourceRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_assign_sub_setStorage_local_literal_semantics, hfind]

/-- Sequencing semantic-preservation theorem for a broader supported subset:
for unified `require` guard-family clause lists followed by
`letVar tmp (literal n); assignVar tmp (mul (localVar tmp) (literal m));
 setStorage fieldName (localVar tmp)`, compiled execution matches direct source
sequencing semantics under explicit field-resolution assumptions. -/
theorem compile_require_family_clauses_then_let_assign_mul_setStorage_local_literal_semantics
    (fields : List Field) (fieldName tmp : String) (slot : Nat)
    (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause) (n m : Nat)
    (hfind : findFieldWithResolvedSlot fields fieldName =
      some ({ name := fieldName, ty := FieldType.uint256 }, slot)) :
    execCompiledRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
        fields fieldName tmp init clauses n m =
      execSourceRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
        init clauses slot n m := by
  simp [execCompiledRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral,
    execSourceRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral,
    compile_require_literal_guard_family_clauses_semantics,
    compile_let_assign_mul_setStorage_local_literal_semantics, hfind]

/-- Supported continuation family after a unified `require` guard-family
clause list for generic sequencing preservation in roadmap item 2.2. -/
inductive RequireFamilyClausesTail (fields : List Field) where
  | noOp
  | setStorageLiteral (fieldName : String) (slot : Nat) (writeVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqSetStorageLiterals
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqSetStorageThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqReturnThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqReturnLiterals
      (n m thenVal elseVal : Nat)
  | iteEqThenIteEqReturnLiterals
      (n m p q thenVal elseVal outerElseVal : Nat)
  | iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | returnLiteral (retVal : Nat)
  | letReturnLocalLiteral (tmp : String) (retVal : Nat)
  | letSetStorageLocalLiteral
      (fieldName tmp : String) (slot : Nat) (n : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letAssignSetStorageLocalLiteral
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letAssignAddSetStorageLocalLiteral
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letAssignSubSetStorageLocalLiteral
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | letAssignMulSetStorageLocalLiteral
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))

/-- Source semantics dispatcher for the supported continuation family after
unified `require` guard-family clause lists. -/
def execSourceRequireFamilyClausesThenTail
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (tail : RequireFamilyClausesTail fields) : TExecResult :=
  match tail with
  | .noOp =>
      execSourceRequireFamilyClausesThenNoop init clauses
  | .setStorageLiteral _ slot writeVal _ =>
      execSourceRequireFamilyClausesThenSetStorageLiteral init clauses slot writeVal
  | .iteEqSetStorageLiterals _ slot n m thenVal elseVal _ =>
      execSourceRequireFamilyClausesThenIteEqSetStorageLiterals
        init clauses slot n m thenVal elseVal
  | .iteEqSetStorageThenReturnLiteral _ slot n m thenVal elseVal _ =>
      execSourceRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        init clauses slot n m thenVal elseVal
  | .iteEqReturnThenSetStorageLiteral _ slot n m thenVal elseVal _ =>
      execSourceRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        init clauses slot n m thenVal elseVal
  | .iteEqReturnLiterals n m thenVal elseVal =>
      execSourceRequireFamilyClausesThenIteEqReturnLiterals
        init clauses n m thenVal elseVal
  | .iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      _ slot n m p q thenVal elseVal outerElseVal _ =>
      execSourceRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        init clauses slot n m p q thenVal elseVal outerElseVal
  | .returnLiteral retVal =>
      execSourceRequireFamilyClausesThenReturnLiteral init clauses retVal
  | .letReturnLocalLiteral _ retVal =>
      execSourceRequireFamilyClausesThenLetReturnLocalLiteral init clauses retVal
  | .letSetStorageLocalLiteral _ _ slot n _ =>
      execSourceRequireFamilyClausesThenLetSetStorageLocalLiteral init clauses slot n
  | .letAssignSetStorageLocalLiteral _ _ slot n m _ =>
      execSourceRequireFamilyClausesThenLetAssignSetStorageLocalLiteral init clauses slot n m
  | .letAssignAddSetStorageLocalLiteral _ _ slot n m _ =>
      execSourceRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral init clauses slot n m
  | .letAssignSubSetStorageLocalLiteral _ _ slot n m _ =>
      execSourceRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral init clauses slot n m
  | .letAssignMulSetStorageLocalLiteral _ _ slot n m _ =>
      execSourceRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral init clauses slot n m

/-- Compiled semantics dispatcher for the supported continuation family after
unified `require` guard-family clause lists. -/
def execCompiledRequireFamilyClausesThenTail
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (tail : RequireFamilyClausesTail fields) : TExecResult :=
  match tail with
  | .noOp =>
      execCompiledRequireFamilyClausesThenNoop fields init clauses
  | .setStorageLiteral fieldName _ writeVal _ =>
      execCompiledRequireFamilyClausesThenSetStorageLiteral fields fieldName init clauses writeVal
  | .iteEqSetStorageLiterals fieldName _ n m thenVal elseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqSetStorageLiterals
        fields fieldName init clauses n m thenVal elseVal
  | .iteEqSetStorageThenReturnLiteral fieldName _ n m thenVal elseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqSetStorageThenReturnLiteral
        fields fieldName init clauses n m thenVal elseVal
  | .iteEqReturnThenSetStorageLiteral fieldName _ n m thenVal elseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqReturnThenSetStorageLiteral
        fields fieldName init clauses n m thenVal elseVal
  | .iteEqReturnLiterals n m thenVal elseVal =>
      execCompiledRequireFamilyClausesThenIteEqReturnLiterals
        fields init clauses n m thenVal elseVal
  | .iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiterals
        fields init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      execCompiledRequireFamilyClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
        fields fieldName init clauses n m p q thenVal elseVal outerElseVal
  | .returnLiteral retVal =>
      execCompiledRequireFamilyClausesThenReturnLiteral fields init clauses retVal
  | .letReturnLocalLiteral tmp retVal =>
      execCompiledRequireFamilyClausesThenLetReturnLocalLiteral fields tmp init clauses retVal
  | .letSetStorageLocalLiteral fieldName tmp _ n _ =>
      execCompiledRequireFamilyClausesThenLetSetStorageLocalLiteral
        fields fieldName tmp init clauses n
  | .letAssignSetStorageLocalLiteral fieldName tmp _ n m _ =>
      execCompiledRequireFamilyClausesThenLetAssignSetStorageLocalLiteral
        fields fieldName tmp init clauses n m
  | .letAssignAddSetStorageLocalLiteral fieldName tmp _ n m _ =>
      execCompiledRequireFamilyClausesThenLetAssignAddSetStorageLocalLiteral
        fields fieldName tmp init clauses n m
  | .letAssignSubSetStorageLocalLiteral fieldName tmp _ n m _ =>
      execCompiledRequireFamilyClausesThenLetAssignSubSetStorageLocalLiteral
        fields fieldName tmp init clauses n m
  | .letAssignMulSetStorageLocalLiteral fieldName tmp _ n m _ =>
      execCompiledRequireFamilyClausesThenLetAssignMulSetStorageLocalLiteral
        fields fieldName tmp init clauses n m

/-- Generic sequencing semantic-preservation theorem over the supported tail
family after unified `require` guard-family clause lists. -/
theorem compile_require_family_clauses_then_tail_semantics
    (fields : List Field) (init : TExecState)
    (clauses : List RequireLiteralGuardFamilyClause)
    (tail : RequireFamilyClausesTail fields) :
    execCompiledRequireFamilyClausesThenTail fields init clauses tail =
      execSourceRequireFamilyClausesThenTail fields init clauses tail := by
  cases tail with
  | noOp =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_noop_semantics fields init clauses
  | setStorageLiteral fieldName slot writeVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_setStorage_literal_semantics
          fields fieldName slot init clauses writeVal hfind
  | iteEqSetStorageLiterals fieldName slot n m thenVal elseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_ite_eq_setStorage_literals_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqSetStorageThenReturnLiteral fieldName slot n m thenVal elseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_ite_eq_setStorage_then_return_literal_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqReturnThenSetStorageLiteral fieldName slot n m thenVal elseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_ite_eq_return_then_setStorage_literal_semantics
          fields fieldName slot init clauses n m thenVal elseVal hfind
  | iteEqReturnLiterals n m thenVal elseVal =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_ite_eq_return_literals_semantics
          fields init clauses n m thenVal elseVal
  | iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_semantics
          fields init clauses n m p q thenVal elseVal outerElseVal
  | iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_return_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_return_literals_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using
          compile_require_family_clauses_then_ite_eq_then_ite_eq_setStorage_literals_then_setStorage_literal_semantics
            fields fieldName slot init clauses n m p q thenVal elseVal outerElseVal hfind
  | returnLiteral retVal =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_return_literal_semantics fields init clauses retVal
  | letReturnLocalLiteral tmp retVal =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_return_local_literal_semantics
          fields tmp init clauses retVal
  | letSetStorageLocalLiteral fieldName tmp slot n hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n hfind
  | letAssignSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_assign_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignAddSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_assign_add_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignSubSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_assign_sub_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind
  | letAssignMulSetStorageLocalLiteral fieldName tmp slot n m hfind =>
      simpa [execCompiledRequireFamilyClausesThenTail, execSourceRequireFamilyClausesThenTail]
        using compile_require_family_clauses_then_let_assign_mul_setStorage_local_literal_semantics
          fields fieldName tmp slot init clauses n m hfind

/-- Program fragment in the currently supported 2.2 generic family:
one unified require-clause list followed by one supported tail. -/
structure RequireFamilyClausesTailProgram (fields : List Field) where
  clauses : List RequireLiteralGuardFamilyClause
  tail : RequireFamilyClausesTail fields

/-- Source semantics dispatcher for lists of supported 2.2 generic program
fragments. Evaluation short-circuits on revert. -/
def execSourceRequireFamilyClausesTailPrograms
    (fields : List Field) (init : TExecState)
    (programs : List (RequireFamilyClausesTailProgram fields)) : TExecResult :=
  match programs with
  | [] => .ok init
  | program :: rest =>
      match execSourceRequireFamilyClausesThenTail fields init program.clauses program.tail with
      | .ok st => execSourceRequireFamilyClausesTailPrograms fields st rest
      | .revert reason => .revert reason

/-- Compiled semantics dispatcher for lists of supported 2.2 generic program
fragments. Evaluation short-circuits on revert. -/
def execCompiledRequireFamilyClausesTailPrograms
    (fields : List Field) (init : TExecState)
    (programs : List (RequireFamilyClausesTailProgram fields)) : TExecResult :=
  match programs with
  | [] => .ok init
  | program :: rest =>
      match execCompiledRequireFamilyClausesThenTail fields init program.clauses program.tail with
      | .ok st => execCompiledRequireFamilyClausesTailPrograms fields st rest
      | .revert reason => .revert reason

/-- Structural-induction semantic-preservation theorem over lists of supported
2.2 generic fragments `(require-clause-list + tail)`. -/
theorem compile_require_family_clauses_tail_programs_semantics
    (fields : List Field) (init : TExecState)
    (programs : List (RequireFamilyClausesTailProgram fields)) :
    execCompiledRequireFamilyClausesTailPrograms fields init programs =
      execSourceRequireFamilyClausesTailPrograms fields init programs := by
  induction programs generalizing init with
  | nil =>
      simp [execCompiledRequireFamilyClausesTailPrograms, execSourceRequireFamilyClausesTailPrograms]
  | cons program rest ih =>
      simp [execCompiledRequireFamilyClausesTailPrograms,
        execSourceRequireFamilyClausesTailPrograms,
        compile_require_family_clauses_then_tail_semantics, ih]

/-- Structural append theorem for source semantics over lists of supported
2.2 generic fragments `(require-clause-list + tail)`, specialized to any
initial execution state. -/
theorem execSourceRequireFamilyClausesTailPrograms_append_from
    (fields : List Field) (init : TExecState)
    (pre post : List (RequireFamilyClausesTailProgram fields)) :
    execSourceRequireFamilyClausesTailPrograms fields init (pre ++ post) =
      match execSourceRequireFamilyClausesTailPrograms fields init pre with
      | .ok st => execSourceRequireFamilyClausesTailPrograms fields st post
      | .revert reason => .revert reason := by
  induction pre generalizing init with
  | nil =>
      simp [execSourceRequireFamilyClausesTailPrograms]
  | cons program rest ih =>
      cases hstep : execSourceRequireFamilyClausesThenTail fields init program.clauses program.tail with
      | ok st =>
          simp [execSourceRequireFamilyClausesTailPrograms, hstep, ih]
      | revert reason =>
          simp [execSourceRequireFamilyClausesTailPrograms, hstep]

/-- Structural append theorem for compiled semantics over lists of supported
2.2 generic fragments `(require-clause-list + tail)`, specialized to any
initial execution state. -/
theorem execCompiledRequireFamilyClausesTailPrograms_append_from
    (fields : List Field) (init : TExecState)
    (pre post : List (RequireFamilyClausesTailProgram fields)) :
    execCompiledRequireFamilyClausesTailPrograms fields init (pre ++ post) =
      match execCompiledRequireFamilyClausesTailPrograms fields init pre with
      | .ok st => execCompiledRequireFamilyClausesTailPrograms fields st post
      | .revert reason => .revert reason := by
  induction pre generalizing init with
  | nil =>
      simp [execCompiledRequireFamilyClausesTailPrograms]
  | cons program rest ih =>
      cases hstep : execCompiledRequireFamilyClausesThenTail fields init program.clauses program.tail with
      | ok st =>
          simp [execCompiledRequireFamilyClausesTailPrograms, hstep, ih]
      | revert reason =>
          simp [execCompiledRequireFamilyClausesTailPrograms, hstep]

/-- Generic append/composition semantic-preservation theorem over lists of
supported 2.2 fragments `(require-clause-list + tail)`. -/
theorem compile_require_family_clauses_tail_programs_append_semantics
    (fields : List Field) (init : TExecState)
    (pre post : List (RequireFamilyClausesTailProgram fields)) :
    execCompiledRequireFamilyClausesTailPrograms fields init (pre ++ post) =
      execSourceRequireFamilyClausesTailPrograms fields init (pre ++ post) := by
  calc
    execCompiledRequireFamilyClausesTailPrograms fields init (pre ++ post)
        =
          match execCompiledRequireFamilyClausesTailPrograms fields init pre with
          | .ok st => execCompiledRequireFamilyClausesTailPrograms fields st post
          | .revert reason => .revert reason := by
            simpa using
              execCompiledRequireFamilyClausesTailPrograms_append_from fields init pre post
    _ =
          match execSourceRequireFamilyClausesTailPrograms fields init pre with
          | .ok st => execSourceRequireFamilyClausesTailPrograms fields st post
          | .revert reason => .revert reason := by
            simpa [compile_require_family_clauses_tail_programs_semantics] using
              congrArg
                (fun r =>
                  match r with
                  | .ok st => execCompiledRequireFamilyClausesTailPrograms fields st post
                  | .revert reason => .revert reason)
                (compile_require_family_clauses_tail_programs_semantics fields init pre)
    _ = execSourceRequireFamilyClausesTailPrograms fields init (pre ++ post) := by
          simpa using
            (execSourceRequireFamilyClausesTailPrograms_append_from fields init pre post).symm

/-- Explicit statement-fragment grammar for the currently supported generic 2.2
subset: one require-clause-list prefix followed by one supported continuation. -/
inductive SupportedStmtFragment (fields : List Field) where
  | requireClausesOnly
      (clauses : List RequireLiteralGuardFamilyClause)
  | requireClausesThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat) (writeVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqSetStorageLiterals
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqSetStorageThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqReturnThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m thenVal elseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqReturnLiterals
      (clauses : List RequireLiteralGuardFamilyClause)
      (n m thenVal elseVal : Nat)
  | requireClausesThenIteEqThenIteEqReturnLiterals
      (clauses : List RequireLiteralGuardFamilyClause)
      (n m p q thenVal elseVal outerElseVal : Nat)
  | requireClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName : String) (slot : Nat)
      (n m p q thenVal elseVal outerElseVal : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenReturnLiteral
      (clauses : List RequireLiteralGuardFamilyClause) (retVal : Nat)
  | requireClausesThenLetReturnLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause) (tmp : String) (retVal : Nat)
  | requireClausesThenLetSetStorageLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (n : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetAssignSetStorageLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetAssignAddSetStorageLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetAssignSubSetStorageLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))
  | requireClausesThenLetAssignMulSetStorageLocalLiteral
      (clauses : List RequireLiteralGuardFamilyClause)
      (fieldName tmp : String) (slot : Nat) (n m : Nat)
      (hfind : findFieldWithResolvedSlot fields fieldName =
        some ({ name := fieldName, ty := FieldType.uint256 }, slot))

/-- Encode an explicit supported statement fragment into the generic
`(require-clause-list + tail)` program representation. -/
def SupportedStmtFragment.toRequireFamilyClausesTailProgram
    {fields : List Field} :
    SupportedStmtFragment fields → RequireFamilyClausesTailProgram fields
  | .requireClausesOnly clauses =>
      { clauses := clauses
        tail := .noOp }
  | .requireClausesThenSetStorageLiteral clauses fieldName slot writeVal hfind =>
      { clauses := clauses
        tail := .setStorageLiteral fieldName slot writeVal hfind }
  | .requireClausesThenIteEqSetStorageLiterals clauses fieldName slot n m thenVal elseVal hfind =>
      { clauses := clauses
        tail := .iteEqSetStorageLiterals fieldName slot n m thenVal elseVal hfind }
  | .requireClausesThenIteEqSetStorageThenReturnLiteral
      clauses fieldName slot n m thenVal elseVal hfind =>
      { clauses := clauses
        tail := .iteEqSetStorageThenReturnLiteral fieldName slot n m thenVal elseVal hfind }
  | .requireClausesThenIteEqReturnThenSetStorageLiteral
      clauses fieldName slot n m thenVal elseVal hfind =>
      { clauses := clauses
        tail := .iteEqReturnThenSetStorageLiteral fieldName slot n m thenVal elseVal hfind }
  | .requireClausesThenIteEqReturnLiterals clauses n m thenVal elseVal =>
      { clauses := clauses
        tail := .iteEqReturnLiterals n m thenVal elseVal }
  | .requireClausesThenIteEqThenIteEqReturnLiterals
      clauses n m p q thenVal elseVal outerElseVal =>
      { clauses := clauses
        tail := .iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal }
  | .requireClausesThenIteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenIteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      clauses fieldName slot n m p q thenVal elseVal outerElseVal hfind =>
      { clauses := clauses
        tail := .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
          fieldName slot n m p q thenVal elseVal outerElseVal hfind }
  | .requireClausesThenReturnLiteral clauses retVal =>
      { clauses := clauses
        tail := .returnLiteral retVal }
  | .requireClausesThenLetReturnLocalLiteral clauses tmp retVal =>
      { clauses := clauses
        tail := .letReturnLocalLiteral tmp retVal }
  | .requireClausesThenLetSetStorageLocalLiteral clauses fieldName tmp slot n hfind =>
      { clauses := clauses
        tail := .letSetStorageLocalLiteral fieldName tmp slot n hfind }
  | .requireClausesThenLetAssignSetStorageLocalLiteral clauses fieldName tmp slot n m hfind =>
      { clauses := clauses
        tail := .letAssignSetStorageLocalLiteral fieldName tmp slot n m hfind }
  | .requireClausesThenLetAssignAddSetStorageLocalLiteral clauses fieldName tmp slot n m hfind =>
      { clauses := clauses
        tail := .letAssignAddSetStorageLocalLiteral fieldName tmp slot n m hfind }
  | .requireClausesThenLetAssignSubSetStorageLocalLiteral clauses fieldName tmp slot n m hfind =>
      { clauses := clauses
        tail := .letAssignSubSetStorageLocalLiteral fieldName tmp slot n m hfind }
  | .requireClausesThenLetAssignMulSetStorageLocalLiteral clauses fieldName tmp slot n m hfind =>
      { clauses := clauses
        tail := .letAssignMulSetStorageLocalLiteral fieldName tmp slot n m hfind }

/-- Encode one unified `require` guard-family clause into a source `Stmt.require`. -/
def RequireLiteralGuardFamilyClause.toStmt (clause : RequireLiteralGuardFamilyClause) : Stmt :=
  let guardExpr :=
    match clause.family with
    | .binary .eq =>
        Expr.eq (Expr.literal clause.n) (Expr.literal clause.m)
    | .binary .notEq =>
        Expr.logicalNot (Expr.eq (Expr.literal clause.n) (Expr.literal clause.m))
    | .binary .lt =>
        Expr.lt (Expr.literal clause.n) (Expr.literal clause.m)
    | .binary .gt =>
        Expr.gt (Expr.literal clause.n) (Expr.literal clause.m)
    | .binary .ge =>
        Expr.ge (Expr.literal clause.n) (Expr.literal clause.m)
    | .binary .le =>
        Expr.le (Expr.literal clause.n) (Expr.literal clause.m)
    | .andEqLt =>
        Expr.logicalAnd
          (Expr.eq (Expr.literal clause.n) (Expr.literal clause.m))
          (Expr.lt (Expr.literal clause.p) (Expr.literal clause.q))
    | .orEqLt =>
        Expr.logicalOr
          (Expr.eq (Expr.literal clause.n) (Expr.literal clause.m))
          (Expr.lt (Expr.literal clause.p) (Expr.literal clause.q))
  Stmt.require guardExpr clause.message

/-- Encode one supported continuation tail into a source statement list. -/
def RequireFamilyClausesTail.toStmts
    {fields : List Field} (tail : RequireFamilyClausesTail fields) : List Stmt :=
  match tail with
  | .noOp =>
      []
  | .setStorageLiteral fieldName _ writeVal _ =>
      [Stmt.setStorage fieldName (Expr.literal writeVal)]
  | .iteEqSetStorageLiterals fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
  | .iteEqSetStorageThenReturnLiteral fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.setStorage fieldName (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
  | .iteEqReturnThenSetStorageLiteral fieldName _ n m thenVal elseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.setStorage fieldName (Expr.literal elseVal)]]
  | .iteEqReturnLiterals n m thenVal elseVal =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.return (Expr.literal thenVal)]
          [Stmt.return (Expr.literal elseVal)]]
  | .iteEqThenIteEqReturnLiterals n m p q thenVal elseVal outerElseVal =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageLiteralsThenReturnLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.return (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqReturnLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.return (Expr.literal thenVal)]
            [Stmt.return (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .iteEqThenIteEqSetStorageLiteralsThenSetStorageLiteral
      fieldName _ n m p q thenVal elseVal outerElseVal _ =>
      [Stmt.ite (Expr.eq (Expr.literal n) (Expr.literal m))
          [Stmt.ite (Expr.eq (Expr.literal p) (Expr.literal q))
            [Stmt.setStorage fieldName (Expr.literal thenVal)]
            [Stmt.setStorage fieldName (Expr.literal elseVal)]]
          [Stmt.setStorage fieldName (Expr.literal outerElseVal)]]
  | .returnLiteral retVal =>
      [Stmt.return (Expr.literal retVal)]
  | .letReturnLocalLiteral tmp retVal =>
      [Stmt.letVar tmp (Expr.literal retVal), Stmt.return (Expr.localVar tmp)]
  | .letSetStorageLocalLiteral fieldName tmp _ n _ =>
      [Stmt.letVar tmp (Expr.literal n), Stmt.setStorage fieldName (Expr.localVar tmp)]
  | .letAssignSetStorageLocalLiteral fieldName tmp _ n m _ =>
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.literal m)
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]
  | .letAssignAddSetStorageLocalLiteral fieldName tmp _ n m _ =>
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.add (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]
  | .letAssignSubSetStorageLocalLiteral fieldName tmp _ n m _ =>
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.sub (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]
  | .letAssignMulSetStorageLocalLiteral fieldName tmp _ n m _ =>
      [ Stmt.letVar tmp (Expr.literal n)
      , Stmt.assignVar tmp (Expr.mul (Expr.localVar tmp) (Expr.literal m))
      , Stmt.setStorage fieldName (Expr.localVar tmp)
      ]

/-- Encode one supported `(require-clause-list + tail)` program into raw source
statement lists. -/
def RequireFamilyClausesTailProgram.toStmts
    {fields : List Field} (program : RequireFamilyClausesTailProgram fields) : List Stmt :=
  program.clauses.map RequireLiteralGuardFamilyClause.toStmt ++
    program.tail.toStmts

/-- Encode one explicit supported fragment into raw source statement lists. -/
def SupportedStmtFragment.toStmts
    {fields : List Field} (fragment : SupportedStmtFragment fields) : List Stmt :=
  (fragment.toRequireFamilyClausesTailProgram).toStmts

/-- Raw statement-list projection of explicit supported fragments. -/
def supportedStmtFragmentsToStmts
    {fields : List Field} (fragments : List (SupportedStmtFragment fields)) : List Stmt :=
  (fragments.map SupportedStmtFragment.toStmts).foldr (· ++ ·) []

/-- Raw `List Stmt` membership in the declared supported fragment grammar. -/
def SupportedStmtList (fields : List Field) (stmts : List Stmt) : Prop :=
  ∃ fragments : List (SupportedStmtFragment fields),
    supportedStmtFragmentsToStmts fragments = stmts

/-- Source semantics for lists of explicit supported statement fragments. -/
def execSourceSupportedStmtFragments
    (fields : List Field) (init : TExecState)
    (fragments : List (SupportedStmtFragment fields)) : TExecResult :=
  execSourceRequireFamilyClausesTailPrograms fields init
    (fragments.map SupportedStmtFragment.toRequireFamilyClausesTailProgram)

/-- Compiled semantics for lists of explicit supported statement fragments. -/
def execCompiledSupportedStmtFragments
    (fields : List Field) (init : TExecState)
    (fragments : List (SupportedStmtFragment fields)) : TExecResult :=
  execCompiledRequireFamilyClausesTailPrograms fields init
    (fragments.map SupportedStmtFragment.toRequireFamilyClausesTailProgram)

/-- One generic list-level semantic-preservation theorem over the explicit
supported statement-fragment grammar for roadmap item 2.2. -/
theorem compile_supported_stmt_fragments_semantics
    (fields : List Field) (init : TExecState)
    (fragments : List (SupportedStmtFragment fields)) :
    execCompiledSupportedStmtFragments fields init fragments =
      execSourceSupportedStmtFragments fields init fragments := by
  simpa [execCompiledSupportedStmtFragments, execSourceSupportedStmtFragments]
    using compile_require_family_clauses_tail_programs_semantics fields init
      (fragments.map SupportedStmtFragment.toRequireFamilyClausesTailProgram)

/-- Raw-statement-list semantic-preservation theorem for arbitrary lists in the
declared supported statement fragment (witnessed by `SupportedStmtList`). -/
theorem compile_supported_stmt_list_semantics
    (fields : List Field) (init : TExecState) (stmts : List Stmt)
    (hSupported : SupportedStmtList fields stmts) :
    ∃ fragments : List (SupportedStmtFragment fields),
      supportedStmtFragmentsToStmts fragments = stmts ∧
      execCompiledSupportedStmtFragments fields init fragments =
        execSourceSupportedStmtFragments fields init fragments := by
  rcases hSupported with ⟨fragments, hfragments⟩
  refine ⟨fragments, hfragments, ?_⟩
  exact compile_supported_stmt_fragments_semantics fields init fragments

/-- Compiled semantics for arbitrary raw statement lists in the declared
supported fragment, selected via the provided fragment-membership witness. -/
noncomputable def execCompiledSupportedStmtList
    (fields : List Field) (init : TExecState)
    (stmts : List Stmt) (hSupported : SupportedStmtList fields stmts) : TExecResult :=
  execCompiledSupportedStmtFragments fields init (Classical.choose hSupported)

/-- Source semantics for arbitrary raw statement lists in the declared
supported fragment, selected via the provided fragment-membership witness. -/
noncomputable def execSourceSupportedStmtList
    (fields : List Field) (init : TExecState)
    (stmts : List Stmt) (hSupported : SupportedStmtList fields stmts) : TExecResult :=
  execSourceSupportedStmtFragments fields init (Classical.choose hSupported)

/-- Direct raw-list semantic-preservation theorem for arbitrary supported
statement lists (no existential decomposition in the conclusion). -/
theorem compile_supported_stmt_list_direct_semantics
    (fields : List Field) (init : TExecState) (stmts : List Stmt)
    (hSupported : SupportedStmtList fields stmts) :
    execCompiledSupportedStmtList fields init stmts hSupported =
      execSourceSupportedStmtList fields init stmts hSupported := by
  simp [execCompiledSupportedStmtList, execSourceSupportedStmtList,
    compile_supported_stmt_fragments_semantics]

end Verity.Core.Free
